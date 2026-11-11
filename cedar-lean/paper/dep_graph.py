#!/usr/bin/env python3
"""The dependency graph of the derived generators, enumerators and checkers (the table's 291
definitions), as a figure: one node per mutually recursive group, edges for calls between groups.

Reads the dump that `paper/derived_table.sh` writes (`components.jsonl` and one `.lean` file per
derived definition). A call is either by name or through an instance (`BacktrackGenFor.gen`,
`EnumFor.enum`, `CheckerSearch.search`, `DecOpt.decOpt`), resolved to the derived definition for that
relation and those output positions.

  paper/derived_table.sh /tmp/cedar-dump                  # the dump, from cedar-lean
  python3 paper/dep_graph.py /tmp/cedar-dump dep_graph   # writes dep_graph.{dot,pdf,png}; needs Graphviz
"""
import json, os, re, subprocess, sys
from collections import defaultdict

AREAS = {"CedarGen.Relational.ExprGen": "Expressions", "CedarGen.Relational.PolicyGen": "Policies",
         "CedarGen.Relational.SchemaGen": "Schemas"}
KIND = {"gen": "Generator", "enum": "Enumerator", "check": "Checker"}
NAME = re.compile(r"^specimen_(gen|enum|check)_(.*?)((?:_\d+)*)__(.*)$")
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")


def load(d):
    nodes, seen = {}, set()
    for line in open(f"{d}/components.jsonl"):
        c = json.loads(line)
        if c["module"] not in AREAS:
            continue
        for m in c["members"]:
            if (c["module"], m["name"]) in seen:
                continue
            seen.add((c["module"], m["name"]))
            kind, rel, pos, suffix = NAME.match(m["name"]).groups()
            nodes[m["name"]] = dict(area=AREAS[c["module"]], kind=kind, rel=rel, pos=pos, suffix=suffix,
                                    lines=m["defLines"], code=open(f"{d}/{m['name']}.lean").read())
    return nodes


def group(s, i):
    """The balanced parenthesized group starting at s[i] == '(' (without the outer parens), and its end."""
    depth, j = 0, i
    while True:
        if s[j] in "([{":
            depth += 1
        elif s[j] in ")]}":
            depth -= 1
            if depth == 0:
                return s[i + 1:j], j + 1
        j += 1


def args(s):
    """The top-level whitespace-separated terms of `s`."""
    out, i = [], 0
    while i < len(s):
        if s[i].isspace():
            i += 1
        elif s[i] in "([{":
            g, j = group(s, i)
            out.append(s[i:j]); i = j
        else:
            j = i
            while j < len(s) and not s[j].isspace() and s[j] not in "([{":
                j += 1
            out.append(s[i:j]); i = j
    return out


def relation_call(body):
    """`@Rel a b c` (possibly after `match … with | pattern =>`) → (Rel, [a, b, c], pattern names)."""
    pat = set()
    m = re.match(r"\s*match .*? with\s*\|\s*(.*?)=>", body, re.S)
    if m:
        pat = set(IDENT.findall(m.group(1)))
        body = body[m.end():]
    a = args(body.strip())
    if not a or not a[0].startswith("@"):
        return None
    return a[0][1:], a[1:], pat


def calls(code):
    """(kind, relation, positions) of every call through an instance."""
    out = []
    for marker, kind in [("@BacktrackGenFor.gen _", "gen"), ("@EnumFor.enum _", "enum"),
                         ("@Specimen.CheckerSearch.search _", "enum")]:
        for m in re.finditer(re.escape(marker), code):
            i = m.end()
            while code[i].isspace():
                i += 1
            if code[i] != "(":
                continue
            lam, _ = group(code, i)
            fm = re.match(r"\s*fun\s+(.*?)=>(.*)$", lam, re.S)
            if not fm:
                continue
            binders = fm.group(1)
            names = set(re.findall(r"\(\s*([A-Za-z_][\w']*)\s*:", binders)) or set(IDENT.findall(binders))
            rc = relation_call(fm.group(2))
            if rc:
                rel, a, pat = rc
                bound = names | pat
                out.append((kind, rel, tuple(i for i, x in enumerate(a) if x in bound)))
    for marker in ["@DecOpt.decOpt", "DecOpt.negOpt"]:
        for m in re.finditer(re.escape(marker) + r"\s*\(", code):
            g, _ = group(code, m.end() - 1)
            a = args(g.strip())
            if a and a[0].startswith("@"):
                out.append(("check", a[0][1:], ()))
    return out


def edges(nodes):
    by_key = defaultdict(list)
    for n, v in nodes.items():
        by_key[(v["kind"], v["rel"], v["pos"])].append(n)
    names = set(nodes)
    E = defaultdict(set)
    for n, v in nodes.items():
        for ident in set(re.findall(r"specimen_[A-Za-z0-9_]+", v["code"])):
            if ident in names and ident != n:
                E[n].add(ident)
        for kind, rel, pos in calls(v["code"]):
            key = (kind, rel.replace(".", "_"), "".join(f"_{p}" for p in pos))
            cands = by_key.get(key, [])
            same = [c for c in cands if nodes[c]["suffix"] == v["suffix"]]
            for c in (same or cands[:1]):
                if c != n:
                    E[n].add(c)
    return E


def sccs(nodes, E):
    index, low, stack, on, out, counter = {}, {}, [], set(), [], [0]
    sys.setrecursionlimit(10000)
    def visit(v):
        index[v] = low[v] = counter[0]; counter[0] += 1
        stack.append(v); on.add(v)
        for w in sorted(E[v]):
            if w not in index:
                visit(w); low[v] = min(low[v], low[w])
            elif w in on:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            comp = []
            while True:
                w = stack.pop(); on.discard(w); comp.append(w)
                if w == v:
                    break
            out.append(comp)
    for v in sorted(nodes):
        if v not in index:
            visit(v)
    return out


# --- the figure ---------------------------------------------------------------------------------

COLOR = {"gen": "#2a78d6", "enum": "#eb6834", "check": "#1baf7a"}   # categorical slots 1-3
SHAPE = {"gen": "circle", "enum": "square", "check": "diamond"}
INK, MUTED, EDGE = "#0b0b0b", "#52514e", "#c9c8c3"


def rel_label(rel):
    return re.sub(r"^Cedar_Validation_Relational_(?:SchemaGen_|PolicyGen_|Schema_)?", "", rel)


def to_dot(g, rankdir="LR", label_min=7, size="5.3,7.8", font=1.55):
    """The condensation, one node per group, callers left of callees, fitted to a page (`size`, inches);
    `font` enlarges the text to make up for the fitting."""
    comps, nodes = g["comps"], g["nodes"]
    cid = {n: i for i, c in enumerate(comps) for n in c}
    CE = sorted({(cid[a], cid[b]) for a, bs in g["edges"].items() for b in bs if cid[a] != cid[b]})
    indeg = defaultdict(int)
    for _, b in CE:
        indeg[b] += 1
    loc = [sum(nodes[n]["lines"] for n in c) for c in comps]
    top = max(loc)
    lines = [f'digraph G {{ rankdir={rankdir}; size="{size}"; nodesep=0.025; ranksep=0.28; newrank=true; bgcolor="white";',
             f'  fontname="Helvetica"; fontsize={8 * font:.1f}; fontcolor="{INK}"; labelloc=b; labeljust=c;',
             f'  node [style=filled, label="", fixedsize=true, penwidth=0.4, color="{INK}", fontname="Helvetica"];',
             f'  edge [color="{EDGE}", arrowhead=none, penwidth=0.3];']
    for area in ["Schemas", "Policies", "Expressions"]:
        lines.append(f'  subgraph "cluster_{area}" {{ label="{area}"; labelloc=t; fontsize={9 * font:.1f}; '
                     f'color="{EDGE}"; style=rounded; penwidth=0.6; margin=4;')
        for i, c in enumerate(comps):
            if nodes[c[0]]["area"] != area:
                continue
            kinds = {nodes[n]["kind"] for n in c}
            kind = "gen" if "gen" in kinds else ("enum" if "enum" in kinds else "check")
            w = 0.045 + 0.26 * (loc[i] / top) ** 0.5
            if kind == "check":
                w *= 1.25
            attrs = [f"shape={SHAPE[kind]}", f"width={w:.3f}", f"height={w:.3f}", f'fillcolor="{COLOR[kind]}"']
            if len(c) > 1:
                attrs.append("penwidth=1.3")
            entry = indeg[i] == 0 and kind == "gen"
            if len(c) >= label_min or entry:
                count = {}
                for n in c:
                    r = rel_label(nodes[n]["rel"]); count[r] = count.get(r, 0) + 1
                lab = max(count, key=lambda r: (count[r], -len(r)))
                lab += f" (×{len(c)})" if len(c) > 1 else ""
                attrs += [f'xlabel="{lab}"', f"fontsize={6.5 * font:.1f}", f'fontcolor="{INK}"']
            lines.append(f"    c{i} [{', '.join(attrs)}];")
        lines.append("  }")
    for a, b in CE:
        lines.append(f"  c{a} -> c{b};")
    legend = " &nbsp; ".join(f'<font color="{COLOR[k]}">{g_}</font> {name}' for k, g_, name in
                             [("gen", "●", "generator"), ("enum", "■", "enumerator"), ("check", "◆", "checker")])
    lines.append(f'  label=<{legend}<br/>bold outline: mutually recursive group &nbsp; · &nbsp; '
                 f'area: lines of code &nbsp; · &nbsp; callers left of callees>;')
    lines.append("}")
    return "\n".join(lines)


def render(dotsrc, out, engine="dot"):
    open(out + ".dot", "w").write(dotsrc)
    for fmt in ["pdf", "png"]:
        extra = ["-Gdpi=250"] if fmt == "png" else []
        subprocess.run([engine, f"-T{fmt}", *extra, out + ".dot", "-o", f"{out}.{fmt}"], check=True)


if __name__ == "__main__":
    d, out = sys.argv[1], sys.argv[2]
    nodes = load(d)
    E = edges(nodes)
    comps = sccs(nodes, E)
    big = [c for c in comps if len(c) > 1]
    # The table's counts, as a check: 291 definitions, 227 groups, 20 of them mutually recursive.
    print(f"{len(nodes)} definitions, {sum(len(v) for v in E.values())} calls, {len(comps)} groups, "
          f"{len(big)} with more than one member, largest {max(map(len, comps))}")
    g = {"comps": comps, "edges": {k: sorted(v) for k, v in E.items()},
         "nodes": {k: {x: y for x, y in v.items() if x != "code"} for k, v in nodes.items()}}
    render(to_dot(g), out)
    print(f"wrote {out}.dot, {out}.pdf, {out}.png")

