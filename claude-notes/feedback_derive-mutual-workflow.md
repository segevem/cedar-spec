---
name: derive-mutual-workflow
description: How to verify derive_mutual output — check widget for schedule quality, test generators/checkers/enumerators for performance
metadata:
  type: feedback
---

After running `derive_mutual`, check the output in two ways:

1. **Widget output** — The derive_mutual infoview widget shows schedule quality info (scores, constructor stats, dependency graph, SCC decomposition). Use this to diagnose why a generator might be slow (e.g., high backtracking score, unconstrained variables, many checks).

2. **Runtime testing** — Actually run the derived generators/checkers/enumerators (e.g. via `#eval Gen.run (ArbitrarySizedSuchThat.arbitrarySizedST ...)`) to confirm they aren't slow. The widget diagnostics explain *why* something is slow; runtime confirms *whether* it is.

**Why:** Derived generators can have poor schedule quality (too much backtracking, unconstrained sampling) that only shows up at runtime. The widget is the primary diagnostic tool for understanding schedule decisions.

**How to apply:** After every `derive_mutual` invocation, inspect both the widget output and sample from the derived instance to verify acceptable performance before moving on.
