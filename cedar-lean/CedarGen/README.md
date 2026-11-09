# Specimen-derived generators for Cedar

The schema, expression and policy generators that Specimen derives from the relational
specification of Cedar's typechecker (`Cedar/Validation/Relational`), against Basalt, and their
proofs.

- `Relational/SchemaGen*.lean`: the schema generator, from the generator-shaped `GenTypeEnvB` /
  `GenTypeEnvF`, and how they relate to the well-formed type environments.
- `Relational/ExprGen.lean`, `Relational/PolicyGen.lean`: the expression and policy generators,
  from `HasType` and the policy relations.
- `Relational/Sound`, `Relational/Depth`: the paper's claims about the derived generators: what the
  schemas, requests and policies they produce are like (`Sound`), and a bound on the depth of the
  expressions (`Depth`).
- `../CedarGenProof`: the soundness and completeness of every derived expression generator,
  enumerator and checker, its components' proofs split over files. Each file checks that the laws
  it proves depend only on `propext`, `Classical.choice` and `Quot.sound`, and fails otherwise.

Specimen (`segevem/specimen`) and Basalt (`hgoldstein95/basalt`) are pinned at their
`pldi-artifact` commits in `../lakefile.lean`.

## Building

From `cedar-lean`:

```bash
lake exe cache get        # Mathlib's build, rather than compiling it
lake build Cedar
lake build CedarGen CedarGenProof CedarGenProofSlices
lake build $(find CedarGen/Relational/Sound CedarGen/Relational/Depth -name '*.lean' \
  | sed 's|\.lean$||; s|/|.|g')
```

On a 32-core machine, from a fresh clone, these take about 100 s, 5 minutes and 1 minute. The
last lines of the `CedarGenProof` build report the laws checked (1284) and how many depend on a
nonstandard axiom (0).

Optionally, `./build_native_libs.sh` compiles Specimen's and Basalt's libraries (and their
dependencies'), which `lakefile.lean` then loads, so that the derivations and proofs run their
tactics compiled rather than interpreted: faster, with the same results.
