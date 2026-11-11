# Measuring the paper's numbers

Each number the paper reports about the Cedar case study, and how to measure it, from `cedar-lean`,
after the build in `CedarGen/README.md` (`./build_native_libs.sh` included: the times are with
Specimen's and Basalt's tactics compiled).

| Number | Command |
|---|---|
| Inductive relations in the relational specification | `python3 paper/count_relations.py` |
| Derived definitions, lines of derived code and mutually recursive groups, by sort (the table) | `paper/derived_table.sh` |
| Laws proved, and that none depends on an axiom but the standard three | the last lines of `lake env lake -R build CedarGenProof` (`#specimen_audit`) |
| Time of the expression derivation and its proofs | `paper/proof_time.sh` |
| Derivation time, Basalt against Plausible emission; generator speed with SplitMix and with Plausible | `paper/gen_speed.sh` |
| Claims about the schemas, requests and policies the generators produce, and the depth bound | `CedarGen/Relational/Claims.lean` (from the theorems in `CedarGen/Relational/Sound` and `CedarGen/Relational/Depth`), checked by building it |

`paper/derived_table.sh` rebuilds the generators' modules with Specimen pretty-printing every derived
definition into a directory, so it is slower than the plain build. The times depend on the machine:
the paper's were measured on 32 cores.
