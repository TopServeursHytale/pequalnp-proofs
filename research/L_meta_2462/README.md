# Research for L-meta-2462

This branch preserves mathematical supporting work for the live assigned task. It is not an upstream proof submission.

`MultiOutput2462.lean` contains a complete proof of the second proposition of the proposed reduction. It compiled with Lean4.36.0 and the project's pinned Mathlib. The complete project checker has not been run on this standalone helper yet.

`argument.txt` records the constructive mathematical argument and the remaining extraction step. The exact reduction R_meta_2462_724 was accepted by the complete project checker in [validation run45366669908](https://github.com/TopServeursHytale/pequalnp-proofs/actions/runs/45366669908).

The source graph-counting invariant develops the demand-set idea already present in the upstream proof of L-meta-550. The proof here was formalized for the multi-output incidence setting.
