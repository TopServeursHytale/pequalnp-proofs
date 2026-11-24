# A verified lifting lemma for L-meta-2658

[PairClean.lean](PairClean.lean) proves `Research2658.pair_clean_suffices_getD`, the exact first proposed child `h1` of [upstream PR #5758](https://github.com/brilliant-hq/pequalnp-proofs/pull/5758), at PR head `f8fe2d78eb7031ad00f660e0548f5360c1e3e547`.

This is a complete Lean proof of that implication. **L-meta-2658 itself remains unresolved by this contribution**: the existence of a no-larger circuit with the required pair behavior is still needed. This research artifact is available for reuse by the existing reduction's author; it does not propose another reduction or claim an accepted desk submission.

## Statement

Let `n > 0`, let `G` be any simple graph on `Fin n`, and let `C` be a monotone circuit with gate fan-in at most two. Suppose every AND gate is false on `pairInput u v` whenever `G.Adj u v` is false, including diagonal pairs `u = v`.

Then whenever any AND gate is true on an arbitrary input `x`, there are adjacent vertices `u, v` for which both `x u` and `x v` are true.

The theorem uses the project's actual `C.wires ... |>.getD ... false` semantics and the same gate lookup interface as `h1`. It requires neither a C4-free graph nor a hypothesis that the circuit computes the graph's edge function. It adds no backwards-wiring assumption. Empty, unary, and binary gates and missing or future wire references are handled by the proof.

## Proof idea

Fix an input whose true vertices form an independent set. Induct on wire index. Every wire true on this input has a true input vertex that dominates it: making that one vertex true already forces the wire true, regardless of other input bits. Input wires supply their own witness, and OR gates inherit a witness from a true operand.

An AND gate cannot be true. With two operands, their dominating vertices would force the AND gate true on their pair input. Those vertices lie in the independent set, contradicting the pair hypothesis. A unary AND uses a diagonal pair. A zero-input AND is true on every pair, and `n > 0` supplies a diagonal pair for the same contradiction. Unavailable operands evaluate false, so they cannot be true operands in these cases.

Consequently every AND gate is false on every independent-set input, which is exactly the desired implication.

## Validation

The file imports only `Mathlib` and `PEqualNP.Defs`. Direct compilation with the project's pinned Lean toolchain succeeded on 2026-11-24 with exit code 0 and no diagnostics. The validation checkout was `f5e4aa53752fb1bba2aa6a121ec5226158b84f50`, using `leanprover/lean4:v4.36.0`.

To compile in a prepared project checkout with this research directory at its root:

```sh
cd lean
lake env lean ../research/L_meta_2658/PairClean.lean
```

An independent axiom audit of the final theorem also exited successfully:

```text
'Research2658.pair_clean_suffices_getD' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry`, added axiom, or native-decision proof is used. The full project submission checker has **not** been run for this standalone research lemma, and no official acceptance is asserted.

The source SHA-256 and machine-readable validation record are in [VALIDATION.json](VALIDATION.json).

## Remaining work

To finish L-meta-2658 through PR #5758's proposed cut, one must still construct a circuit of no greater size whose AND gates reject every nonedge pair. The proved lifting implication then gives soundness on arbitrary inputs. This file establishes the lifting implication only.
