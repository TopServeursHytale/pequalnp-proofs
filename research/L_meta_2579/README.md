# Supporting lemmas for L-meta-2579

The three lemmas in AlmostPureSide.lean compiled with Lean4.36.0 and the project's pinned Mathlib at upstream commit f5e4aa53752fb1bba2aa6a121ec5226158b84f50. They concern neighborhoods and common neighbors in graphs with no cycle of length four, and support the leaf–junk branch of the proposed structural reduction.

They establish an almost pure side from a cross-pair condition, count centers using selected common neighbors, and bound by two the centers adjacent to a fixed vertex with at most one exception in a set of size at least three.

This branch preserves research, not an upstream task submission. These auxiliary files have only the local Lean compilation result; the complete project checker has not been run on them as standalone submissions. The main reduction is validated separately and sent as one exact Lean file.
