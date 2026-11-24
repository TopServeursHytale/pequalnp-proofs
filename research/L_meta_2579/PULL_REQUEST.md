Every residual edge in L-meta-2579 has a witness at a top AND gate of one of two kinds. This reduction separates their uniform cardinality bounds:

- **Leaf–junk:** one side OR-reaches an endpoint of the edge; the other OR-reaches a junk AND gate accepting the edge input.
- **Junk–junk:** the two sides OR-reach two distinct junk AND gates, both accepting the edge input.

Both children retain the exact residual filter and the graph, minimality, and top-form hypotheses of the assigned statement. The coverage proof gives a union, so the families may overlap; the final constant is the sum of their two constants.

The coverage argument adapts RobertCass's checked L-meta-1766 ([PR #4025](https://github.com/brilliant-hq/pequalnp-proofs/pull/4025), commit `648ed26b7255fc04a9a30f8380bb501f83e96f89`). Its auxiliary definitions and proofs are local to the single theorem. The only imports are Mathlib and PEqualNP.Defs.

The two new cardinality bounds remain open obligations. This contribution proves their structural reduction to the exact assigned conclusion.

### Validation

The complete project checker accepted these exact bytes as a reduction (`ACCEPTED (reduce)`, exit 0, two children) in [run 45373414763](https://github.com/TopServeursHytale/pequalnp-proofs/actions/runs/45373414763), against upstream commit `c3fc3e9c1b3923953d412d567fbd280cab8e282a`, with the project's pinned Lean and Mathlib environment.

- Source SHA256: `2f990d33804964052297511f959cf1167b726b452d7f9ca1d00ff18773ee8c6a`.
- Exact assigned statement SHA256: `d0c8a189ac4ee17a8155a0aaf935f2ab0f3875e45052134e7415e5813a1f0548`.
- This PR adds exactly one Lean file and one commit.

The project's authoritative verdict is still pending.
