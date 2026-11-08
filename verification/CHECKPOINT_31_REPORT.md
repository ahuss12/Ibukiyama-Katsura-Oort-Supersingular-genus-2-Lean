# Checkpoint 31 — actual graph quotient degrees and divisibility

**Block 1 is not complete. Every zero-dV surface having an elliptic map is still unproved.**

Ten new public theorems in three modules have passed normal Lean compilation and
the transitive axiom audit. They establish:

- Equal half-degrees for the actual factors of multiplication, and degree
  `(ell^n)^g` for the residual maps in a prescribed half-rank quotient family.
- Divisibility of a bilinear pairing by `ell^n` on `U + ell^n T` when it vanishes
  on `U`, including on the actual quotient Tate images.
- A degree-controlled family whose members inherit zero actual dV, using the
  previously proved prime-to-characteristic preservation theorem.
- The actual integral rational-graph intersection has a complement and the
  required rank. These are derived, not supplied as additional assumptions.
- Rational isotropy gives integral isotropy for the unchanged original pairing.
- Actual graph quotient families with the exact degree and zero dV.

For two g-dimensional varieties, the graph construction concerns their
2g-dimensional product, so the residual degree is `(ell^n)^(g+g)`. The final
graph-family theorem assumes an actual rational Tate isomorphism and zero dV
on the product. It does not assert finitely many isomorphism classes.

## Verification

`lake build SupersingularCurves.Geometry.ScalarFrobeniusTateGraphQuotients`
and `lake env lean verification/Checkpoint31Audit.lean` passed. All ten named
theorems and all 12 stored declaration entries in the three new modules were
audited, including generated declarations, stored types/bodies and transitive
dependencies. The only allowed axioms are `propext`, `Classical.choice`, and
`Quot.sound`. Source-integrity and admission scans are separate recorded checks.
The full aggregate and historical examples were not rerun.

All 332 previous project proof modules and all 4,667 vendor Lean files (including
the vendor lakefile) remain byte-identical. The checked project has 335 proof
modules and 1,850 public theorem declarations. These are inventories, not a
percentage of the mathematical goal completed.

## Unchecked work and the remaining gap

Five additional root/numerical/descent/moduli modules, containing 22 public
theorem drafts, are preserved under `drafts/checkpoint31/`. They have **not** passed
Lean and are excluded from the project import tree and proved inventory.
The initial broader build was blocked by more than 1,500 missing compiled
dependencies in the restored partial cache. A combined-source experiment was
abandoned because the upstream files rely on separate module environments.
No successful proof result is claimed for that experiment.

The remaining route requires checked numerical bounds for the actual quotient
roots, a uniform very-ampleness theorem for the nonprincipal polarizations,
and the finite-field descent/moduli assembly proving `HasFiniteModels` for a
suitable graph family. The available theorem with `KernelTrivial` cannot be
applied merely from a finite polarization kernel. The unconditional elliptic
map and product isogeny therefore remain open. Oort integral splitting is a
further requirement for the superspecial product isomorphism. Both positive
geometric Cartier converses, Block 1, and the full IKO/Newton project remain
unfinished.

Reproduce the checked additions with `bash verification/verify_checkpoint31.sh`.
The compiler and external package revisions remain pinned. The separate build
cache is partial; use the matching Mathlib cache as documented in the environment
restoration note. Do not count the drafts as completed work.
