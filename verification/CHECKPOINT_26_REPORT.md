# Checkpoint 26 — actual subgroup order and abelian quotient

**The actual order-p subgroup and quotient constructions are now proved in Lean. Full Block 1 remains incomplete: both requested elliptic-product converses still require a product-decomposition theorem.**

For a represented separable quintic or sextic over an algebraically closed field of odd characteristic, let A be any representing Jacobian and H = ker(F on A^(p)) ∩ ker(V_A). If Cartier is nonzero and square zero, the new development constructs an actual abelian surface Q and actual degree-p group isogenies

A^(p) → Q → A, and Q → A^(p²).

The first composite is V_A; composing A^(p) → Q with the second residual factor gives F_(A^(p)). All maps are finite, flat and surjective, their degrees are proved, and the quotient kernel is exactly the actual subgroup H. The quotient retains p-rank zero. The quotient Verschiebung cotangent map is proved zero from the presented-model Cartier hypotheses. Combining the zero/nonzero Cartier branches constructs an actual isogeny from the original Jacobian to an actual same-dimension abelian variety with zero dV, from C² = 0 alone.

## Completed proof steps

- H is a genuine group scheme. Its order is p in the nonzero square-zero branch. The proof constructs invariant derivations from infinitesimal group translation, then uses Frobenius nilpotence and a local power basis. It does not assume a classification of finite group schemes.
- The actual quotient theorem supplies the quotient scheme, group law and universal property. Properness, smoothness, connectedness and dimension give an actual abelian variety.
- Frobenius and Verschiebung descend uniquely through the quotient; the residual maps are actual group isogenies. Their degrees follow from scheme-theoretic rank multiplication.
- Finite-fibre rational-point lifting and the infinitesimal kernel prove an isomorphism of rational-point groups and preservation of every torsion group and p-rank.
- The quotient's own F and V satisfy the actual Frobenius-twisted factor diagram.
- Cartier squared zero now kills the actual differential of V^(p) followed by V. Residue duality gives absolute Cech Frobenius squared zero; actual projection equivalences and two Picard comparisons identify the actual twice-relative maps. No unproved scheme-projection normalization is supplied as a hypothesis.
- In the Cartier-zero branch, H is isomorphic to the actual V-kernel and has order p^g.
- Conversely, an actual finite flat one-point group of order p has cotangent dimension one, proved by local algebra and the actual group law.

The Cartier-zero route also now proves an actual sheaf isomorphism between pullbacks of the p²-th tensor power of a symmetric invertible sheaf under the residual isomorphism and under the genuine double projection. The symmetric invertible sheaf is itself constructed with an actual finite projective presentation, so its existence is not a caller-supplied input. No finite-field moduli descent or elliptic-product theorem follows by definition.

## Remaining geometric boundary

| Direction | Status |
|---|---|
| Superspecial ⇒ Cartier zero | Previously proved for the presented genus-two models. |
| Cartier zero ⇒ superspecial | Unproved: needs an actual supersingular elliptic-product isomorphism. |
| Supersingular ⇒ Cartier square zero | Previously proved for the presented genus-two models. |
| Cartier square zero ⇒ supersingular | Unproved: needs an actual supersingular elliptic-product isogeny. |

The previous factorization V_A = e ∘ F_(A^(p)), with e: A^(p²) ≅ A, is retained. Neither that isomorphism nor the quotient is an elliptic-product decomposition. Supersingular and superspecial keep their independent geometric definitions, and no classification conclusion is introduced as an axiom or a caller-supplied hypothesis. C² refers to semilinear operator composition, with the corresponding Frobenius-twisted matrix product.

The wider sheet/IKO §1 scope remains as recorded in `SECTION1_COVERAGE.md`: abstract genus-two presentation, full descent to arbitrary perfect fields, the actual crystalline Newton attachment/comparison, remaining automorphism/quotient/isomorphism classifications and cyclic-cover identifications are separate unfinished work.

## Verification

- Full aggregate build passed: 10,932 Lake jobs; all 43 new project modules compiled.
- All 1,094 declaration entries from the new project and vendor modules were audited, including private/generated entries, stored types/bodies and transitive axiom dependencies. Only `propext`, `Classical.choice` and `Quot.sound` occur. Advertised new public theorem names were checked as theorem declarations.
- 9 concrete integration examples passed on the actual y² = x⁵ − 1 models, including characteristic-3 subgroup/quotient/residual degrees and actual twofold-V vanishing, and characteristic-19 subgroup order 361.
- All 152 previous proof modules and 1,936 previous vendor Lean files remain byte-identical. 37 new foundation modules are exact copies from the same pinned upstream commit; no new compatibility ports.
- 310 current source hashes checked; 2,168 project/vendor Lean sources scanned without proof-admission or native-evaluation markers.

Inventory: 195 project proof modules, 1180 public theorem declarations and 41 private supporting lemmas. This checkpoint adds 43 modules, 183 public theorems and 13 private lemmas. These are source counts, not completion percentages.

Lean is pinned to 4.34.0-rc2 and Mathlib to `85e3a25e006c35636f0e53b0e9296caca2685bc0`. The build reuses unchanged checked artifacts and the official pinned Mathlib cache; it is not a clean rebuild of every retained dependency. Historical suites and audits were retained for byte-identical sources rather than rerun.

Reproduce the focused checks with `bash verification/verify_checkpoint26.sh`. Exact logs and hashes are recorded in `verification/checkpoint-26-run.json`; source provenance is in `provenance/checkpoint-26-sources.json`.
