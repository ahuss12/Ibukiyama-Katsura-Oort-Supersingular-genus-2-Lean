# Checkpoint 25 — actual Frobenius factor and group isomorphism

**The planned Frobenius-factor argument is completed in Lean. The two requested elliptic-product converses, and therefore full Block 1, remain unfinished.**

## Main proved result

For every abelian variety A over an algebraically closed field of characteristic p, zero actual Verschiebung cotangent at the identity is equivalent to the existence of an actual group-scheme isomorphism e: A^(p²) ≅ A satisfying

V_A = e ∘ F_(A^(p)).

The factorization identity is part of the theorem: an unspecified isomorphism between the double twist and A is not the stated criterion. The factor is constructed from actual scheme morphisms and the independently defined Verschiebung and group laws. For each presented separable quintic or sextic in odd characteristic, this criterion is equivalent to coefficient-matrix zero and to Cartier vanishing on the entire regular or global differential space, for every representing Jacobian and base point.

The proof closes the previously missing identity-to-global step. Translation moves the zero cotangent differential to all rational points. The local cotangent bridge controls pulled-back universal differentials modulo each closed-point maximal ideal. Reduced/projective differential detection makes them vanish globally. The existing root and gluing arguments then construct the unique Frobenius factor. Finite-flat descent and the equal actual degrees p^g prove the residual factor has degree one and is an isomorphism. Faithfully flat cancellation proves compatibility with the group laws. Conversely, relative Frobenius has zero cotangent differential, proving the reverse criterion.

Primary entry points are in `Geometry/VerschiebungFrobeniusCriterion.lean` and `Hyperelliptic/GenusTwoFrobeniusIsomorphism.lean`:

- `Jacobian.verschiebungCotangent_eq_zero_iff_exists_frobenius_factor_groupIso`
- `SimpleRootModel.matrix_zero_iff_jacobian_exists_frobenius_factor_groupIso`
- `SimpleRootModel.globalCartier_zero_iff_jacobian_exists_frobenius_factor_groupIso`

The existing independent definitions of supersingular and superspecial are unchanged.

## Actual subgroup progress

The actual subgroup H = ker(F_(A^(p))) ∩ ker(V_A) is constructed by scheme pullbacks. It is finite flat, closed, killed by p, and supported at one geometric point, with the subgroup laws verified on all test schemes.

At p-rank zero, ker(V_A) has one geometric point but still has scheme length p^g. When g > 0 its cotangent space cannot vanish. The actual inclusion of H into ker(V_A) induces a cotangent isomorphism, so H also has nonzero cotangent space. This constructs a genuinely nontrivial infinitesimal subgroup; it does not construct an elliptic-product isogeny.

The new actual fibre cotangent exact sequence gives the sharper formula dim Cot(H) = g − rank(dV). On an actual abelian surface, p-rank zero and dV ≠ 0 force rank(dV) = 1, so dim Cot(H) = 1. For every presented genus-two model, C² = 0 with C ≠ 0 therefore gives cotangent dimension one; C = 0 gives cotangent dimension two. These are cotangent dimensions, not finite subgroup orders. The precise matrix and global-Cartier applications are in `Hyperelliptic/GenusTwoFiniteSubgroup.lean`.

In characteristic three, every separable quintic or sextic has a nonzero genus-two Cartier matrix. The previously proved superspecial-to-Cartier implication therefore rules out geometric superspeciality for every representing Jacobian of these presented curves.

## Remaining classification boundary

| Direction | Current status |
|---|---|
| Superspecial ⇒ C = 0 | Proved for the presented genus-two models. |
| C = 0 ⇒ superspecial | Unproved: needs an actual supersingular elliptic-product isomorphism. |
| Supersingular ⇒ C² = 0 | Previously proved for the presented genus-two models. |
| C² = 0 ⇒ supersingular | Unproved: needs an actual supersingular elliptic-product isogeny. |

Here C² means composition of the semilinear Cartier operator; the matrix formulation uses the corresponding Frobenius-twisted product.

The new isomorphism A^(p²) ≅ A is a completed intermediate geometric theorem, not an elliptic-product decomposition. On the subgroup route for a non-superspecial genus-two surface, the next missing arguments establish order p, construct the quotient, and show its actual Verschiebung cotangent vanishes. Product splitting is then still needed. The bounded review in `provenance/checkpoint-25-classification-route-review.md` records the arithmetic and constructive routes inspected and their missing realization inputs. No classification conclusion has been introduced as an axiom or supplied hypothesis.

The remaining wider project scope is unchanged: abstract genus-two presentation; full descent to arbitrary perfect fields; scheme-projection interpretation of the cohomological scalar untwist; actual crystalline Newton attachment and comparison; remaining IKO §1 automorphism, quotient and isomorphism results; and the sheet's cyclic-cover identifications. `SECTION1_COVERAGE.md` retains the full ledger.

## Verification

All current checks passed on pinned Lean 4.34.0-rc2 and Mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0`:

- Full aggregate build: 10,852 Lake jobs; all 18 new project modules compiled.
- Transitive axiom audit: 197 entries from every new module, including private/generated entries and stored declaration types/bodies. Only `propext`, `Classical.choice`, and `Quot.sound` occur. All advertised new public theorem names resolve to theorem declarations.
- 7 concrete integration examples, including actual residual scheme/group isomorphisms in characteristic 19 and actual finite kernel length and nonzero cotangents in characteristic 3 for y² = x⁵ − 1.
- All 134 previous proof modules and 1,936 previous vendor Lean files are byte-identical. No vendor additions or compatibility ports were needed.
- 260 current source hashes checked; 2,088 project/vendor Lean sources scanned without proof-admission or native-evaluation markers.

Inventory: **152 project proof modules, 997 public theorem declarations, 28 private supporting lemmas**. Additions: 18 modules, 106 public theorems and 4 private lemmas. These are inventory counts, not completion percentages.

Unchanged checked artifacts and the official pinned Mathlib cache were reused. This is not a clean rebuild of every retained dependency; historical suites and audits were retained for byte-identical sources rather than rerun. Runtime restoration provenance remains recorded from checkpoint 23.

Reproduce the focused checks with `bash verification/verify_checkpoint25.sh`. Exact logs and their hashes are in `verification/checkpoint-25-run.json`; source provenance is in `provenance/checkpoint-25-sources.json`.
