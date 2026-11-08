# Checkpoint 32 — checked isotropic graph and polarization foundations

**Block 1 is not complete.** The unconditional elliptic-map theorem and global
supersingular product-isogeny theorem remain open.

Twelve newly checked public theorems in five modules passed normal focused
Lake compilation and a transitive axiom audit. Nine are newly written; three
root-kernel lemmas were promoted from the previously unchecked numerical draft.

## What is now proved

1. **Isotropic graphs from perfect alternating pairings.** For two actual
   abelian surfaces over an algebraically closed field and an auxiliary prime
   different from the characteristic,
   perfect alternating integral Tate pairings construct a rational
   anti-isometry. Its graph has the required rank and integral complement.
   The original integral product pairing vanishes on the actual integral
   graph intersection. The pairings are inputs here; their realization by
   actual line bundles is still in the unchecked assembly.
2. **Actual graph quotient families.** The resulting family has residual
   isogeny degrees `(ell^n)^4`, inherits zero actual dV when the product has
   zero dV, and has the pairing divisibility needed for the proposed root
   construction. An anti-isometry is constructed rather than assumed.
3. **Zero dV on actual binary products.** Over perfect fields, in arbitrary dimensions, zero dV
   on both factors implies zero dV on their actual scheme-theoretic product.
   The supporting differential-detection theorem uses square-zero points
   and the actual product's universal property.
4. **Finite projective presentations on products.** An actual Segre
   construction shows that exterior tensor products of bundles finite by
   sections are finite by sections on the scheme fibre product. The actual
   abelian product bundle is constructed and proved invertible and finite
   by sections from the corresponding properties on the factors.
5. **Finite set of translation-kernel points of a root.** For an invertible root R with
   `M ≅ R^n ⊗ P` and `P` in Pic0, finiteness of the set `kernelPts(M)`
   implies finiteness of `kernelPts(R)`. Kernel invariance under sheaf isomorphism and
   inclusion under tensor powers are also checked.

These statements concern actual schemes, maps, line bundles and Tate modules.
They do not identify finite projective maps with closed immersions.

## Verification and preservation

`bash verification/verify_checkpoint32.sh` reproduces the focused build,
declaration audit, source-integrity check and admission scan. All twelve
advertised theorem names and all 19 stored declaration entries in the five
new modules were audited, including generated entries, stored types/bodies
and transitive dependencies. Only `propext`, `Classical.choice`, and
`Quot.sound` are allowed. No new axiom or proof admission was introduced.

All 335 previous project proof modules and all 4,667 vendor Lean files remain
byte-identical to checkpoint 31. The checked inventory is now 340 project
proof modules, 1,862 public theorems and 82 private supporting lemmas. Those
counts measure declarations, not a completion percentage. The full aggregate
build and historical example suite were not rerun.

## Work that is still unchecked or unproved

Seven continuation files with 26 public theorem drafts are preserved under
`drafts/checkpoint32/`, outside the build and proved inventory. They include
the exact root-section scaling, cancellation against isogeny degrees,
construction of common actual Riemann pairings, the uniform symmetric-bundle
assembly, and the conditional descent/moduli assembly. The new assembly keeps
one quotient family throughout and attempts to choose its starting bundles.
These files have not passed Lean and must not be counted as completed.

The broader build failed before reaching them. Loading the pinned upstream
torsion-density dependency exceeded the workspace's 8 GiB memory limit.
Single-compiler scheduling, synchronous elaboration, and direct compilation
did not resolve that import problem. No diagnostic experiment is certified.
Completed dependencies are preserved in the expanded partial build cache.

The mathematical route still needs checked uniform section bounds, a uniform
very-ampleness/closed-immersion theorem for the resulting nonprincipal
polarizations, and the actual finite-model conclusion `HasFiniteModels`.
Finiteness of a polarization kernel does not imply `KernelTrivial`.
The previously checked finite-model-to-elliptic-map and product-isogeny chain
becomes applicable only after those hypotheses are proved. Integral splitting
is a further requirement for the superspecial product isomorphism. Neither
positive geometric Cartier converse, Block 1, nor the full IKO/Newton project
is finished by this checkpoint.

The separate cache and environment note document the pinned compiler/packages
and reuse procedure. Proof sources and their audits remain authoritative.
