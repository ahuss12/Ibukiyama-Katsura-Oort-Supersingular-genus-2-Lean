# Checkpoint 32: unchecked continuation

These seven Lean files have NOT passed compilation or the axiom audit. They
are excluded from the project import tree and proved-theorem inventory.
The original checkpoint-31 drafts are retained separately as history.

The active draft assembly has 26 public theorem drafts and one private lemma.
It attempts the following chain:

1. `PolarisationRootNumerics`: positivity, higher-cohomology vanishing, exact
   H0 scaling, and a symmetric cube finite by sections. Its three kernel
   lemmas have moved to the checked `PolarisationRootKernel` module.
2. `AbelianIsogenyRootNumerics`: cancel the degree m^g against the m-th root
   scaling; obtain a symmetric finite bundle of rank 3^g h0(M).
3. `AbelianTateProductPolarization`: construct common actual Riemann pairings
   at sufficiently large auxiliary primes, and the actual isotropic graph
   quotient sequence. The actual product bundle and its finite presentation
   have moved to the checked `AbelianProductLineBundle` module.
4. `ScalarFrobeniusTateQuotientRoots`: construct a root from divisibility of
   the actual pulled-back pairing, then obtain quotient-root numerical bounds.
   The root construction requires characteristic different from two.
5. `ScalarFrobeniusTateUniformPolarization`: combine those results on one and
   the same quotient sequence, choose the starting bundles, and obtain a
   positive section bound independent of the quotient index.
6. `ScalarFrobeniusPolarizedDescentRank` and `PolarizedFiniteModels`: conditional
   very-ample descent and finite-model assembly. Closed immersion is an
   explicit hypothesis; these drafts do not supply it.

The build stopped before checking these files. Loading the pinned dependency
`P2M.Sol.S_GoodReductionJacobian_AbelianSchemePropertyBundle_forall_mem_of_isClosed_of_forall_torsion_mem`
exceeded the 8 GiB workspace limit. Single-compiler scheduling, synchronous
elaboration and a direct compiler invocation did not resolve it. Diagnostic
copies did not produce any certified result. Vendor sources remain unchanged.

To continue in a runtime able to load that dependency, restore the matching
checkpoint source, build cache and Mathlib cache, then copy these seven files
into `SupersingularCurves/Geometry/` and run:

```sh
lake build SupersingularCurves.Geometry.ScalarFrobeniusTateUniformPolarization
```

Fix any actual errors exposed when the drafts are reached, then audit every
new declaration and its transitive axioms before adding it to the proved
inventory. The two descent/moduli drafts are later targets. Do not equate a
finite projective morphism with a closed immersion, or a finite polarization
kernel with `KernelTrivial`. The unconditional elliptic map, global product
isogeny, integral superspecial splitting and both positive Cartier converses
are still open.
