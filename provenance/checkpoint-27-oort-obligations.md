# Oort elliptic restriction lifting: implemented input and remaining proof

This is a development note, not a classification theorem. The four new modules below are frozen. No preexisting project or vendor proof source was edited by this agent or its child.

## Implemented, actual geometric input

All module paths are relative to `/workspace/scratch/8cf314e8ad34/project/supersingular-curves-mini/SupersingularCurves/Geometry/`.

* `EllipticTorsionRealization.lean`: constructs the actual schemes `torsion` and `frobeniusKernel`. `frobeniusOnTorsion_isPullback` identifies the map E[p]→ker(V) as a base change of actual relative Frobenius. It is finite, flat, surjective, and has rank p. `frobeniusKernel_isPullback` identifies its identity fibre. `restrictFrobeniusKernel` restricts any actual pointed torsion-scheme map, and `restrictFrobeniusKernel_torsion`/`_unique` prove compatibility and uniqueness. `onTorsion` and `onFrobeniusKernel` come from actual elliptic group homomorphisms. The closure statements `one_factors`, `mul_factors`, and `inv_factors` prove the genuine subgroup property on every test scheme.
* `EllipticTorsionRealizationDieudonne.lean`: `AbelianVariety.torsionHopfRealization` constructs the finite Hopf algebra of actual torsion with a natural multiplicative comparison on every test algebra. `TorsionHopfRealization.map` and `dieudonneMap` are induced by actual group morphisms, with identity/composition laws and F/V compatibility. The elliptic p-torsion coordinate algebra has rank p². This does not identify the Dieudonné object with a rank-two semilinear normal form.
* `EllipticFrobeniusKernelHopf.lean`: `frobeniusKernelHopf` constructs an actual Spec(HF)≅ker(F), and proves rank(HF)=p. `FrobeniusKernelHopf.restriction` is the genuine coordinate BialgHom from torsion to its Frobenius kernel, identified with the actual inclusion on all test algebras. `dieudonneRestriction` commutes with both operators.
* `EllipticTorsionRealizationDivisibility.lean`: `dividedHom` is constructed by effective epimorphism descent along [p]; multiplication preservation is proved by descent along [p]×[p]. `torsion_zero_iff_exists_dividedHom` proves that an actual elliptic group homomorphism vanishes on the whole E[p] scheme exactly when it factors as [p] followed by an actual group homomorphism. There is no supplied realization or divided map. The theorem works for prime p over an algebraically closed field without requiring that p equal the characteristic.

The first module's targeted build passed 10,397 jobs; the Hopf pair's final build passed 10,437 jobs; the divisibility module's final build passed 10,400 jobs. Fifteen core declarations in the first/divisibility modules were checked with `#print axioms`: only `propext`, `Classical.choice`, and `Quot.sound` occurred. Root owns the aggregate audit.

Logs under `/workspace/scratch/8cf314e8ad34/`:

* `elliptic-torsion-realization28-build.log`, `elliptic-torsion-realization28-axioms.log`
* `elliptic-frobenius-kernel-hopf-build.log`
* `elliptic-torsion-divisibility28-build.log`, `elliptic-torsion-divisibility28-axioms.log`

An attempted import of the already-present but previously unbuilt abelian-rigidity theorem hit old-source compatibility failures in its dependency closure. The final divisibility module does not import that theorem; the direct faithful-flat proof avoids it. No vendor port was made.

## Exact remaining local lifting problem

For supersingular elliptic curves E₁,E₂ over an algebraically closed field K of characteristic p, Oort Lemma 5 says: a group morphism ker(F_E₂)→ker(F_E₁) which extends to a group morphism E₂[p]→E₁[p] is the restriction of an actual elliptic group homomorphism E₂→E₁. Neither this surjectivity statement nor an equivalent assumed fullness has been introduced into the new modules.

The first concrete remaining bridge is to identify canonical finite-group Verschiebung with restriction of the actual ambient Verschiebung over a general perfect field, retaining Frobenius twists. A useful route is:

1. Construct twisted finite-Hopf Verschiebung, with its Cartier-dual pairing characterization and naturality under every finite group morphism. The existing canonical theorem is over ZMod p. The general characteristic-p identity `PDivisibleGroup.Hopf.nsmulAlgHom_eq_sum_pow_apply_smul_pow` suggests an inverse-Frobenius-semilinear construction over a perfect field, but its twisted Hopf realization must be proved.
2. Construct the compatible actual levels E[p²] and E[p], their transition, and the coordinate identification H_p≅range([p]*:H_p²→H_p²). Use that identification to compare ambient V with canonical finite V; the equations FV=VF=[p] on a single killed-by-p level do not establish uniqueness.
3. For an arbitrary torsion group morphism, combine F/V naturality with the existing actual factorization V=e∘F. Cancel the finite-flat Frobenius projection to obtain compatibility of its ker(F) restriction with e:ker(F)^(p²)≅ker(F). A faithful cotangent action on this rank-p height-one group then bounds its possible restrictions by p². Alternatively prove an actual ker(F)≅α_p identification. Neither the requisite cotangent faithfulness nor that identification is asserted here.
4. Supply a supersingular E₀/F_p with all geometric endomorphisms defined over F_p², and identify its actual scheme End group with a free Z-module of rank four. Existing Weierstrass arithmetic gives rank-four pointwise rational endomorphisms under an algebraicity hypothesis; the actual scheme/finite-field-model bridge must still be supplied. The new divisibility theorem gives the required full-torsion restriction kernel p·End. Counting the p⁴ full-torsion restrictions, and a kernel of size at most p² for restriction to ker(F), supplies all p² permitted scalars. Separable isogenies to E₀ transfer this to arbitrary E₁,E₂.

The local rank data alone cannot replace step 1–3: the additive group α_(p²)=Spec K[t]/(t^(p²)) has rank p², is killed by p, and has Frobenius-kernel rank p, yet t↦a·t gives arbitrary scalar restrictions for a∈K. The elliptic V/duality constraint is essential.

## Precise proof sources

Original Oort 1975, printed pp.38–41 (Lemma 5 and the inseparable induction): `/workspace/scratch/8cf314e8ad34/checkpoint27-oort-original/Oort-1975.pdf`; OCR: sibling `ocr.txt`. Canonical source: https://gdz.sub.uni-goettingen.de/download/pdf/PPN235181684_0214/LOG_0012.pdf .

Pinned upstream is `anthropics/fermats-last-theorem@aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`.

The existing finite-level comparison argument is in:
`/workspace/scratch/8cf314e8ad34/classification-source-inspection/P2M/Sol/S_ModularCurve_JHNeronObjectAtP_LevelData_restrict_frobenius_eq_pow_and_cartierDual_map_restrict_verschiebung_eq_pow_of_abelianSchemePropertyBundle.lean`.
Lines 187–201 establish V(a^p)=[p]*a; 202–215 establish transition compatibility; 217–243 compare canonical V using the next level's range identification. The exported theorem is specialized to the modular setup over F_p; there is no exported general perfect-field comparison.

Canonical finite V is in sibling
`S_PDivisibleGroup_Hopf_exists_verschiebung_algHom_zmodp.lean`: basis construction line 64, pairing characterization line 77, FV=p line 101, multiplication line 179, comultiplication line 208, final theorem line 257.

Separate global gap: even a completed Oort Lemma 5 would not construct the initial elliptic map/product isogeny into a surface with dV=0. Oort's surface induction starts with that genuine global existence theorem. Thus Block 1 product classification remains unproved.
