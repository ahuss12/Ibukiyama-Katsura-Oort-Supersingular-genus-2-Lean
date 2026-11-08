/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.AbelianTateRiemannForm
import Theorems.Thm_AlgebraicGeometry_Polarisation_kernelPts_finite_and_geomFibreH0Finrank_pos_of_finiteBySections
import Theorems.Thm_AlgebraicGeometry_Polarisation_mem_kernelPts_iff_nonempty_pullback_translate_iso
import Theorems.Thm_AlgebraicGeometry_RiemannForm_exists_addSubgroup_mem_iff_nonempty_pullback_translation_iso
import Theorems.Thm_AlgebraicGeometry_RiemannForm_translation_eq_translate_toUnitPt_and_translate_eq_translation_ofUnitPt

/-! # Actual perfect Riemann pairings at sufficiently large auxiliary primes -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SupersingularCurves.Geometry.AbelianTate
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open RelativeGroupLaw AlgebraicGeometry.RiemannForm

variable {K : Type} [Field K] [IsAlgClosed K] {g : ℕ}

/-- The actual translation kernel of a finite-by-sections invertible line
bundle has no primary torsion at any prime exceeding a finite bound. -/
theorem exists_bound_translation_kernel (A : AbelianVariety K g)
    (M : A.group.X.left.Modules) (hM : Scheme.Modules.IsInvertible M)
    (hfs : M.FiniteBySections A.group.X.hom) :
    ∃ N : ℕ, 0 < N ∧ ∀ (ℓ : ℕ), ℓ.Prime → N < ℓ →
      ∀ (n : ℕ) (Q : GeometricPoints A K), ℓ ^ n • Q = 0 →
        Nonempty ((Scheme.Modules.pullback (translation A.group.X.hom
          (GroupScheme.law A.group) (AlgPoints.toPoint Q))).obj M ≅ M) → Q = 0 := by
  let L := GroupScheme.law A.group
  have hdim (s : Spec (CommRingCat.of K)) :
      topologicalKrullDim (A.group.X.hom.base ⁻¹' {s}) = g :=
    SmoothOfRelativeDimension.topologicalKrullDim_preimage_singleton_eq A.group.X.hom g s
      (A.abelianSchemePropertyBundle.connectedFibres s).nonempty
  have hfin := (Polarisation.kernelPts_finite_and_geomFibreH0Finrank_pos_of_finiteBySections
    K A.group.X.hom L A.groupScheme_law_commutative A.abelianSchemePropertyBundle
    g hdim M hM hfs).1
  obtain ⟨H, hH⟩ := exists_addSubgroup_mem_iff_nonempty_pullback_translation_iso
    K A.group.X.hom L A.groupScheme_law_commutative M
  let ι : H → Polarisation.kernelPts A.group.X.hom L M := fun x =>
    ⟨toUnitPt A.group.X.hom (AlgPoints.toPoint x.1), by
      apply (Polarisation.mem_kernelPts_iff_nonempty_pullback_translate_iso K
        A.group.X.hom L M _).mpr
      rw [← (translation_eq_translate_toUnitPt_and_translate_eq_translation_ofUnitPt
        K A.group.X.hom L).1]
      exact (hH x.1).mp x.2⟩
  have hinj : Function.Injective ι := by
    intro x y h
    apply Subtype.ext
    apply AlgPoints.toPoint_injective
    apply Subtype.ext
    exact congrArg (fun z => z.1.1) h
  letI := hfin.fintype
  haveI : Finite H := Finite.of_injective ι hinj
  have hN : 0 < Nat.card H := Nat.card_pos
  refine ⟨Nat.card H, hN, ?_⟩
  intro ℓ hprime hlt n Q hQ hQM
  let q : H := ⟨Q, (hH Q).mpr hQM⟩
  have hq : ℓ ^ n • q = 0 := Subtype.ext hQ
  have hcop : Nat.Coprime (ℓ ^ n) (Nat.card H) :=
    ((hprime.coprime_iff_not_dvd).mpr (Nat.not_dvd_of_pos_of_lt hN hlt)).pow_left n
  have hd : addOrderOf q ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hq) (addOrderOf_dvd_natCard q)
  have hz : q = 0 := AddMonoid.addOrderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one hd)
  exact congrArg Subtype.val hz

/-- A genuine finite-by-sections line bundle constructs perfect alternating
forms for every sufficiently large prime different from the characteristic. -/
theorem exists_bound_perfect_riemannPairing (A : AbelianVariety K g)
    (M : A.group.X.left.Modules) (hM : Scheme.Modules.IsInvertible M)
    (hfs : M.FiniteBySections A.group.X.hom) :
    ∃ N : ℕ, 0 < N ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], N < ℓ → (ℓ : K) ≠ 0 →
      ∃ (ζ : ℕ → K) (e : Pairing ℓ A),
        (∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ n)) ∧ (∀ n, ζ (n + 1) ^ ℓ = ζ n) ∧
          IsRiemannPairing A M ℓ ζ e ∧ e.IsAlt ∧ e.IsPerfPair := by
  obtain ⟨N, hN, hbound⟩ := exists_bound_translation_kernel A M hM hfs
  refine ⟨N, hN, ?_⟩
  intro ℓ _ hlt hℓ
  obtain ⟨ζ, e, hζ, hζℓ, he, halt⟩ := exists_riemannPairing A M hM ℓ hℓ
  exact ⟨ζ, e, hζ, hζℓ, he, halt,
    IsRiemannPairing.perfect A M hM ℓ hℓ ζ hζ hζℓ e he (hbound ℓ Fact.out hlt)⟩

end SupersingularCurves.Geometry.AbelianTate
