/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.ScalarFrobeniusTatePolarizedDescent
import SupersingularCurves.Geometry.PolarisationRootNumerics
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_comp_eq_of_isPullback_of_iso

/-!
# Exact section rank in the Frobenius finite-field polarized model

The prescribed symmetric very ample bundle descends after the fixed p^2 power.
Its section count is (p^2)^g times the original count, on every geometric fibre.
The closed-immersion input remains explicit; numerical boundedness is proved.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SupersingularCurves.Geometry.AbelianVariety
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian
open AlgebraicGeometry.Polarisation FrobeniusDescent PolarisationRootNumerics

variable {K : Type} [Field K] [IsAlgClosed K] {g : ℕ}
  (A : AbelianVariety K g) (p : ℕ) [Fact p.Prime] [CharP K p]

/-- Finite-field descent preserves the explicit H0 bound up to the fixed
factor p^(2g), independent of the quotient level. -/
theorem exists_finiteField_polarized_model_with_rank
    (hV : GroupScheme.verschiebungCotangent p A.group A.groupScheme_law_commutative = 0)
    (L : A.group.X.left.Modules) (hL : Scheme.Modules.IsInvertible L)
    (hsym : Nonempty ((Scheme.Modules.pullback ((𝟙 A.group.X)⁻¹).left).obj L ≅ L))
    (hclosed : L.ClosedImmersionBySections A.group.X.hom) :
    ∃ (A₀ : AbelianVariety (fixedField K p 2) g) (M₀ : A₀.group.X.left.Modules),
      Scheme.Modules.IsInvertible M₀ ∧ M₀.ClosedImmersionBySections A₀.group.X.hom ∧
      Nonempty (A.group ≅ (A₀.baseChange K).group) ∧
      ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : fixedField K p 2 →+* k'),
        Scheme.Modules.geomFibreH0Finrank A₀.group.X.hom M₀ k' sk =
          (p ^ 2) ^ g * Scheme.Modules.geomFibreH0Finrank A.group.X.hom L K (RingHom.id K) := by
  obtain ⟨A₀, M₀, d, hM₀, hc₀, hd, hpol, hgroup, _⟩ :=
    A.exists_finiteField_polarized_abelian_model p hV L hL hsym hclosed
  have hfs : L.FiniteBySections A.group.X.hom := by
    obtain ⟨N, P, hP⟩ := hclosed
    letI := hP
    exact ⟨N, P, inferInstance⟩
  have hdim (s : Spec (CommRingCat.of K)) :
      topologicalKrullDim (A.group.X.hom.base ⁻¹' {s}) = g :=
    SmoothOfRelativeDimension.topologicalKrullDim_preimage_singleton_eq A.group.X.hom g s
      (A.abelianSchemePropertyBundle.connectedFibres s).nonempty
  obtain ⟨hKL, hpos⟩ := kernelPts_finite_and_geomFibreH0Finrank_pos_of_finiteBySections
    K A.group.X.hom (GroupScheme.law A.group) A.groupScheme_law_commutative
    A.abelianSchemePropertyBundle g hdim L hL hfs
  have hpow := geomH0_tensorPow K A.group.X.hom (GroupScheme.law A.group)
    A.groupScheme_law_commutative A.abelianSchemePropertyBundle g L hL hKL
    (hpos K (RingHom.id K)) (p ^ 2) (pow_pos (Fact.out : p.Prime).pos 2) K (RingHom.id K)
  have hbase := Scheme.Modules.geomFibreH0Finrank_comp_eq_of_isPullback_of_iso
    (algebraMap (fixedField K p 2) K) A₀.group.X.hom A.group.X.hom d hd
    M₀ (L.tensorPow (p ^ 2)) hpol K (RingHom.id K)
  simp only [RingHom.id_comp] at hbase
  refine ⟨A₀, M₀, hM₀, hc₀, hgroup, ?_⟩
  intro k' _ _ sk
  have e₁ := Scheme.Modules.geomFibreH0Finrank_comp_eq A₀.group.X.hom M₀ hM₀
    (fixedField K p 2) k' (RingHom.id _) sk
  have e₂ := Scheme.Modules.geomFibreH0Finrank_comp_eq A₀.group.X.hom M₀ hM₀
    (fixedField K p 2) K (RingHom.id _) (algebraMap (fixedField K p 2) K)
  simp only [RingHom.comp_id] at e₁ e₂
  exact e₁.trans (e₂.symm.trans (hbase.trans hpow))

end SupersingularCurves.Geometry.AbelianVariety
