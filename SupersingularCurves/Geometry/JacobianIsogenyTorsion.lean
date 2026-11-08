/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.SupersingularGeometryTorsion
import SupersingularCurves.Geometry.JacobianIndependence
import Theorems.Thm_AlgebraicCurve_Pic0_exists_nsmul_eq_of_charP

/-!
# Geometric supersingularity forces actual Jacobian p-rank zero

Divisibility is proved for the independent divisor-class group and transferred
through the independently constructed Picard point equivalence. The geometric
isogeny may live over the algebraic closure of K: faithful scalar extension
embeds its point kernel into a genuinely finite geometric fibre. This proves
the forward implication from the original product-isogeny definition.

The function-field finiteness witness is the standard one-variable hypothesis,
and is constructed explicitly for every presented hyperelliptic model.
No converse supersingular or superspecial classification is asserted here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v

namespace SupersingularCurves.Geometry.Jacobian
open CategoryTheory AlgebraicGeometry AlgebraicCurve NeronModelInfra
open scoped CategoryTheory.MonObj

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] [IsCurveOver K F]
  {M : AlgebraicCurve.CurveModel K F}
  {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase}
  {p : ℕ} [Fact p.Prime] [CharP K p]

include p in
/-- Divisibility on actual Jacobian points, including multiplication by p,
comes from a theorem about independent divisor classes. -/
theorem points_pow_surjective (J : Jacobian M s)
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (n : ℕ) (hn : n ≠ 0) :
    Function.Surjective (fun P : J.abelianVariety.Points => P ^ n) := by
  intro Q
  obtain ⟨D, hD⟩ := AlgebraicCurve.Pic0.exists_nsmul_eq_of_charP K F p hfg n hn
    (J.picardPoints.symm (Additive.ofMul Q))
  refine ⟨(J.picardPoints D).toMul, ?_⟩
  have h := congrArg J.picardPoints hD
  rw [map_nsmul, J.picardPoints.apply_symm_apply] at h
  exact congrArg Additive.toMul h

/-- A finite geometric isogeny to a supersingular elliptic product forces
trivial p-torsion in the actual original Jacobian point group. -/
theorem IsSupersingular.torsion_trivial
    {J : Jacobian M s} (h : J.IsSupersingular p)
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (P : J.abelianVariety.Points) (hP : P ^ p = 1) : P = 1 := by
  obtain ⟨E, hE, f, hf⟩ := h
  let q := J.abelianVariety.pointsBaseChange (AlgebraicClosure K)
  let fpts := groupSchemePointsHom f
  let := hf.1
  let := finite_groupSchemePointsHom_ker f
  let := finite_ker_comp_of_injective fpts q
    (J.abelianVariety.pointsBaseChange_injective (AlgebraicClosure K))
  exact torsion_trivial_of_finite_kernel_of_pow_surjective p (fpts.comp q)
    (J.points_pow_surjective hfg (p := p) p (Fact.out : p.Prime).ne_zero)
    (ellipticProduct_torsion_trivial E hE) P hP

/-- The conclusion refers to the independently defined geometric p-rank of
the actual Jacobian, not a Cartier-based replacement for supersingularity. -/
theorem IsSupersingular.hasPRankOver_zero
    {J : Jacobian M s} (h : J.IsSupersingular p)
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    J.abelianVariety.HasPRankOver p 0 :=
  (AbelianVariety.hasPRankOver_zero_iff J.abelianVariety p).mpr (h.torsion_trivial hfg)

end SupersingularCurves.Geometry.Jacobian
