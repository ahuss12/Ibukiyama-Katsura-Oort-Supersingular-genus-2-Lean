/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.JacobianQuotientVerschiebung
import SupersingularCurves.Hyperelliptic.GenusTwoQuotient
import SupersingularCurves.Geometry.GlobalCartierModels

/-!
# Square-zero Cartier constructs an isogeny to a surface with zero dV

Every represented separable genus-two quintic or sextic with square-zero
Cartier admits an actual group isogeny to an actual abelian variety with
zero Verschiebung cotangent map. In the nonzero-Cartier branch the target
is the genuine simultaneous-kernel quotient. Its dimension, p-rank, finite
kernel, factor ranks and actual twice-V comparison are all supplied.
-/
set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.Hyperelliptic.SimpleRootModel
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open NeronModelInfra SupersingularCurves.Geometry SupersingularCurves.IKO
open FrobeniusVerschiebungSubgroup

variable {K : Type*} [Field K] [IsAlgClosed K] [NeZero (2 : K)]
  (a : SimpleRootModel K) (p : ℕ) [Fact p.Prime] [CharP K p]
  (hf : a.f.Separable) (hd : a.f.natDegree = 5 ∨ a.f.natDegree = 6)
  (hp : p % 2 = 1)
  {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) a.curveModel.toBase}
  (J : Jacobian a.curveModel s)
  (D : QuotientData p J.abelianVariety)

local instance quotient_smooth : Smooth D.group.X.hom := D.smooth
include hf hd hp

/-- The actual quotient has zero Verschiebung cotangent from full-space
Cartier squared zero and Cartier nonzero, with no extra rank or p-rank input. -/
theorem jacobian_quotient_verschiebungCotangent_eq_zero_of_globalCartier
    (hC2 : ∀ ω : a.GlobalForms, a.globalCartier p (a.globalCartier p ω) = 0)
    (hC : ¬ ∀ ω : a.GlobalForms, a.globalCartier p ω = 0) :
    GroupScheme.verschiebungCotangent p D.group
      (GroupScheme.law_commutative D.group) = 0 := by
  apply J.quotient_verschiebungCotangent_eq_zero_of_globalCartier_square_zero
    p D (differentialChart a.curveModel) a.x (a.genus_eq_two hf hd)
    ((a.jacobian_hasPRankOver_zero_iff_globalCartier_square_zero p hf hd hp J).mpr hC2)
  · intro hV
    exact hC ((J.verschiebungCotangent_eq_zero_iff_forall
      (differentialChart a.curveModel) p a.x).mp hV)
  · exact hC2

/-- The twisted coefficient-matrix square criterion gives zero actual dV
on the constructed quotient whenever the matrix itself is nonzero. -/
theorem jacobian_quotient_verschiebungCotangent_eq_zero_of_matrix
    (hC2 : (coefficientMatrix p a.f).map (fun c => c ^ p) * coefficientMatrix p a.f = 0)
    (hC : coefficientMatrix p a.f ≠ 0) :
    GroupScheme.verschiebungCotangent p D.group
      (GroupScheme.law_commutative D.group) = 0 :=
  a.jacobian_quotient_verschiebungCotangent_eq_zero_of_globalCartier p hf hd hp J D
    ((a.all_globalCartier_square_zero_iff hf hd p hp).mpr hC2)
    (fun h => hC ((a.all_globalCartier_zero_iff hf hd p hp).mp h))

omit D in
/-- Square-zero global Cartier constructs a genuine isogeny from the actual
Jacobian to an actual abelian variety of the same genus with zero dV. -/
theorem jacobian_exists_isogeny_to_zero_verschiebungCotangent_of_globalCartier
    (hC2 : ∀ ω : a.GlobalForms, a.globalCartier p (a.globalCartier p ω) = 0) :
    ∃ (B : AbelianVariety K (genusFF K a.FunctionField))
      (f : J.abelianVariety.group ⟶ B.group),
      IsIsogeny f ∧ GroupScheme.verschiebungCotangent p B.group
        (GroupScheme.law_commutative B.group) = 0 :=
  J.exists_isogeny_to_zero_verschiebungCotangent_of_globalCartier_square_zero p
    (differentialChart a.curveModel) a.x (a.genus_eq_two hf hd)
    ((a.jacobian_hasPRankOver_zero_iff_globalCartier_square_zero p hf hd hp J).mpr hC2) hC2

omit D in
/-- The matrix criterion constructs an actual isogeny to zero dV, including
both the zero and nonzero Cartier branches. -/
theorem jacobian_exists_isogeny_to_zero_verschiebungCotangent_of_matrix
    (hC2 : (coefficientMatrix p a.f).map (fun c => c ^ p) * coefficientMatrix p a.f = 0) :
    ∃ (B : AbelianVariety K (genusFF K a.FunctionField))
      (f : J.abelianVariety.group ⟶ B.group),
      IsIsogeny f ∧ GroupScheme.verschiebungCotangent p B.group
        (GroupScheme.law_commutative B.group) = 0 :=
  a.jacobian_exists_isogeny_to_zero_verschiebungCotangent_of_globalCartier p hf hd hp J
    ((a.all_globalCartier_square_zero_iff hf hd p hp).mpr hC2)

end SupersingularCurves.Hyperelliptic.SimpleRootModel
