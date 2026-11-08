/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.VerschiebungFrobeniusCriterion
import SupersingularCurves.IKO.VerschiebungCriteria

/-!
# Actual Frobenius-twist isomorphisms from genus-two Cartier vanishing

For any representing Jacobian of a separable quintic or sextic, zero Cartier
constructs a scheme isomorphism from the actual double Frobenius twist to
the Jacobian. Its composition with relative Frobenius is actual Verschiebung.
The conclusion does not assert an elliptic-product decomposition.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.Hyperelliptic.SimpleRootModel
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open NeronModelInfra GoodReductionJacobian
open SupersingularCurves.Geometry SupersingularCurves.Differentials
open SupersingularCurves.IKO

variable {K : Type*} [Field K] [IsAlgClosed K] [NeZero (2 : K)]
  (a : SimpleRootModel K) (p : ℕ) [Fact p.Prime] [CharP K p]
  (hf : a.f.Separable) (hd : a.f.natDegree = 5 ∨ a.f.natDegree = 6)
  (hp : p % 2 = 1)
  {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) a.curveModel.toBase}
  (J : Jacobian a.curveModel s)

include hf hd hp

/-- A zero coefficient matrix constructs an actual Frobenius-twist
isomorphism for every representing Jacobian and base point. -/
theorem jacobian_exists_frobenius_factor_iso_of_matrix_zero
    (h : coefficientMatrix p a.f = 0) :
    ∃ e : SchemeFrobenius.Twist p (J.twistToBase p) ≅ J.designation.P,
      SchemeFrobenius.relative p (J.twistToBase p) ≫ e.hom = J.verschiebung p ∧
        e.hom ≫ J.designation.toBase = SchemeFrobenius.toBase p (J.twistToBase p) :=
  J.exists_frobenius_factor_iso_of_verschiebungCotangent_eq_zero p
    ((a.jacobian_verschiebungCotangent_zero_iff_matrix p hf hd hp J).mpr h)

/-- Vanishing on all regular differentials supplies the actual isomorphism
and its Verschiebung factorization, with no added differential hypothesis. -/
theorem jacobian_exists_frobenius_factor_iso_of_regularCartier_zero
    (h : ∀ ω : regularDifferentials K a.FunctionField, regularCartier p a.x ω = 0) :
    ∃ e : SchemeFrobenius.Twist p (J.twistToBase p) ≅ J.designation.P,
      SchemeFrobenius.relative p (J.twistToBase p) ≫ e.hom = J.verschiebung p ∧
        e.hom ≫ J.designation.toBase = SchemeFrobenius.toBase p (J.twistToBase p) :=
  a.jacobian_exists_frobenius_factor_iso_of_matrix_zero p hf hd hp J
    ((a.all_regularCartier_zero_iff hf hd p hp).mp h)

/-- The same geometric conclusion from the entire scheme-global Cartier
operator, rather than a chosen basis or subspace. -/
theorem jacobian_exists_frobenius_factor_iso_of_globalCartier_zero
    (h : ∀ ω : a.GlobalForms, a.globalCartier p ω = 0) :
    ∃ e : SchemeFrobenius.Twist p (J.twistToBase p) ≅ J.designation.P,
      SchemeFrobenius.relative p (J.twistToBase p) ≫ e.hom = J.verschiebung p ∧
        e.hom ≫ J.designation.toBase = SchemeFrobenius.toBase p (J.twistToBase p) :=
  a.jacobian_exists_frobenius_factor_iso_of_matrix_zero p hf hd hp J
    ((a.all_globalCartier_zero_iff hf hd p hp).mp h)

/-- Matrix vanishing is equivalent to the actual residual scheme-isomorphism
criterion. The displayed factorization is essential to the equivalence. -/
theorem matrix_zero_iff_jacobian_exists_frobenius_factor_iso :
    coefficientMatrix p a.f = 0 ↔
      ∃ e : SchemeFrobenius.Twist p (J.twistToBase p) ≅ J.designation.P,
        SchemeFrobenius.relative p (J.twistToBase p) ≫ e.hom = J.verschiebung p ∧
          e.hom ≫ J.designation.toBase = SchemeFrobenius.toBase p (J.twistToBase p) :=
  (a.jacobian_verschiebungCotangent_zero_iff_matrix p hf hd hp J).symm.trans
    (J.verschiebungCotangent_eq_zero_iff_exists_frobenius_factor_iso p)

/-- The residual isomorphism respects the independently constructed Picard
group law. This still does not assert an elliptic-product decomposition. -/
theorem matrix_zero_iff_jacobian_exists_frobenius_factor_groupIso :
    coefficientMatrix p a.f = 0 ↔
      ∃ e : J.abelianVariety.doubleFrobeniusTwistGroup p ≅ J.abelianVariety.group,
        SchemeFrobenius.relative p (J.twistToBase p) ≫ e.hom.hom.hom.left =
          J.verschiebung p :=
  (a.jacobian_verschiebungCotangent_zero_iff_matrix p hf hd hp J).symm.trans
    (J.verschiebungCotangent_eq_zero_iff_exists_frobenius_factor_groupIso p)

/-- The scheme-isomorphism criterion uses the entire regular differential space. -/
theorem regularCartier_zero_iff_jacobian_exists_frobenius_factor_iso :
    (∀ ω : regularDifferentials K a.FunctionField, regularCartier p a.x ω = 0) ↔
      ∃ e : SchemeFrobenius.Twist p (J.twistToBase p) ≅ J.designation.P,
        SchemeFrobenius.relative p (J.twistToBase p) ≫ e.hom = J.verschiebung p ∧
          e.hom ≫ J.designation.toBase = SchemeFrobenius.toBase p (J.twistToBase p) :=
  (a.all_regularCartier_zero_iff hf hd p hp).trans
    (a.matrix_zero_iff_jacobian_exists_frobenius_factor_iso p hf hd hp J)

/-- The scheme-isomorphism criterion uses the entire global differential space. -/
theorem globalCartier_zero_iff_jacobian_exists_frobenius_factor_iso :
    (∀ ω : a.GlobalForms, a.globalCartier p ω = 0) ↔
      ∃ e : SchemeFrobenius.Twist p (J.twistToBase p) ≅ J.designation.P,
        SchemeFrobenius.relative p (J.twistToBase p) ≫ e.hom = J.verschiebung p ∧
          e.hom ≫ J.designation.toBase = SchemeFrobenius.toBase p (J.twistToBase p) :=
  (a.all_globalCartier_zero_iff hf hd p hp).trans
    (a.matrix_zero_iff_jacobian_exists_frobenius_factor_iso p hf hd hp J)

/-- Global Cartier vanishing is equivalent to an actual group-scheme
isomorphism realizing the residual Verschiebung factor. -/
theorem globalCartier_zero_iff_jacobian_exists_frobenius_factor_groupIso :
    (∀ ω : a.GlobalForms, a.globalCartier p ω = 0) ↔
      ∃ e : J.abelianVariety.doubleFrobeniusTwistGroup p ≅ J.abelianVariety.group,
        SchemeFrobenius.relative p (J.twistToBase p) ≫ e.hom.hom.hom.left =
          J.verschiebung p :=
  (a.all_globalCartier_zero_iff hf hd p hp).trans
    (a.matrix_zero_iff_jacobian_exists_frobenius_factor_groupIso p hf hd hp J)

end SupersingularCurves.Hyperelliptic.SimpleRootModel
