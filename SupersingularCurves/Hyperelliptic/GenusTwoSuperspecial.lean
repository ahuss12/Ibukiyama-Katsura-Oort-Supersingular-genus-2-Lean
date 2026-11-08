/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.SuperspecialVerschiebung
import SupersingularCurves.IKO.VerschiebungCriteria

/-!
# The geometric-to-Cartier superspecial criterion in genus two

Every geometric superspecial Jacobian of a presented separable quintic or
sextic has zero actual Cartier operator on the entire regular and global
differential spaces. The geometric definition remains actual product
isomorphism after algebraic closure. The reverse direction is not assumed.
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

include hf hd hp

/-- IKO Lemma 1.1(ii), geometric-to-matrix direction, for every
representing Jacobian and base point of the presented model. -/
theorem jacobian_isSuperspecial_imp_matrix
    {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) a.curveModel.toBase}
    (J : Jacobian a.curveModel s) (h : J.IsSuperspecial p) :
    coefficientMatrix p a.f = 0 :=
  (a.jacobian_verschiebungCotangent_zero_iff_matrix p hf hd hp J).mp
    (Jacobian.IsSuperspecial.verschiebungCotangent_eq_zero p h)

/-- The existential geometric curve predicate forces the zero matrix. -/
theorem isSuperspecial_imp_matrix
    (h : Geometry.CurveModel.IsSuperspecial p a.curveModel) :
    coefficientMatrix p a.f = 0 := by
  obtain ⟨s, J, hJ⟩ := h
  exact a.jacobian_isSuperspecial_imp_matrix p hf hd hp J hJ

/-- Cartier vanishes on the entire regular differential space. -/
theorem isSuperspecial_imp_cartier_zero
    (h : Geometry.CurveModel.IsSuperspecial p a.curveModel) :
    ∀ ω : regularDifferentials K a.FunctionField, regularCartier p a.x ω = 0 :=
  (a.all_regularCartier_zero_iff hf hd p hp).mpr
    (a.isSuperspecial_imp_matrix p hf hd hp h)

/-- Cartier vanishes on the entire scheme-global differential space. -/
theorem isSuperspecial_imp_globalCartier_zero
    (h : Geometry.CurveModel.IsSuperspecial p a.curveModel) :
    ∀ ω : a.GlobalForms, a.globalCartier p ω = 0 :=
  (a.all_globalCartier_zero_iff hf hd p hp).mpr
    (a.isSuperspecial_imp_matrix p hf hd hp h)

end SupersingularCurves.Hyperelliptic.SimpleRootModel
