/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.GlobalDifferentials
import SupersingularCurves.Geometry.CartierTransport

/-!
# Cartier on actual global differential sections

The operator is transported from the existing regular Cartier map through the
proved generic-restriction equivalence. Its definition does not involve a
Jacobian, a duality pairing, or Verschiebung. The comparison with the scheme's
own function field follows from naturality under the specified field isomorphism.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

namespace SupersingularCurves.Geometry.DifferentialChart
open CategoryTheory AlgebraicGeometry AlgebraicCurve KaehlerDifferential
open SupersingularCurves.Differentials
variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
  [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
  {M : AlgebraicCurve.CurveModel K F} (V : DifferentialChart M)
  (p : ℕ) [Fact p.Prime] [CharP K p]
  (x : F) [FiniteDimensional (IntermediateField.adjoin K {x}) F]

/-- Existing regular Cartier, conjugated by actual generic restriction. -/
def globalCartier : V.GlobalForms →+ V.GlobalForms :=
  V.regularEquiv.symm.toAddMonoidHom.comp
    ((regularCartier p x).comp V.regularEquiv.toAddMonoidHom)

theorem globalCartier_apply (ω : V.GlobalForms) :
    V.globalCartier p x ω =
      V.regularEquiv.symm (regularCartier p x (V.regularEquiv ω)) := rfl

@[simp] theorem regularEquiv_globalCartier (ω : V.GlobalForms) :
    V.regularEquiv (V.globalCartier p x ω) = regularCartier p x (V.regularEquiv ω) :=
  V.regularEquiv.apply_symm_apply _

theorem globalCartier_pow_smul (a : K) (ω : V.GlobalForms) :
    V.globalCartier p x (a ^ p • ω) = a • V.globalCartier p x ω := by
  change V.regularEquiv.symm (regularCartier p x (V.regularEquiv (a ^ p • ω))) =
    a • V.regularEquiv.symm (regularCartier p x (V.regularEquiv ω))
  rw [map_smul, regularCartier_pow_smul, map_smul]

/-- The inverse Frobenius scalar action remains explicit in the type. -/
def globalCartierSemilinear :
    V.GlobalForms →ₛₗ[(frobeniusEquiv K p).symm.toRingHom] V.GlobalForms where
  toFun := V.globalCartier p x
  map_add' := map_add (V.globalCartier p x)
  map_smul' a ω := by
    change V.globalCartier p x (a • ω) =
      (frobeniusEquiv K p).symm a • V.globalCartier p x ω
    simpa only [frobeniusEquiv_symm_pow_p] using
      V.globalCartier_pow_smul p x ((frobeniusEquiv K p).symm a) ω

theorem globalCartierSemilinear_apply (ω : V.GlobalForms) :
    V.globalCartierSemilinear p x ω = V.globalCartier p x ω := rfl

theorem globalCartier_independent_of_coordinate (y : F)
    [FiniteDimensional (IntermediateField.adjoin K {y}) F] :
    V.globalCartier p x = V.globalCartier p y := by
  apply AddMonoidHom.ext
  intro ω
  exact congrArg V.regularEquiv.symm (Subtype.ext
    (congrArg (fun C : Ω[F⁄K] →+ Ω[F⁄K] => C (V.regularEquiv ω).val)
      (cartier_independent_of_coordinate p x y)))

/-- The original field's Cartier equals Cartier on the actual scheme function
field after generic restriction and the prescribed function-field isomorphism.
The curve instance on that field is supplied by the smooth proper model. -/
theorem schemeRegularEquiv_globalCartier (ω : V.GlobalForms) :
    letI := M.functionFieldAlgebra
    letI : IsCurveOver K M.C.functionField :=
      isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
        M.toBase (RingEquiv.refl _) (fun _ => rfl)
    ∀ (y : M.C.functionField)
      [FiniteDimensional (IntermediateField.adjoin K {y}) M.C.functionField],
      V.schemeRegularEquiv (V.globalCartier p x ω) =
        regularCartier p y (V.schemeRegularEquiv ω) := by
  letI := M.functionFieldAlgebra
  letI : IsCurveOver K M.C.functionField :=
    isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase (RingEquiv.refl _) (fun _ => rfl)
  intro y hy
  letI : Algebra.EssFiniteType K M.C.functionField :=
    Algebra.EssFiniteType.of_surjective M.ffAlgEquiv.toAlgHom M.ffAlgEquiv.surjective
  letI : ∀ w : Place K F, w.DCoordGenerates := dCoordGenerates_of_isCurveOver
  letI : ∀ w : Place K M.C.functionField, w.DCoordGenerates := dCoordGenerates_of_isCurveOver
  apply (regularDifferentialCongr M.ffAlgEquiv.symm).injective
  change V.regularEquiv (V.globalCartier p x ω) = _
  rw [regularEquiv_globalCartier]
  exact (regularDifferentialCongr_cartier p y x M.ffAlgEquiv.symm
    (V.schemeRegularEquiv ω))

/-- Rational differentials underlying the two sides of the comparison. -/
theorem schemeRegularEquiv_globalCartier_coe (ω : V.GlobalForms) :
    letI := M.functionFieldAlgebra
    letI : IsCurveOver K M.C.functionField :=
      isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
        M.toBase (RingEquiv.refl _) (fun _ => rfl)
    ∀ (y : M.C.functionField)
      [FiniteDimensional (IntermediateField.adjoin K {y}) M.C.functionField],
      (V.schemeRegularEquiv (V.globalCartier p x ω) : Ω[M.C.functionField⁄K]) =
        cartier p y (V.schemeRegularEquiv ω : Ω[M.C.functionField⁄K]) := by
  letI := M.functionFieldAlgebra
  letI : IsCurveOver K M.C.functionField :=
    isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase (RingEquiv.refl _) (fun _ => rfl)
  intro y hy
  exact congrArg Subtype.val (V.schemeRegularEquiv_globalCartier p x ω y)

/-- The comparison directly on the generic restriction used in the residue
pairing. This relates the existing global operator to the actual rational
Cartier operator occurring in local residue adjointness. -/
theorem generic_restriction_globalCartier (ω : V.GlobalForms) :
    letI := M.functionFieldAlgebra
    letI : IsCurveOver K M.C.functionField :=
      isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
        M.toBase (RingEquiv.refl _) (fun _ => rfl)
    ∀ (y : M.C.functionField)
      [FiniteDimensional (IntermediateField.adjoin K {y}) M.C.functionField],
      kaehlerToFunctionField M.toBase V.cover.U0 (V.globalCartier p x ω).val.1 =
        cartier p y (kaehlerToFunctionField M.toBase V.cover.U0 ω.val.1) := by
  letI := M.functionFieldAlgebra
  letI : IsCurveOver K M.C.functionField :=
    isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase (RingEquiv.refl _) (fun _ => rfl)
  intro y hy
  simpa only [V.schemeRegularEquiv_generic_restriction] using
    V.schemeRegularEquiv_globalCartier_coe p x ω y

end SupersingularCurves.Geometry.DifferentialChart
