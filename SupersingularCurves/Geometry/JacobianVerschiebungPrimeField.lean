/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.VerschiebungPrimeField
import SupersingularCurves.Geometry.JacobianCotangent

/-!
# Independently constructed Jacobian Verschiebung over the prime field

The scheme morphism is obtained by effective descent of multiplication by p
for the independently representing Jacobian and its tensor-product group law.
Its infinitesimal and cotangent actions are then constructed from that actual
morphism. No curve Cartier operator appears in the construction.

This module does not yet identify this action with Cartier, and does not
extend the construction to arbitrary perfect ground fields.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe v

namespace SupersingularCurves.Geometry.Jacobian
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicCurve NeronModelInfra GoodReductionJacobian InfinitesimalPicard

variable (p : ℕ) [Fact p.Prime]
variable {F : Type v} [Field F] [Algebra (ZMod p) F]
variable {M : CurveModel (ZMod p) F}
  {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ZMod p)))) M.toBase}
variable (J : Jacobian M s)

local instance smoothPrimeJacobian : Smooth J.designation.toBase :=
  SmoothOfRelativeDimension.smooth (genusFF (ZMod p) F) J.designation.toBase

/-- The tensor-product group law from the actual Picard representation. -/
abbrev primeFieldLaw : RelativeGroupLaw (ZMod p) J.designation.toBase :=
  J.represents.relativeGroupLaw (P := algEquivZeroGroupCut M.toBase s)

/-- The actual scheme Verschiebung over the prime field, constructed by descent. -/
def primeVerschiebung : J.designation.P ⟶ J.designation.P :=
  PrimeFieldVerschiebung.verschiebung p J.designation.toBase (J.primeFieldLaw p)
    (J.represents.relativeGroupLaw_isCommutative (P := algEquivZeroGroupCut M.toBase s))

theorem primeFrobenius_verschiebung :
    SchemeFrobenius.absolute p J.designation.toBase ≫ J.primeVerschiebung p =
      (J.primeFieldLaw p).schemeNsmul p :=
  PrimeFieldVerschiebung.frobenius_verschiebung p J.designation.toBase (J.primeFieldLaw p)
    (J.represents.relativeGroupLaw_isCommutative (P := algEquivZeroGroupCut M.toBase s))

theorem primeVerschiebung_frobenius :
    J.primeVerschiebung p ≫ SchemeFrobenius.absolute p J.designation.toBase =
      (J.primeFieldLaw p).schemeNsmul p :=
  PrimeFieldVerschiebung.verschiebung_frobenius p J.designation.toBase (J.primeFieldLaw p)
    (J.represents.relativeGroupLaw_isCommutative (P := algEquivZeroGroupCut M.toBase s))

theorem primeVerschiebung_over :
    J.primeVerschiebung p ≫ J.designation.toBase = J.designation.toBase :=
  PrimeFieldVerschiebung.verschiebung_over p J.designation.toBase (J.primeFieldLaw p)
    (J.represents.relativeGroupLaw_isCommutative (P := algEquivZeroGroupCut M.toBase s))

theorem primeVerschiebung_zero :
    J.designation.zeroSection ≫ J.primeVerschiebung p = J.designation.zeroSection := by
  have h := PrimeFieldVerschiebung.verschiebung_zero p J.designation.toBase
    (J.primeFieldLaw p)
    (J.represents.relativeGroupLaw_isCommutative (P := algEquivZeroGroupCut M.toBase s))
  change ((J.represents.relativeGroupLaw (P := algEquivZeroGroupCut M.toBase s)).one
      (𝟙 (Spec (CommRingCat.of (ZMod p))))).1 ≫ J.primeVerschiebung p =
    ((J.represents.relativeGroupLaw (P := algEquivZeroGroupCut M.toBase s)).one
      (𝟙 (Spec (CommRingCat.of (ZMod p))))).1 at h
  rw [J.represents.relativeGroupLaw_one (P := algEquivZeroGroupCut M.toBase s)] at h
  exact h

variable {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  [Module (ZMod p)ᵐᵒᵖ V] [IsCentralScalar (ZMod p) V]
variable {W : Type} [AddCommGroup W] [Module (ZMod p) W]
  [Module (ZMod p)ᵐᵒᵖ W] [IsCentralScalar (ZMod p) W]

/-- The action of the independently constructed V on actual infinitesimal points. -/
def primeVerschiebungPoint (t : J.InfinitesimalPoints V) : J.InfinitesimalPoints V :=
  ⟨t.1 ≫ J.primeVerschiebung p,
    by rw [Category.assoc, J.primeVerschiebung_over, t.2.1],
    by rw [← Category.assoc, t.2.2, J.primeVerschiebung_zero]⟩

theorem primeVerschiebungPoint_map (φ : V →ₗ[ZMod p] W) (t : J.InfinitesimalPoints V) :
    J.primeVerschiebungPoint p (t.map φ) = (J.primeVerschiebungPoint p t).map φ := by
  apply TangentPoints.ext
  exact Category.assoc _ _ _

local instance cotangentOppositeModulePrime : Module (ZMod p)ᵐᵒᵖ J.Cotangent :=
  Module.compHom _ (RingEquiv.toOpposite (ZMod p)).symm.toRingHom

local instance cotangentCentralScalarPrime : IsCentralScalar (ZMod p) J.Cotangent :=
  ⟨fun _ _ => rfl⟩

/-- The true cotangent action of the descended V; it is not defined using Cartier. -/
def primeVerschiebungCotangent : J.Cotangent →ₗ[ZMod p] J.Cotangent :=
  (J.cotangentPointsEquiv J.Cotangent).symm
    (J.primeVerschiebungPoint p
      (J.cotangentPointsEquiv J.Cotangent LinearMap.id))

/-- The cotangent action agrees with the scheme morphism on every square-zero test. -/
theorem primeVerschiebungCotangent_action (l : J.Cotangent →ₗ[ZMod p] V) :
    J.cotangentPointsEquiv V (l ∘ₗ J.primeVerschiebungCotangent p) =
      J.primeVerschiebungPoint p (J.cotangentPointsEquiv V l) := by
  rw [J.cotangentPointsEquiv_map]
  change ((J.cotangentPointsEquiv J.Cotangent)
    ((J.cotangentPointsEquiv J.Cotangent).symm _)).map l = _
  rw [Equiv.apply_symm_apply, ← J.primeVerschiebungPoint_map,
    ← J.cotangentPointsEquiv_map, LinearMap.comp_id]

end SupersingularCurves.Geometry.Jacobian
