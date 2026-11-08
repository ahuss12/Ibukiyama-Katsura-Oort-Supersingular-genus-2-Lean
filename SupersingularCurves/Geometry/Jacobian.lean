/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.Superspecial
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Repartitions

/-!
# Jacobians and superspecial/supersingular curves

A Jacobian represents the functor of line bundles algebraically equivalent to
zero. Its group law is derived from tensor product in that functor, not supplied
as an unrelated group structure. Its dimension is the previously defined
function-field genus. The representation property quantifies over test schemes
and actual invertible sheaves; it is substantially stronger than a bijection of
K-points with divisor classes.

The curve predicates below are over algebraically closed fields. They existentially
quantify a point and a representing Jacobian, so no arbitrary chosen object is
silently called a Jacobian. Existence for the explicit IKO families and the
Cartier-to-Jacobian equivalences are further theorems, not part of the definitions.
-/

set_option autoImplicit false
noncomputable section
universe u v

namespace SupersingularCurves.Geometry
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicCurve NeronModelInfra GoodReductionJacobian

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]

/-- A genuine representing Jacobian of a pointed smooth proper curve model. -/
structure Jacobian (M : CurveModel K F)
    (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase) where
  designation : RelativePic0Designation K M.toBase
  represents : RepresentsRelSubPic M.toBase s
    (algEquivZeroCut M.toBase s) designation
  [smooth : SmoothOfRelativeDimension (genusFF K F) designation.toBase]
  [proper : IsProper designation.toBase]
  [connected : GeometricallyConnected designation.toBase]

attribute [instance] Jacobian.smooth Jacobian.proper Jacobian.connected

namespace Jacobian
variable {M : CurveModel K F}
  {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase}

/-- The abelian variety with the group law induced by tensoring line bundles. -/
def abelianVariety (J : Jacobian M s) : AbelianVariety K (genusFF K F) where
  group := { X := Over.mk J.designation.toBase
             grp := J.represents.grpObj (P := algEquivZeroGroupCut M.toBase s) }
  comm := J.represents.isCommMonObj (P := algEquivZeroGroupCut M.toBase s)
  smooth := J.smooth
  proper := J.proper
  connected := J.connected

/-- Superspeciality of this Jacobian is the geometric isomorphism condition. -/
def IsSuperspecial (p : ℕ) [Fact p.Prime] [CharP K p] (J : Jacobian M s) : Prop :=
  J.abelianVariety.IsSuperspecial p

/-- Supersingularity of this Jacobian is the geometric isogeny condition. -/
def IsSupersingular (p : ℕ) [Fact p.Prime] [CharP K p] (J : Jacobian M s) : Prop :=
  J.abelianVariety.IsSupersingular p

theorem IsSuperspecial.isSupersingular {p : ℕ} [Fact p.Prime] [CharP K p]
    {J : Jacobian M s} (h : J.IsSuperspecial p) : J.IsSupersingular p :=
  AbelianVariety.IsSuperspecial.isSupersingular h

end Jacobian

namespace CurveModel

/-- A curve is superspecial if its Jacobian is geometrically a product of
supersingular elliptic curves. The base point exists in the algebraically closed
setting; it is included explicitly in the representation witness. -/
def IsSuperspecial (p : ℕ) [Fact p.Prime] [CharP K p] [IsAlgClosed K]
    (M : AlgebraicCurve.CurveModel K F) : Prop :=
  ∃ (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase)
    (J : Jacobian M s), J.IsSuperspecial p

/-- The corresponding isogeny condition on the Jacobian. -/
def IsSupersingular (p : ℕ) [Fact p.Prime] [CharP K p] [IsAlgClosed K]
    (M : AlgebraicCurve.CurveModel K F) : Prop :=
  ∃ (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase)
    (J : Jacobian M s), J.IsSupersingular p

theorem IsSuperspecial.isSupersingular {p : ℕ} [Fact p.Prime] [CharP K p]
    [IsAlgClosed K] {M : AlgebraicCurve.CurveModel K F}
    (h : IsSuperspecial p M) : IsSupersingular p M := by
  obtain ⟨s, J, hJ⟩ := h
  exact ⟨s, J, hJ.isSupersingular⟩

end CurveModel
end SupersingularCurves.Geometry
