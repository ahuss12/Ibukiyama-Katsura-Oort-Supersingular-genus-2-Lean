/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.JacobianVerschiebungSquare
import SupersingularCurves.Hyperelliptic.GenusTwoGlobalForms
import SupersingularCurves.Geometry.GlobalCartierModels

/-!
# Square-zero Cartier and the actual successive Verschiebung differentials

The source and both Frobenius twists are actual schemes. The coefficient
criterion reaches their actual local-ring cotangent differentials through
the full global-form space, residue duality and the two Picard comparisons.
-/
set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.Hyperelliptic.SimpleRootModel
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open NeronModelInfra SupersingularCurves.Geometry SupersingularCurves.IKO

variable {K : Type*} [Field K] [IsAlgClosed K] [NeZero (2 : K)]
  (a : SimpleRootModel K) (p : ℕ) [Fact p.Prime] [CharP K p]
  {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) a.curveModel.toBase}
  (J : Jacobian a.curveModel s)

/-- Full global Cartier squared zero kills the actual two successive
Verschiebung cotangent maps. -/
theorem jacobian_verschiebungCotangent_twice_eq_zero_of_globalCartier
    (hC2 : ∀ ω : a.GlobalForms, a.globalCartier p (a.globalCartier p ω) = 0) :
    J.twistedVerschiebungCotangent p ∘ₗ J.verschiebungCotangent p = 0 :=
  J.verschiebungCotangent_twice_eq_zero_of_globalCartier_square_zero p
    (differentialChart a.curveModel) a.x hC2

/-- The twisted matrix-square criterion kills the actual successive
Verschiebung cotangent maps for every represented separable quintic or sextic. -/
theorem jacobian_verschiebungCotangent_twice_eq_zero_of_matrix
    (hf : a.f.Separable) (hd : a.f.natDegree = 5 ∨ a.f.natDegree = 6)
    (hp : p % 2 = 1)
    (hC2 : (coefficientMatrix p a.f).map (fun c => c ^ p) * coefficientMatrix p a.f = 0) :
    J.twistedVerschiebungCotangent p ∘ₗ J.verschiebungCotangent p = 0 :=
  a.jacobian_verschiebungCotangent_twice_eq_zero_of_globalCartier p J
    ((a.all_globalCartier_square_zero_iff hf hd p hp).mpr hC2)

end SupersingularCurves.Hyperelliptic.SimpleRootModel
