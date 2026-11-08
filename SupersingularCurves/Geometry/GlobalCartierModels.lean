/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.GlobalCartier
import SupersingularCurves.Hyperelliptic.GenusTwoGlobalForms
import SupersingularCurves.IKO.GlobalForms

/-!
# Compatibility with the previously computed global Cartier operators

The generic operator is definitionally the one already used for all smooth
hyperelliptic genus-two models and the two IKO families. Thus results about the
generic operator apply to the existing matrices without redefining Cartier.
-/
set_option autoImplicit false
noncomputable section

namespace SupersingularCurves
open Geometry AlgebraicCurve
variable {K : Type*} [Field K] [IsAlgClosed K] [NeZero (2 : K)]
  (p : ℕ) [Fact p.Prime] [CharP K p]

namespace Hyperelliptic.SimpleRootModel

theorem chart_globalCartier_eq (a : SimpleRootModel K) (ω : a.GlobalForms) :
    (differentialChart a.curveModel).globalCartier p a.x ω = a.globalCartier p ω := rfl

end Hyperelliptic.SimpleRootModel

namespace IKO

theorem familyA_chart_globalCartier_eq (t : K) (h3 : (3 : K) ≠ 0)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (ω : familyAGlobalForms t h3 ht0 ht1) :
    (differentialChart (familyACurve t h3 ht0 ht1)).globalCartier p
      (familyAModel t h3 ht1).x ω = familyAGlobalCartier p t h3 ht0 ht1 ω := rfl

theorem familyB_chart_globalCartier_eq (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (ω : familyBGlobalForms t ht0 ht1) :
    (differentialChart (familyBCurve t ht0 ht1)).globalCartier p
      (familyBModel t ht0).x ω = familyBGlobalCartier p t ht0 ht1 ω := rfl

end IKO
end SupersingularCurves
