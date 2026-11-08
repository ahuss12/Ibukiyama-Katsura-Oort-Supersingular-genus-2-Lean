import SupersingularCurves.Hyperelliptic.GenusTwoSupersingular
import SupersingularCurves.IKO.SupersingularObstructions

/-!
A concrete geometric exclusion: family B at parameter 2 in characteristic 3
has no representing Jacobian geometrically isogenous to a product of
supersingular elliptic curves. This exercises the actual curve predicate,
the isogeny/p-rank bridge and the previously proved polynomial calculation.
-/

set_option autoImplicit false
noncomputable section

open SupersingularCurves.IKO

namespace SupersingularGeometryExamples

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
private abbrev K := AlgebraicClosure (ZMod 3)
local instance : NeZero (2 : K) :=
  ⟨fun h => (show ¬ 3 ∣ 2 by decide) ((CharP.cast_eq_zero_iff K 3 2).mp h)⟩

private theorem two_ne_one : (2 : K) ≠ 1 := by
  intro h
  have h1 : (1 : K) = 0 := by linear_combination h
  exact one_ne_zero h1

example : ¬ SupersingularCurves.Geometry.CurveModel.IsSupersingular 3
    (familyBCurve (2 : K) (NeZero.ne _) two_ne_one) :=
  familyB_not_isSupersingular_char_three (2 : K) (NeZero.ne _) two_ne_one

end SupersingularGeometryExamples
