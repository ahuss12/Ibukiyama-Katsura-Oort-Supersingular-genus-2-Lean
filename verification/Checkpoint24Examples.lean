import SupersingularCurves.Hyperelliptic.FifthPowerGeometricObstructions

/-!
Concrete integration checks for genuine geometric non-superspeciality and
scheme-theoretic Frobenius, Verschiebung and multiplication degrees on an
actual genus-two Jacobian. The characteristic-three curve has p-rank zero,
but its nonzero Cartier operator now rules out a genuine product isomorphism.
-/
set_option autoImplicit false
noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open SupersingularCurves.Geometry SupersingularCurves.Hyperelliptic

namespace Checkpoint24Examples

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : NeZero (2 : AlgebraicClosure (ZMod 3)) :=
  ⟨fun h => (show ¬ 3 ∣ 2 by decide) ((CharP.cast_eq_zero_iff _ 3 2).mp h)⟩
local instance : NeZero (2 : AlgebraicClosure (ZMod 7)) :=
  ⟨fun h => (show ¬ 7 ∣ 2 by decide) ((CharP.cast_eq_zero_iff _ 7 2).mp h)⟩

private abbrev K := AlgebraicClosure (ZMod 3)
private abbrev M := FifthPowerClassification.model (K := K) 3 (by decide)
private abbrev J := M.jacobianRealization.jacobian
private abbrev A := J.abelianVariety

example : ¬ CurveModel.IsSuperspecial 3 M.curveModel :=
  FifthPowerClassification.not_isSuperspecial_of_mod_three 3
    (by decide) (by decide) (by decide)

example : ¬ CurveModel.IsSuperspecial 7
    (FifthPowerClassification.model (K := AlgebraicClosure (ZMod 7)) 7
      (by decide)).curveModel :=
  FifthPowerClassification.not_isSuperspecial_of_mod_two 7
    (by decide) (by decide) (by decide)

example : (∀ ω : M.GlobalForms, M.globalCartier 3 (M.globalCartier 3 ω) = 0) ∧
    ¬ CurveModel.IsSuperspecial 3 M.curveModel := by
  constructor
  · exact (FifthPowerClassification.global_cartier_square_zero_iff 3
      (by decide) (by decide)).mpr (by decide)
  · exact FifthPowerClassification.not_isSuperspecial_of_mod_three 3
      (by decide) (by decide) (by decide)

example (y : SchemeFrobenius.Twist 3 A.group.X.hom) :
    (SchemeFrobenius.relative 3 A.group.X.hom).finrank y = 9 := by
  rw [A.relativeFrobenius_finrank 3]
  rw [FifthPowerClassification.genus_eq_two 3 (by decide)]
  norm_num

example (y : A.group.X.left) :
    (PerfectFieldVerschiebung.verschiebung 3 A.group.X.hom
      (GroupScheme.law A.group) A.groupScheme_law_commutative).finrank y = 9 := by
  rw [A.verschiebung_finrank 3]
  rw [FifthPowerClassification.genus_eq_two 3 (by decide)]
  norm_num

example (y : A.group.X.left) :
    ((GroupScheme.law A.group).schemeNsmul 3).finrank y = 81 := by
  rw [(A.multiplication_finite_flat_degree 3 (by decide)).2.2.2.2.2 y]
  rw [FifthPowerClassification.genus_eq_two 3 (by decide)]
  norm_num

end Checkpoint24Examples
