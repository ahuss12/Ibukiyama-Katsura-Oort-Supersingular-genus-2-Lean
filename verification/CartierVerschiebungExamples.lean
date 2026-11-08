import SupersingularCurves.IKO.VerschiebungCriteria

/-!
Integration checks for the Cartier/Verschiebung comparison on actual curves.
The fields are inhabited algebraic closures of finite fields. The characteristic
three example checks that p-rank zero does not imply V-cotangent vanishing;
the IKO examples exercise both family constructions and their matrix equations.
No supersingular or superspecial classification hypothesis is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open AlgebraicGeometry AlgebraicCurve SupersingularCurves
open SupersingularCurves.Geometry SupersingularCurves.Geometry.InfinitesimalPicard
open SupersingularCurves.Hyperelliptic

namespace CartierVerschiebungExamples

section CharacteristicThree

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
private abbrev K := AlgebraicClosure (ZMod 3)
local instance : NeZero (2 : K) :=
  ⟨fun h => (show ¬ 3 ∣ 2 by decide) ((CharP.cast_eq_zero_iff K 3 2).mp h)⟩
private abbrev a := CharacteristicThree.model (K := K)
private abbrev J := a.jacobianRealization.jacobian
private def chart : DifferentialChart a.curveModel := differentialChart a.curveModel

example :
    J.abelianVariety.HasPRankOver 3 0 ∧ J.verschiebungCotangent 3 ≠ 0 :=
  CharacteristicThree.jacobian_pRank_zero_and_verschiebungCotangent_ne_zero

/-- The general matrix criterion specializes to this genuine smooth curve. -/
example : J.verschiebungCotangent 3 = 0 ↔
    IKO.coefficientMatrix 3 (Polynomial.X ^ 5 - 1 : Polynomial K) = 0 := by
  exact a.jacobian_verschiebungCotangent_zero_iff_matrix 3
    CharacteristicThree.quintic_separable
    (Or.inl CharacteristicThree.quintic_degree) (by decide) J

/-- The scalar untwist and cotangent/global-form comparison are fixed
independently, so this tests the full normalization rather than only zeros. -/
example (z : J.Cotangent) :
    J.cotangentGlobalEquiv chart
        (J.cotangentCohomologicalUntwist chart.cover 3 (J.verschiebungCotangent 3 z)) =
      chart.globalCartier 3 a.x (J.cotangentGlobalEquiv chart z) :=
  J.cotangentGlobalEquiv_verschiebung chart 3 a.x z

/-- Residue adjointness is checked on arbitrary actual Cech classes. -/
example (ω : chart.GlobalForms) (q : CechH1 a.curveModel.toBase chart.cover) :
    chart.globalDualRepartitionEquiv (chart.globalCartier 3 a.x ω)
        (SchemeCech.toRepartition a.curveModel.toBase chart.cover q) ^ 3 =
      chart.globalDualRepartitionEquiv ω
        (SchemeCech.toRepartition a.curveModel.toBase chart.cover
          (SchemeFrobenius.absoluteCech 3 a.curveModel.toBase chart.cover q)) :=
  chart.globalCartier_residue_adjoint 3 a.x ω q

example (z : J.Cotangent) :
    J.verschiebungCotangent 3 z = 0 ↔
      chart.globalCartier 3 a.x (J.cotangentGlobalEquiv chart z) = 0 :=
  J.verschiebungCotangent_apply_eq_zero_iff chart 3 a.x z

end CharacteristicThree

section FamilyACharacteristicFive

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev K5 := AlgebraicClosure (ZMod 5)
local instance : NeZero (2 : K5) :=
  ⟨fun h => (show ¬ 5 ∣ 2 by decide) ((CharP.cast_eq_zero_iff K5 5 2).mp h)⟩
private theorem three_ne_zero : (3 : K5) ≠ 0 :=
  fun h => (show ¬ 5 ∣ 3 by decide) ((CharP.cast_eq_zero_iff K5 5 3).mp h)
private theorem two_ne_one : (2 : K5) ≠ 1 := by
  intro h
  have hz : (1 : K5) = 0 := by linear_combination h
  exact one_ne_zero hz

/-- A concrete admissible family-A parameter over the algebraic closure of F5. -/
example :
    (IKO.familyAJacobian (2 : K5) three_ne_zero (NeZero.ne 2) two_ne_one).jacobian.verschiebungCotangent 5 = 0 ↔
      (IKO.gPolynomial 5).eval (2 : K5) = 0 :=
  IKO.familyAJacobian_verschiebungCotangent_zero_iff 5 (by decide)
    (2 : K5) three_ne_zero (NeZero.ne 2) two_ne_one

end FamilyACharacteristicFive

section FamilyBCharacteristicSeven

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private abbrev K7 := AlgebraicClosure (ZMod 7)
local instance : NeZero (2 : K7) :=
  ⟨fun h => (show ¬ 7 ∣ 2 by decide) ((CharP.cast_eq_zero_iff K7 7 2).mp h)⟩
private theorem two_ne_one7 : (2 : K7) ≠ 1 := by
  intro h
  have hz : (1 : K7) = 0 := by linear_combination h
  exact one_ne_zero hz

/-- A concrete admissible family-B parameter over the algebraic closure of F7. -/
example :
    (IKO.familyBJacobian (2 : K7) (NeZero.ne 2) two_ne_one7).jacobian.verschiebungCotangent 7 = 0 ↔
      (IKO.hPolynomial 7).eval (2 : K7) = 0 :=
  IKO.familyBJacobian_verschiebungCotangent_zero_iff 7 (by decide)
    (2 : K7) (NeZero.ne 2) two_ne_one7

end FamilyBCharacteristicSeven

end CartierVerschiebungExamples
