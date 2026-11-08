import SupersingularCurves.Geometry.JacobianRepartition
import SupersingularCurves.Hyperelliptic.CharacteristicThree

/- Integration with the actual genus-two curve y² = x⁵ - 1 over F₃-bar.
The new repartition quotient has dimension two, and the independently
constructed V satisfies the deformation evaluation formula on this curve.
No Cartier/V identity or supersingular classification is assumed. -/

noncomputable section
open AlgebraicCurve SupersingularCurves.Geometry
open SupersingularCurves.Hyperelliptic
open P2MW.S_AlgebraicCurve_CurveModel_finrank_cotangentSpace_zeroSection_eq_genusFF_of_representsRelSubPic

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
private abbrev K := AlgebraicClosure (ZMod 3)
local instance : NeZero (2 : K) :=
  ⟨fun h => (show ¬ 3 ∣ 2 by decide) ((CharP.cast_eq_zero_iff K 3 2).mp h)⟩
private abbrev a := CharacteristicThree.model (K := K)
private abbrev J := a.jacobianRealization.jacobian
private def cover : a.curveModel.C.TwoAffineOpenCover :=
  Classical.choice (P2mTJ.nonempty_twoAffineOpenCover a.curveModel)

example :
    letI := a.curveModel.functionFieldAlgebra
    Module.finrank K (SchemeCech.RepartitionH1 a.curveModel.toBase) = 2 := by
  letI := a.curveModel.functionFieldAlgebra
  rw [← (J.tangentRepartitionEquiv cover).finrank_eq, Subspace.dual_finrank_eq]
  rw [J.finrank_cotangent ⟨a.x, a.transcendental_x, a.finiteDimensional_coordinate⟩]
  exact CharacteristicThree.genus_eq_two

example (x : J.Cotangent) (l : Module.Dual K (J.TwistedCotangent 3)) :
    J.cotangentDualRepartitionEquiv cover x (J.frobeniusRepartitionClass cover 3 l) =
      l (J.verschiebungCotangent 3 x) :=
  J.cotangentDualRepartitionEquiv_frobeniusDeformation cover 3 x l
