import SupersingularCurves.Geometry.FrobeniusPicardCohomology
import SupersingularCurves.Hyperelliptic.CharacteristicThree

/- Integration on the existing genuine genus-two model in characteristic
three. These examples check the new local-ring/cohomology interfaces against
the independently constructed curve and Jacobian, retaining the actual twist.
No Cartier/V identification or geometric classification is assumed. -/

noncomputable section
open AlgebraicCurve SupersingularCurves.Geometry
open SupersingularCurves.Geometry.InfinitesimalPicard
open SupersingularCurves.Hyperelliptic
open scoped TensorProduct
open P2MW.S_AlgebraicCurve_CurveModel_finrank_cotangentSpace_zeroSection_eq_genusFF_of_representsRelSubPic

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
private abbrev K := AlgebraicClosure (ZMod 3)
local instance : NeZero (2 : K) :=
  ⟨fun h => (show ¬ 3 ∣ 2 by decide) ((CharP.cast_eq_zero_iff K 3 2).mp h)⟩
private abbrev a := CharacteristicThree.model (K := K)
private abbrev J := a.jacobianRealization.jacobian
private def cover : a.curveModel.C.TwoAffineOpenCover :=
  Classical.choice (P2mTJ.nonempty_twoAffineOpenCover a.curveModel)

example : Module.finrank K (CechH1 a.curveModel.toBase cover) = 2 := by
  rw [← (J.tangentCechEquiv cover).finrank_eq, Subspace.dual_finrank_eq]
  rw [J.finrank_cotangent ⟨a.x, a.transcendental_x, a.finiteDimensional_coordinate⟩]
  exact CharacteristicThree.genus_eq_two

example : Nonempty (J.TwistedCotangent 3 ≃ₗ[K]
    Module.Dual K (CechH1 (SchemeFrobenius.toBase 3 a.curveModel.toBase)
      (SchemeFrobenius.twistedCover 3 a.curveModel.toBase cover))) :=
  ⟨J.twistedCotangentDualCechEquiv cover 3⟩

example (l : J.TwistedCotangent 3 →ₗ[K] K × K) :
    PicardCohomology.cotangentCechLinearEquiv J.represents cover (K × K)
        (l ∘ₗ J.verschiebungCotangent 3) =
      deformationCechEquiv a.curveModel.toBase a.curveModelBasepoint cover (K × K)
        (deformationClass a.curveModel.toBase a.curveModelBasepoint (K × K)
          (J.frobeniusPoincareDeformation 3 l)) :=
  J.verschiebungCotangent_cech cover 3 l
