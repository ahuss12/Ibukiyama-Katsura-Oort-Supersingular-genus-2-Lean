import SupersingularCurves.Geometry.FrobeniusCechComparison
import SupersingularCurves.Hyperelliptic.CharacteristicThree

/- Integration on the genuine genus-two curve y² = x⁵ - 1 over F₃-bar.
These instantiate the actual Frobenius cochain map and its comparison with
the independently constructed Jacobian Verschiebung, including a two-dimensional
coefficient module. They do not assume a Cartier/V comparison or a geometric
supersingular/superspecial classification theorem. -/

noncomputable section
open AlgebraicGeometry AlgebraicCurve SupersingularCurves.Geometry
open SupersingularCurves.Geometry.InfinitesimalPicard
open SupersingularCurves.Hyperelliptic

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
private abbrev K := AlgebraicClosure (ZMod 3)
local instance : NeZero (2 : K) :=
  ⟨fun h => (show ¬ 3 ∣ 2 by decide) ((CharP.cast_eq_zero_iff K 3 2).mp h)⟩
private abbrev a := CharacteristicThree.model (K := K)
private abbrev J := a.jacobianRealization.jacobian
private def chart : DifferentialChart a.curveModel := differentialChart a.curveModel

example : Nonempty
    (CechH1 (SchemeFrobenius.toBase 3 a.curveModel.toBase)
      (SchemeFrobenius.twistedCover 3 a.curveModel.toBase chart.cover) →ₗ[K]
        CechH1 a.curveModel.toBase chart.cover) :=
  ⟨SchemeFrobenius.cechPullback 3 a.curveModel.toBase chart.cover⟩

example (z : (chart.cover.structureSheafSections a.curveModel.toBase).M01) :
    SchemeFrobenius.cechPullback 3 a.curveModel.toBase chart.cover
      (Submodule.Quotient.mk
        (((SchemeFrobenius.projection 3 a.curveModel.toBase).app
          (chart.cover.U0 ⊓ chart.cover.U1)).hom z)) =
      Submodule.Quotient.mk
        (z ^ 3 : (chart.cover.structureSheafSections a.curveModel.toBase).M01) :=
  SchemeFrobenius.cechPullback_projection_mk 3 a.curveModel.toBase chart.cover z

example (l : Module.Dual K (J.TwistedCotangent 3)) :
    J.tangentCechEquiv chart.cover (l ∘ₗ J.verschiebungCotangent 3) =
      SchemeFrobenius.cechPullback 3 a.curveModel.toBase chart.cover
        (J.twistedTangentCechEquiv chart.cover 3 l) :=
  J.tangentCechEquiv_verschiebung_cochain chart.cover 3 l

example (x : J.Cotangent)
    (q : CechH1 (SchemeFrobenius.toBase 3 a.curveModel.toBase)
      (SchemeFrobenius.twistedCover 3 a.curveModel.toBase chart.cover)) :
    J.cotangentDualCechEquiv chart.cover x
        (SchemeFrobenius.cechPullback 3 a.curveModel.toBase chart.cover q) =
      J.twistedCotangentDualCechEquiv chart.cover 3 (J.verschiebungCotangent 3 x) q :=
  J.cotangentDualCechEquiv_frobenius_cochain chart.cover 3 x q

example (l : J.TwistedCotangent 3 →ₗ[K] K × K) :
    PicardCohomology.cotangentCechLinearEquiv J.represents chart.cover (K × K)
        (l ∘ₗ J.verschiebungCotangent 3) =
      (SchemeFrobenius.cechPullback 3 a.curveModel.toBase chart.cover).rTensor (K × K)
        (PicardCohomology.cotangentCechLinearEquiv (J.twistedPicardRepresentation 3)
          (SchemeFrobenius.twistedCover 3 a.curveModel.toBase chart.cover) (K × K) l) :=
  J.verschiebungCotangent_cochain chart.cover 3 l
