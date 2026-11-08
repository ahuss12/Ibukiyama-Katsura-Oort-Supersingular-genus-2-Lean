import SupersingularCurves.Geometry.JacobianResidue
import SupersingularCurves.Hyperelliptic.CharacteristicThree

/- Integration on the genuine genus-two curve y² = x⁵ - 1 over F₃-bar.
The actual local cotangent space is compared with actual global sheaf forms;
the residue normalization and independent-V deformation evaluation are
instantiated without additional residue-theorem or duality assumptions. -/

noncomputable section
open AlgebraicGeometry AlgebraicCurve SupersingularCurves.Geometry
open SupersingularCurves.Hyperelliptic

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
private abbrev K := AlgebraicClosure (ZMod 3)
local instance : NeZero (2 : K) :=
  ⟨fun h => (show ¬ 3 ∣ 2 by decide) ((CharP.cast_eq_zero_iff K 3 2).mp h)⟩
private abbrev a := CharacteristicThree.model (K := K)
private abbrev J := a.jacobianRealization.jacobian
private def V : DifferentialChart a.curveModel := differentialChart a.curveModel

example : Nonempty (J.Cotangent ≃ₗ[K] V.GlobalForms) :=
  ⟨J.cotangentGlobalEquiv V⟩

example : Module.finrank K V.GlobalForms = 2 := by
  rw [← (J.cotangentGlobalEquiv V).finrank_eq]
  rw [J.finrank_cotangent ⟨a.x, a.transcendental_x, a.finiteDimensional_coordinate⟩]
  exact CharacteristicThree.genus_eq_two

example (x : J.Cotangent) :
    letI := a.curveModel.functionFieldAlgebra
    ∀ r : ↥(repartitions K a.curveModel.C.functionField),
    SchemeResidue.residueSum a.curveModel.toBase
        (kaehlerToFunctionField a.curveModel.toBase V.cover.U0
          (J.cotangentGlobalEquiv V x).val.1) r =
      J.cotangentDualRepartitionEquiv V.cover x (Submodule.Quotient.mk r) :=
  J.cotangentGlobalEquiv_residue_mk V x

example (x : J.Cotangent) (l : Module.Dual K (J.TwistedCotangent 3)) :
    V.globalDualRepartitionEquiv (J.cotangentGlobalEquiv V x)
        (J.frobeniusRepartitionClass V.cover 3 l) =
      l (J.verschiebungCotangent 3 x) :=
  J.cotangentGlobalEquiv_frobeniusDeformation V 3 x l
