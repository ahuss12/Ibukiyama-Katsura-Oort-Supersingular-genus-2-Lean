import SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentScheme
import SupersingularCurves.Hyperelliptic.GenusTwoQuotientVanishing
import SupersingularCurves.Hyperelliptic.FifthPowerClassification

/-!
Actual-curve integration checks for the genuine finite-field scheme model.
In characteristic 19 the Jacobian of y²=x⁵−1 itself has the model; in
characteristic 3 the constructed isogenous zero-dV surface has it.
These descend the underlying schemes, not their group laws or elliptic products.
-/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open SupersingularCurves.Geometry.FrobeniusDescent
open SupersingularCurves.Geometry SupersingularCurves.Hyperelliptic

namespace Checkpoint27Examples
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 19) := ⟨by decide⟩
local instance : NeZero (2 : AlgebraicClosure (ZMod 3)) :=
  ⟨fun h => (show ¬ 3 ∣ 2 by decide) ((CharP.cast_eq_zero_iff _ 3 2).mp h)⟩
local instance : NeZero (2 : AlgebraicClosure (ZMod 19)) :=
  ⟨fun h => (show ¬ 19 ∣ 2 by decide) ((CharP.cast_eq_zero_iff _ 19 2).mp h)⟩

private def HasFiniteFieldModel {K : Type} [Field K] {g : ℕ}
    (A : AbelianVariety K g) (p : ℕ) [Fact p.Prime] [CharP K p] : Prop :=
  Finite (fixedField K p 2) ∧ Nat.card (fixedField K p 2) = p ^ 2 ∧
    ∃ (X₀ : Scheme) (c₀ : X₀ ⟶ Spec (CommRingCat.of (fixedField K p 2)))
      (d : A.group.X.left ⟶ X₀),
      IsPullback d A.group.X.hom c₀
        (Spec.map (CommRingCat.ofHom (algebraMap (fixedField K p 2) K)))

private theorem hasFiniteFieldModel_of_zeroV {K : Type} [Field K] [IsAlgClosed K]
    {g : ℕ} (A : AbelianVariety K g) (p : ℕ) [Fact p.Prime] [CharP K p]
    (hV : GroupScheme.verschiebungCotangent p A.group A.groupScheme_law_commutative = 0) :
    HasFiniteFieldModel A p :=
  A.exists_finiteField_scheme_model_of_verschiebungCotangent_eq_zero p hV

private abbrev K3 := AlgebraicClosure (ZMod 3)
private abbrev M3 := FifthPowerClassification.model (K := K3) 3 (by decide)
private abbrev J3 := M3.jacobianRealization.jacobian
private abbrev M19 := FifthPowerClassification.model
  (K := AlgebraicClosure (ZMod 19)) 19 (by decide)
private abbrev J19 := M19.jacobianRealization.jacobian

example : HasFiniteFieldModel J19.abelianVariety 19 := by
  apply hasFiniteFieldModel_of_zeroV J19.abelianVariety 19
  exact (J19.groupScheme_verschiebungCotangent_eq_zero_iff 19).mpr
    ((J19.verschiebungCotangent_eq_zero_iff_forall
      (differentialChart M19.curveModel) 19 M19.x).mpr
      ((FifthPowerClassification.global_cartier_zero_iff 19
        (by decide) (by decide)).mpr (by decide)))

example : ∃ (B : AbelianVariety K3 (genusFF K3 M3.FunctionField))
    (f : J3.abelianVariety.group ⟶ B.group), IsIsogeny f ∧
      GroupScheme.verschiebungCotangent 3 B.group B.groupScheme_law_commutative = 0 ∧
      HasFiniteFieldModel B 3 := by
  have hC : ∀ ω : M3.GlobalForms, M3.globalCartier 3 (M3.globalCartier 3 ω) = 0 :=
    (FifthPowerClassification.global_cartier_square_zero_iff 3
      (by decide) (by decide)).mpr (by decide)
  obtain ⟨B, f, hf, hV⟩ :=
    M3.jacobian_exists_isogeny_to_zero_verschiebungCotangent_of_globalCartier 3
      (FifthPowerClassification.quintic_separable 3 (by decide))
      (Or.inl FifthPowerClassification.quintic_degree) (by decide) J3 hC
  exact ⟨B, f, hf, hV, hasFiniteFieldModel_of_zeroV B 3 hV⟩
end Checkpoint27Examples
