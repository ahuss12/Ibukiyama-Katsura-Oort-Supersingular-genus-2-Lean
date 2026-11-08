import SupersingularCurves.Geometry.PointedCotangent
import Theorems.Thm_AlgebraicGeometry_smoothOfRelativeDimension_of_finrank_cotangentSpace_eq

/-!
# Dimension of the actual cotangent space at a rational smooth point

The maximal-ideal cotangent space at a rational point of a smooth scheme has
dimension equal to the relative dimension of its structure morphism.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.PointedCotangent

open CategoryTheory AlgebraicGeometry NeronModelInfra
open P2MW.S_AlgebraicGeometry_smoothOfRelativeDimension_of_finrank_cotangentSpace_eq
open P2MW.S_AlgebraicCurve_CurveModel_finrank_cotangentSpace_zeroSection_eq_genusFF_of_representsRelSubPic

variable {K : Type u} [Field K] {X : Scheme.{u}}
variable (c : X ⟶ Spec (CommRingCat.of K))
  (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)

/-- The dimension over the residue field, obtained from an actual standard-smooth
affine neighbourhood of the rational point. -/
theorem finrank_residueField_eq_relativeDimension (n : ℕ)
    [SmoothOfRelativeDimension n c] :
    Module.finrank (IsLocalRing.ResidueField (Stalk c s)) (Cotangent c s) = n := by
  set x : X := s.1.base (IsLocalRing.closedPoint K)
  obtain ⟨U, hU, V, hV, hxV, e, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := n) (f := c) x
  obtain rfl : U = ⊤ := by
    refine eq_top_iff.mpr fun p _ => ?_
    rw [Subsingleton.elim p (c.base x)]
    exact e hxV
  let R : Type u := Γ(Spec (CommRingCat.of K), ⊤)
  let A : Type u := Γ(X, V)
  let S : Type u := X.presheaf.stalk x
  let φ : R →+* A := (c.appLE ⊤ V e).hom
  let : Algebra R A := φ.toAlgebra
  let : Algebra A S := X.presheaf.algebra_section_stalk (⟨x, hxV⟩ : V)
  let : Algebra R S := ((algebraMap A S).comp φ).toAlgebra
  have : IsScalarTower R A S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsLocalization.AtPrime S (hV.primeIdealOf ⟨x, hxV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨x, hxV⟩
  have : Algebra.IsStandardSmoothOfRelativeDimension n R A := hstd
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have : Nontrivial A := inferInstance
  have hcomp : algebraMap R (IsLocalRing.ResidueField S) =
      (c.residueFieldMap x).hom.comp
        ((Spec (CommRingCat.of K)).evaluation ⊤ (c.base x) trivial).hom := by
    have h₁ : algebraMap R (IsLocalRing.ResidueField S) =
        (c.appLE ⊤ V e ≫ X.presheaf.germ V x hxV ≫ X.residue x).hom := by
      rw [IsScalarTower.algebraMap_eq R S (IsLocalRing.ResidueField S),
        IsLocalRing.ResidueField.algebraMap_eq]
      rfl
    rw [h₁, ← CommRingCat.hom_comp, Scheme.evaluation_naturality c x (V := ⊤) trivial]
    congr 1
    simp only [Scheme.Hom.appLE, Category.assoc]
    rw [TopCat.Presheaf.germ_res_assoc]
    rfl
  have hres : Function.Bijective (algebraMap R (IsLocalRing.ResidueField S)) := by
    constructor
    · let ιK := Scheme.ΓSpecIso (CommRingCat.of K)
      have hfac : algebraMap R (IsLocalRing.ResidueField S) =
          ((algebraMap R (IsLocalRing.ResidueField S)).comp ιK.inv.hom).comp
            ιK.hom.hom := by
        ext r
        simp only [RingHom.coe_comp, Function.comp_apply]
        rw [← CommRingCat.comp_apply, Iso.hom_inv_id]
        rfl
      rw [hfac]
      exact (RingHom.injective
        ((algebraMap R (IsLocalRing.ResidueField S)).comp ιK.inv.hom)).comp
        ιK.commRingCatIsoToRingEquiv.injective
    · rw [hcomp]
      exact (P2mRelDim.surjective_residueFieldMap_of_section c s.1 s.2 _).comp
        (P2mRelDim.surjective_evaluation_top_Spec_field K (c.base x))
  exact P2mRelDim.finrank_cotangentSpace_eq_of_isLocalization
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl n hres

/-- At a rational point the base field is the residue field, so the actual
cotangent space has the prescribed relative dimension over the base field. -/
theorem finrank_eq_relativeDimension (n : ℕ) [SmoothOfRelativeDimension n c] :
    Module.finrank K (Cotangent c s) = n := by
  have hK := P2mTJ.bijective_algebraMap_residueField c s.1 s.2
  have hdim := finrank_residueField_eq_relativeDimension c s n
  rw [P2mTJ.finrank_cotangentSpace_residueField_eq hK] at hdim
  exact hdim

end SupersingularCurves.Geometry.PointedCotangent
