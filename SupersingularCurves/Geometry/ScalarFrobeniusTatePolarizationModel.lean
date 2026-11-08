/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentEquivariantModel
import SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentProjective

/-!
# Finite-field reconstruction retaining a prescribed symmetric bundle

Any supplied symmetric invertible bundle with a finite projective presentation
can be used for the Frobenius-fixed construction. The exponent is exactly p²,
independent of the variety and of the chosen bundle. This permits subsequent
bounded-polarization work to retain its own line bundle; it does not assert
that the line bundle or its projective presentation has descended.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SupersingularCurves.Geometry.AbelianVariety
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
open SchemeFrobenius PerfectFieldVerschiebung FrobeniusFiniteFieldDescent FrobeniusDescent

variable {K : Type u} [Field K] [IsAlgClosed K] {g : ℕ}
variable (A : AbelianVariety K g) (p : ℕ) [Fact p.Prime] [CharP K p]
local instance : Smooth A.group.X.hom :=
  SmoothOfRelativeDimension.smooth g A.group.X.hom

/-- The model is constructed from the p²-th power of the prescribed symmetric
bundle. Both the invariant bundle and the genuine equivariant model are retained. -/
theorem exists_equivariant_model_of_symmetric_finite_bundle
    (hV : GroupScheme.verschiebungCotangent p A.group A.groupScheme_law_commutative = 0)
    (L : A.group.X.left.Modules) (hL : Scheme.Modules.IsInvertible L)
    (hsym : Nonempty ((Scheme.Modules.pullback ((𝟙 A.group.X)⁻¹).left).obj L ≅ L))
    (hfinite : L.FiniteBySections A.group.X.hom) :
    ∃ (τ : A.group.X.left ≅ A.group.X.left)
      (eM : (Scheme.Modules.pullback τ.hom).obj (L.tensorPow (p ^ 2)) ≅ L.tensorPow (p ^ 2)),
      τ.hom ≫ A.group.X.hom = A.group.X.hom ≫ baseMap p K ≫ baseMap p K ∧
      (GroupScheme.law A.group).schemeNsmul p ≫ τ.hom =
        absolute p A.group.X.hom ≫ absolute p A.group.X.hom ∧
      Scheme.Modules.IsInvertible (L.tensorPow (p ^ 2)) ∧
      (L.tensorPow (p ^ 2)).FiniteBySections A.group.X.hom ∧
      (letI := sectionsModule (L.tensorPow (p ^ 2)) A.group.X.hom
       ∃ b : Module.Basis (Fin (Module.finrank K Γ(L.tensorPow (p ^ 2), ⊤))) K
         Γ(L.tensorPow (p ^ 2), ⊤), ∀ i, actionAddHom τ (L.tensorPow (p ^ 2)) eM (b i) = b i) ∧
      ∃ (X₀ : Scheme.{u}) (c₀ : X₀ ⟶ Spec (CommRingCat.of (fixedField K p 2)))
        (d : A.group.X.left ⟶ X₀),
        IsPullback d A.group.X.hom c₀
          (Spec.map (CommRingCat.ofHom (algebraMap (fixedField K p 2) K))) ∧
        τ.hom ≫ d = d := by
  obtain ⟨e, he, hover, ⟨hcompat⟩⟩ :=
    A.exists_frobenius_factor_iso_symmetric_bundle p L hL hsym hV
  let M := L.tensorPow (p ^ 2)
  let τ := schemeAutomorphism p A.group.X.hom e
  let eM := invariantBundleIso p A.group.X.hom e M hcompat
  have hτ := schemeAutomorphism_over p A.group.X.hom e hover
  have hdouble : doubleRelative p A.group.X.hom ≫ e.hom =
      (GroupScheme.law A.group).schemeNsmul p := by
    rw [doubleRelative, Category.assoc, he, frobenius_verschiebung]
  have hp := endomorphism_comp_schemeAutomorphism p A.group.X.hom e _ hdouble
  have hM : Scheme.Modules.IsInvertible M :=
    FrobeniusLineBundle.tensorPower_invertible hL (p ^ 2)
  have hf : M.FiniteBySections A.group.X.hom :=
    hfinite.tensorPow (pow_pos (Fact.out : p.Prime).pos 2)
  refine ⟨τ, eM, hτ, hp, hM, hf, ?_,
    exists_fixedField_equivariant_scheme_model p A.group.X.hom M hM hf τ eM hτ⟩
  exact exists_fixedSectionBasis M A.group.X.hom hM τ eM p hτ

end SupersingularCurves.Geometry.AbelianVariety
