/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusFiniteFieldProjectiveImage
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_projPresentation_toProj_eq_and_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_nonempty_iso_of_toProj_eq

/-! # Descent retaining the actual prescribed very ample line bundle -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SupersingularCurves.Geometry.FrobeniusFiniteFieldDescent
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial FrobeniusDescent
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] [IsAlgClosed K]
  (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)
  {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of K))
  (M : X.Modules) {N : ℕ} (P : M.ProjPresentation c N)

/-- An equivariant actual closed presentation produces a finite-field model
with an invertible very ample line whose pullback is the prescribed line M. -/
theorem exists_fixedField_polarized_model [IsClosedImmersion P.toProj]
    (τ : X ⟶ X)
    (hτ : τ ≫ P.toProj = P.toProj ≫ coefficientMap (iterateFrobenius K p s) N)
    (hs : s ≠ 0) :
    ∃ (X₀ : Scheme.{0}) (c₀ : X₀ ⟶ Spec (CommRingCat.of (fixedField K p s)))
      (M₀ : X₀.Modules) (P₀ : M₀.ProjPresentation c₀ N) (d : X ⟶ X₀),
      Scheme.Modules.IsInvertible M₀ ∧ IsClosedImmersion P₀.toProj ∧
      d ≫ P₀.toProj = P.toProj ≫ ProjSpace.map (fixedField K p s) K N ∧
      IsPullback d c c₀ (Spec.map (CommRingCat.ofHom (algebraMap (fixedField K p s) K))) ∧
      Nonempty ((Scheme.Modules.pullback d).obj M₀ ≅ M) ∧ τ ≫ d = d := by
  let k := fixedField K p s
  obtain ⟨X₀, ι₀, d, hι₀, hdι, hd, hτd⟩ :=
    exists_fixedField_closed_projective_model p s P.toProj τ hτ hs
  obtain ⟨M₀, P₀, hP₀, hM₀⟩ := ProjSpace.exists_projPresentation_toProj_eq_and_locallyTrivial ι₀
  let c₀ := ι₀ ≫ ProjSpace.π k N
  have hpb : IsPullback d c c₀
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
    simpa only [P.toProj_π] using hd
  refine ⟨X₀, c₀, M₀, P₀, d, ⟨hM₀⟩, hP₀ ▸ hι₀, ?_, hpb, ?_, hτd⟩
  · simpa only [hP₀] using hdι
  obtain ⟨Q, _, hQ⟩ := P₀.exists_projPresentation_pullback_sigma_eq_toProj_eq d
  obtain ⟨P', _, hP'⟩ := P.exists_sigma_eq_toProj_eq_comp_map_of_algebraMap (R := k)
  let Q' : ((Scheme.Modules.pullback d).obj M₀).ProjPresentation
      (c ≫ Spec.map (CommRingCat.ofHom (algebraMap k K))) N :=
    { Q with toProj_π := Q.toProj_π.trans hpb.w }
  apply Q'.nonempty_iso_of_toProj_eq P'
  exact (hQ.trans (by rw [hP₀]; exact hdι)).trans hP'.symm

end SupersingularCurves.Geometry.FrobeniusFiniteFieldDescent
