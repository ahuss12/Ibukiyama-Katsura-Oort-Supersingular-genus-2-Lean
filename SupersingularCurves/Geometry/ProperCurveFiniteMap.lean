/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import Theorems.Thm_AlgebraicGeometry_Scheme_finite_of_isClosed_of_ne_univ_of_forall_isClosed_singleton
import Theorems.Thm_AlgebraicGeometry_isClosed_singleton_or_isGenericPoint_and_exists_not_isGenericPoint_of_smoothOfRelativeDimension_one

/-! # Nonconstant maps from actual proper curves are finite

The hypothesis concerns the underlying morphism of schemes. No finite-kernel
or isogeny assumption is supplied.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SupersingularCurves.Geometry
open CategoryTheory AlgebraicGeometry

theorem isFinite_of_proper_curve_of_not_constant
    {K : Type u} [Field K] [IsAlgClosed K]
    {X Y : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of K))
    (d : Y ⟶ Spec (CommRingCat.of K))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    [IsSeparated d] (f : X ⟶ Y) (hf : f ≫ d = c)
    (hnc : ¬ ∃ y : Y, ∀ x : X, f x = y) : IsFinite f := by
  letI : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton c
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian c
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace c
  letI : IsNoetherian X := ⟨⟩
  letI : IsProper (f ≫ d) := by rw [hf]; infer_instance
  letI : IsProper f := IsProper.of_comp f d
  have hpoints :=
    (isClosed_singleton_or_isGenericPoint_and_exists_not_isGenericPoint_of_smoothOfRelativeDimension_one
      K c).1
  have hclosed : ∀ x : X, x ≠ genericPoint X → IsClosed ({x} : Set X) := by
    intro x hx
    rcases hpoints x with h | h
    · exact h
    · exact (hx (h.eq (genericPoint_spec X))).elim
  letI : LocallyQuasiFinite f := LocallyQuasiFinite.of_finite_preimage_singleton f (by
    intro y
    by_cases hy : IsClosed ({y} : Set Y)
    · apply Scheme.finite_of_isClosed_of_ne_univ_of_forall_isClosed_singleton hclosed
        (f ⁻¹' {y}) (hy.preimage f.continuous)
      intro h
      exact hnc ⟨y, fun x => by
        have hx : x ∈ f ⁻¹' {y} := h.symm ▸ Set.mem_univ x
        exact hx⟩
    · apply (Set.finite_singleton (genericPoint X)).subset
      intro x hx
      by_contra h
      have hc := f.isClosedMap _ (hclosed x h)
      rw [Set.image_singleton, show f x = y from hx] at hc
      exact hy hc)
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

/-- A nonconstant proper map from an irreducible scheme onto a proper curve
has the whole curve as its image. -/
theorem surjective_of_target_proper_curve_of_not_constant
    {K : Type u} [Field K] [IsAlgClosed K]
    {X Y : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of K))
    (d : Y ⟶ Spec (CommRingCat.of K))
    [IsProper c] [IrreducibleSpace X]
    [IsProper d] [SmoothOfRelativeDimension 1 d] [GeometricallyIntegral d]
    (f : X ⟶ Y) (hf : f ≫ d = c)
    (hnc : ¬ ∃ y : Y, ∀ x : X, f x = y) : Surjective f := by
  classical
  letI : IsIntegral Y := GeometricallyIntegral.isIntegral_of_subsingleton d
  letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian d
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace d
  letI : IsNoetherian Y := ⟨⟩
  letI : IsProper (f ≫ d) := by rw [hf]; infer_instance
  letI : IsProper f := IsProper.of_comp f d
  have hcl : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
  by_contra hsurj
  have hne : Set.range f ≠ Set.univ := fun h =>
    hsurj ⟨Set.range_eq_univ.mp h⟩
  have hη : genericPoint Y ∉ Set.range f := by
    intro h
    exact hne (Set.eq_univ_of_univ_subset (by
      rw [← genericPoint_closure Y]
      exact closure_minimal (Set.singleton_subset_iff.mpr h) hcl))
  have hpoints :=
    (isClosed_singleton_or_isGenericPoint_and_exists_not_isGenericPoint_of_smoothOfRelativeDimension_one
      K d).1
  have hclosed : ∀ y : Y, y ≠ genericPoint Y → IsClosed ({y} : Set Y) := by
    intro y hy
    rcases hpoints y with h | h
    · exact h
    · exact (hy (h.eq (genericPoint_spec Y))).elim
  have hfin := Scheme.finite_of_isClosed_of_ne_univ_of_forall_isClosed_singleton
    hclosed (Set.range f) hcl hne
  letI : Finite (Set.range f) := hfin.to_subtype
  letI : T1Space (Set.range f) := ⟨fun y => by
    have hy := hclosed y.1 (fun h => hη (h ▸ y.2))
    have he : (Subtype.val : Set.range f → Y) ⁻¹' {y.1} = {y} := by
      ext z
      exact Subtype.val_inj
    rw [← he]
    exact hy.preimage continuous_subtype_val⟩
  have hdisc : _root_.IsDiscrete (Set.range f) := isDiscrete_iff_discreteTopology.mpr inferInstance
  have hirr : IsPreirreducible (Set.range f) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ X).2.image f f.continuous.continuousOn
  have hsub := hdisc.subsingleton_of_isPreirreducible hirr
  let x₀ : X := Classical.choice inferInstance
  exact hnc ⟨f x₀, fun x => hsub ⟨x, rfl⟩ ⟨x₀, rfl⟩⟩

end SupersingularCurves.Geometry
