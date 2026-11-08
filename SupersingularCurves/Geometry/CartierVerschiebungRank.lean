/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.CartierVerschiebung

/-!
# Invertibility of Cartier and actual Jacobian Verschiebung cotangents

The independently fixed cotangent/global-form and cohomological twist
equivalences identify injectivity, surjectivity and bijectivity of the two
actual operators. The scalar twist is retained; no geometric classification
is assumed, and no new operator is substituted for Verschiebung.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

namespace SupersingularCurves.Geometry.Jacobian
open CategoryTheory AlgebraicGeometry AlgebraicCurve InfinitesimalPicard NeronModelInfra

variable {K : Type u} [Field K] [IsAlgClosed K]
variable {F : Type v} [Field F] [Algebra K F]
variable {M : CurveModel K F}
  {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase}
variable (J : Jacobian M s) (V : DifferentialChart M)
variable [Algebra.EssFiniteType K F] [IsCurveOver K F]
variable (p : ℕ) [Fact p.Prime] [CharP K p]
variable (x : F) [FiniteDimensional (IntermediateField.adjoin K {x}) F]

/-- Injectivity is unaffected by the independently specified scalar untwist. -/
theorem verschiebungCotangent_injective_iff :
    Function.Injective (J.verschiebungCotangent p) ↔
      Function.Injective (V.globalCartier p x) := by
  constructor
  · intro h ω η hωη
    obtain ⟨z, rfl⟩ := (J.cotangentGlobalEquiv V).surjective ω
    obtain ⟨w, rfl⟩ := (J.cotangentGlobalEquiv V).surjective η
    apply congrArg (J.cotangentGlobalEquiv V)
    apply h
    apply (J.cotangentCohomologicalUntwist V.cover p).injective
    apply (J.cotangentGlobalEquiv V).injective
    simpa only [J.cotangentGlobalEquiv_verschiebung V p x] using hωη
  · intro h z w hzw
    apply (J.cotangentGlobalEquiv V).injective
    apply h
    rw [← J.cotangentGlobalEquiv_verschiebung V p x z,
      ← J.cotangentGlobalEquiv_verschiebung V p x w, hzw]

/-- Surjectivity compares the actual target cotangent space with global forms. -/
theorem verschiebungCotangent_surjective_iff :
    Function.Surjective (J.verschiebungCotangent p) ↔
      Function.Surjective (V.globalCartier p x) := by
  constructor
  · intro h ω
    obtain ⟨z, rfl⟩ := (J.cotangentGlobalEquiv V).surjective ω
    obtain ⟨w, hw⟩ := h ((J.cotangentCohomologicalUntwist V.cover p).symm z)
    refine ⟨J.cotangentGlobalEquiv V w, ?_⟩
    rw [← J.cotangentGlobalEquiv_verschiebung V p x w, hw,
      LinearEquiv.apply_symm_apply]
  · intro h z
    obtain ⟨ω, hω⟩ := h
      (J.cotangentGlobalEquiv V (J.cotangentCohomologicalUntwist V.cover p z))
    obtain ⟨w, rfl⟩ := (J.cotangentGlobalEquiv V).surjective ω
    refine ⟨w, ?_⟩
    apply (J.cotangentCohomologicalUntwist V.cover p).injective
    apply (J.cotangentGlobalEquiv V).injective
    exact (J.cotangentGlobalEquiv_verschiebung V p x w).trans hω

/-- Cartier is bijective exactly when the actual Verschiebung cotangent map is. -/
theorem verschiebungCotangent_bijective_iff :
    Function.Bijective (J.verschiebungCotangent p) ↔
      Function.Bijective (V.globalCartier p x) :=
  and_congr (J.verschiebungCotangent_injective_iff V p x)
    (J.verschiebungCotangent_surjective_iff V p x)

end SupersingularCurves.Geometry.Jacobian
