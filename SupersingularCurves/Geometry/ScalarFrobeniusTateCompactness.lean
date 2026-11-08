/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import Mathlib

/-!
# The finite-dimensional compactness step of Tate's argument

A bounded sequence of linear maps in the scalar span of actual morphisms
has a limit in that same span. If its images approach a prescribed kernel,
and a finite spanning family has uniformly bounded preimages, the limit has
exactly that kernel as its image. Finite generation of an integral Hom group
is not an assumption: every subspace of the finite-dimensional operator
space is closed over the complete scalar field.

This analytic lemma does not assert that the geometric isogenies supplying
the sequence have been constructed.
-/
set_option maxHeartbeats 800000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SupersingularCurves.Geometry.ScalarFrobeniusTate
open Filter Topology

variable {k : Type*} [NontriviallyNormedField k] [CompleteSpace k]
variable {V Q : Type*} [NormedAddCommGroup V] [NormedSpace k V]
  [FiniteDimensional k V] [ProperSpace V]
  [NormedAddCommGroup Q] [NormedSpace k Q]

/-- Compactness realizes an exact limiting image inside any prescribed
scalar subspace of actual linearized morphisms. -/
theorem exists_mem_range_eq_of_bounded_preimages
    [ProperSpace (V →L[k] V)]
    (S : Submodule k (V →L[k] V)) (π : V →L[k] Q)
    {ι : Type*} [Fintype ι] (w : ι → V)
    (hspan : Submodule.span k (Set.range w) = LinearMap.ker π.toLinearMap)
    (f : ℕ → V →L[k] V) (y : ℕ → ι → V)
    (hfS : ∀ n, f n ∈ S) (C D : ℝ)
    (hfbound : ∀ n, ‖f n‖ ≤ C) (hybound : ∀ n, ‖y n‖ ≤ D)
    (hpre : ∀ n i, f n (y n i) = w i)
    (hlim : ∀ v : V, Tendsto (fun n => π (f n v)) atTop (𝓝 0)) :
    ∃ u ∈ S, LinearMap.range u.toLinearMap = LinearMap.ker π.toLinearMap := by
  have hcompact : IsCompact (Metric.closedBall (0 : V →L[k] V) C ×ˢ
      Metric.closedBall (0 : ι → V) D) :=
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  obtain ⟨z, hz, a, ha, hza⟩ := hcompact.tendsto_subseq
    (x := fun n => (f n, y n)) (fun n => by
      exact ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hfbound n,
        by simpa only [Metric.mem_closedBall, dist_zero_right] using hybound n⟩)
  have hfa : Tendsto (fun n => f (a n)) atTop (𝓝 z.1) := by
    simpa only [Function.comp_def, Prod.fst, Prod.snd] using (continuous_fst.tendsto z).comp hza
  have hya : Tendsto (fun n => y (a n)) atTop (𝓝 z.2) := by
    simpa only [Function.comp_def, Prod.fst, Prod.snd] using (continuous_snd.tendsto z).comp hza
  have heval : Continuous (fun z : (V →L[k] V) × V => z.1 z.2) :=
    continuous_fst.clm_apply continuous_snd
  have hzS : z.1 ∈ S := S.closed_of_finiteDimensional.mem_of_tendsto hfa
    (Filter.Eventually.of_forall fun n => hfS (a n))
  refine ⟨z.1, hzS, le_antisymm ?_ ?_⟩
  · rintro _ ⟨v, rfl⟩
    change π (z.1 v) = 0
    have hv : Tendsto (fun n => f (a n) v) atTop (𝓝 (z.1 v)) := by
      simpa only [Function.comp_def] using
        (heval.tendsto (z.1, v)).comp (hfa.prodMk_nhds tendsto_const_nhds)
    have h₁ : Tendsto (fun n => π (f (a n) v)) atTop (𝓝 (π (z.1 v))) :=
      (π.continuous.tendsto (z.1 v)).comp hv
    have h₂ : Tendsto (fun n => π (f (a n) v)) atTop (𝓝 0) :=
      (hlim v).comp ha.tendsto_atTop
    exact tendsto_nhds_unique h₁ h₂
  · rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    refine ⟨z.2 i, ?_⟩
    have hyi : Tendsto (fun n => y (a n) i) atTop (𝓝 (z.2 i)) :=
      ((continuous_apply i).tendsto z.2).comp hya
    have h₁ : Tendsto (fun n => f (a n) (y (a n) i)) atTop (𝓝 (z.1 (z.2 i))) := by
      simpa only [Function.comp_def] using
        (heval.tendsto (z.1, z.2 i)).comp (hfa.prodMk_nhds hyi)
    have h₂ : Tendsto (fun n => f (a n) (y (a n) i)) atTop (𝓝 (w i)) := by
      simpa only [hpre] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => w i) atTop (𝓝 (w i)))
    exact tendsto_nhds_unique h₁ h₂

/-- In the p-adic finite-dimensional setting the operator and source
compactness hypotheses follow automatically from properness. -/
theorem exists_padic_mem_range_eq_of_bounded_preimages
    (ℓ : ℕ) [Fact ℓ.Prime]
    {V Q : Type*} [NormedAddCommGroup V] [NormedSpace ℚ_[ℓ] V]
    [FiniteDimensional ℚ_[ℓ] V]
    [NormedAddCommGroup Q] [NormedSpace ℚ_[ℓ] Q]
    (S : Submodule ℚ_[ℓ] (V →L[ℚ_[ℓ]] V)) (π : V →L[ℚ_[ℓ]] Q)
    {ι : Type*} [Fintype ι] (w : ι → V)
    (hspan : Submodule.span ℚ_[ℓ] (Set.range w) = LinearMap.ker π.toLinearMap)
    (f : ℕ → V →L[ℚ_[ℓ]] V) (y : ℕ → ι → V)
    (hfS : ∀ n, f n ∈ S) (C D : ℝ)
    (hfbound : ∀ n, ‖f n‖ ≤ C) (hybound : ∀ n, ‖y n‖ ≤ D)
    (hpre : ∀ n i, f n (y n i) = w i)
    (hlim : ∀ v : V, Tendsto (fun n => π (f n v)) atTop (𝓝 0)) :
    ∃ u ∈ S, LinearMap.range u.toLinearMap = LinearMap.ker π.toLinearMap := by
  letI : ProperSpace V := FiniteDimensional.proper ℚ_[ℓ] V
  letI : ProperSpace (V →L[ℚ_[ℓ]] V) := FiniteDimensional.proper ℚ_[ℓ] _
  exact exists_mem_range_eq_of_bounded_preimages S π w hspan f y hfS C D hfbound hybound hpre hlim

end SupersingularCurves.Geometry.ScalarFrobeniusTate
