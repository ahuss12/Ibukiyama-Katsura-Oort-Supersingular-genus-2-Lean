/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Cancellation through nonzero rank-one factorizations

For actual cotangent maps of a quotient and its Frobenius twist, the
vanishing of the fourfold composite forces the middle twofold composite
to vanish. The only linear-algebra inputs are rank one for the middle
maps and nonvanishing of both outer pairs. No identification of twisted
cotangent spaces with untwisted spaces is needed.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.Geometry.RankOneFactorCancellation

variable {K U V W X Y : Type*} [Field K]
  [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [AddCommGroup X] [Module K X]
  [AddCommGroup Y] [Module K Y]

/-- A nonzero composite onto a rank-one image has that entire image. -/
theorem range_comp_eq_of_rank_one (f : U →ₗ[K] V) (g : V →ₗ[K] W)
    (hg : Module.finrank K (LinearMap.range g) = 1) (hgf : g.comp f ≠ 0) :
    LinearMap.range (g.comp f) = LinearMap.range g := by
  obtain ⟨u, hu⟩ := DFunLike.ne_iff.mp hgf
  have hu0 : g (f u) ≠ 0 := hu
  apply le_antisymm (LinearMap.range_comp_le_range f g)
  rw [eq_span_singleton_of_mem_of_finrank_eq_one hg ⟨f u, rfl⟩ hu0]
  exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ⟨u, rfl⟩)

/-- A map with nonzero composite is injective on a rank-one image. -/
theorem eq_zero_of_mem_rank_one_range (h : W →ₗ[K] X) (i : X →ₗ[K] Y)
    (hh : Module.finrank K (LinearMap.range h) = 1) (hih : i.comp h ≠ 0)
    {x : X} (hx : x ∈ LinearMap.range h) (hix : i x = 0) : x = 0 := by
  obtain ⟨w, hw⟩ := DFunLike.ne_iff.mp hih
  have hiw : i (h w) ≠ 0 := hw
  have hw0 : h w ≠ 0 := by
    intro hw0
    exact hiw (by rw [hw0, map_zero])
  rw [eq_span_singleton_of_mem_of_finrank_eq_one hh ⟨w, rfl⟩ hw0] at hx
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
  have hc0 : c = 0 := by
    rw [← hc, map_smul] at hix
    exact (smul_eq_zero.mp hix).resolve_right hiw
  simpa only [hc0, zero_smul] using hc.symm

/-- Rank-one outer factorizations let a vanishing fourfold composite
cancel to the actual middle composite. In the quotient application,
`f,g,h,i` are `dψ,dq,dψ^(p),dq^(p)`, respectively. -/
theorem middle_comp_eq_zero
    (f : U →ₗ[K] V) (g : V →ₗ[K] W) (h : W →ₗ[K] X) (i : X →ₗ[K] Y)
    (hg : Module.finrank K (LinearMap.range g) = 1)
    (hh : Module.finrank K (LinearMap.range h) = 1)
    (hgf : g.comp f ≠ 0) (hih : i.comp h ≠ 0)
    (hzero : (i.comp h).comp (g.comp f) = 0) : h.comp g = 0 := by
  ext v
  apply eq_zero_of_mem_rank_one_range h i hh hih ⟨g v, rfl⟩
  have hgv : g v ∈ LinearMap.range (g.comp f) := by
    rw [range_comp_eq_of_rank_one f g hg hgf]
    exact ⟨v, rfl⟩
  obtain ⟨u, hu⟩ := hgv
  change g (f u) = g v at hu
  have hz := LinearMap.congr_fun hzero u
  change i (h (g (f u))) = 0 at hz
  simpa only [hu] using hz

end SupersingularCurves.Geometry.RankOneFactorCancellation
