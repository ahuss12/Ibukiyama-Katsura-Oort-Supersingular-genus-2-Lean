/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import Mathlib

/-!
# A nonzero limit of integral operators

Integral matrices, integral preimages, and integral errors lie in a compact
space. A fixed nonzero image prevents the limiting matrix from vanishing.
Errors divisible by increasingly large powers of the prime disappear, so the
limiting image lies in the prescribed rational subspace. No bounds on a chosen
operator norm, and no integral finite-generation theorem for geometric Hom
groups, are required.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace SupersingularCurves.Geometry.PadicLattice
open Filter Topology
open scoped Matrix.Norms.Elementwise
variable (ℓ : ℕ) [Fact ℓ.Prime]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Entrywise inclusion of an integral matrix in its rational matrix space. -/
def rationalMatrix (M : Matrix ι ι ℤ_[ℓ]) : Matrix ι ι ℚ_[ℓ] :=
  fun i j => (M i j : ℚ_[ℓ])

omit [Fintype ι] [DecidableEq ι] in
theorem continuous_rationalMatrix : Continuous (rationalMatrix ℓ (ι := ι)) := by
  unfold rationalMatrix
  fun_prop

/-- The limit stays in the given operator subspace, is nonzero, and has image
in `W`. The fixed nonzero vector is an image of an integral vector at every
stage; each column differs from `W` by a prime-power multiple of an integral
error vector. -/
theorem exists_nonzero_mem_range_le
    (S : Submodule ℚ_[ℓ] (Matrix ι ι ℚ_[ℓ]))
    (W : Submodule ℚ_[ℓ] (ι → ℚ_[ℓ]))
    (M : ℕ → Matrix ι ι ℤ_[ℓ]) (y : ℕ → ι → ℤ_[ℓ])
    (err : ℕ → Matrix ι ι ℤ_[ℓ]) (a : ℕ → ℕ) (ha : StrictMono a)
    (w : ι → ℚ_[ℓ]) (hw : w ≠ 0)
    (hS : ∀ n, rationalMatrix ℓ (M n) ∈ S)
    (hpre : ∀ n, (rationalMatrix ℓ (M n)).mulVec (fun i => (y n i : ℚ_[ℓ])) = w)
    (hW : ∀ n j, (fun i => (M n i j : ℚ_[ℓ]) -
      (ℓ : ℚ_[ℓ]) ^ a n * (err n i j : ℚ_[ℓ])) ∈ W) :
    ∃ u ∈ S, u ≠ 0 ∧ LinearMap.range (Matrix.toLin' u) ≤ W := by
  classical
  have : CompactSpace (Matrix ι ι ℤ_[ℓ]) :=
    inferInstanceAs (CompactSpace (ι → ι → ℤ_[ℓ]))
  have : FirstCountableTopology (Matrix ι ι ℤ_[ℓ]) :=
    inferInstanceAs (FirstCountableTopology (ι → ι → ℤ_[ℓ]))
  obtain ⟨z, b, hb, hz⟩ := CompactSpace.tendsto_subseq
    (fun n => (M n, y n, err n))
  have hM : Tendsto (fun n => rationalMatrix ℓ (M (b n))) atTop
      (𝓝 (rationalMatrix ℓ z.1)) := by
    exact ((continuous_rationalMatrix ℓ).comp continuous_fst).tendsto z |>.comp hz
  have hy : Tendsto (fun n i => (y (b n) i : ℚ_[ℓ])) atTop
      (𝓝 (fun i => (z.2.1 i : ℚ_[ℓ]))) := by
    have hc : Continuous (fun t : Matrix ι ι ℤ_[ℓ] × (ι → ℤ_[ℓ]) ×
        Matrix ι ι ℤ_[ℓ] => fun i => (t.2.1 i : ℚ_[ℓ])) := by fun_prop
    exact (hc.tendsto z).comp hz
  have hp : Tendsto (fun n => (ℓ : ℚ_[ℓ]) ^ a (b n)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (Padic.norm_p_lt_one (p := ℓ))).comp
      (ha.tendsto_atTop.comp hb.tendsto_atTop)
  have hnonzero : rationalMatrix ℓ z.1 ≠ 0 := by
    intro hzero
    have heval : Continuous (fun t : Matrix ι ι ℚ_[ℓ] × (ι → ℚ_[ℓ]) =>
        t.1.mulVec t.2) := by
      unfold Matrix.mulVec dotProduct
      fun_prop
    have hlim := (heval.tendsto (rationalMatrix ℓ z.1,
      fun i => (z.2.1 i : ℚ_[ℓ]))).comp (hM.prodMk_nhds hy)
    have heq : (rationalMatrix ℓ z.1).mulVec (fun i => (z.2.1 i : ℚ_[ℓ])) = w :=
      tendsto_nhds_unique hlim (by simpa only [Function.comp_def, hpre] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => w) atTop (𝓝 w)))
    exact hw (by simpa [hzero] using heq.symm)
  refine ⟨rationalMatrix ℓ z.1,
    S.closed_of_finiteDimensional.mem_of_tendsto hM (.of_forall fun n => hS (b n)),
    hnonzero, ?_⟩
  rw [Matrix.range_toLin', Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  apply W.closed_of_finiteDimensional.mem_of_tendsto
    (b := atTop)
    (f := fun n i => (M (b n) i j : ℚ_[ℓ]) -
      (ℓ : ℚ_[ℓ]) ^ a (b n) * (err (b n) i j : ℚ_[ℓ]))
  · apply tendsto_pi_nhds.mpr
    intro i
    have hentry : Tendsto (fun n => (M (b n) i j : ℚ_[ℓ])) atTop
        (𝓝 (z.1 i j : ℚ_[ℓ])) :=
      ((continuous_apply j).tendsto _).comp
        (((continuous_apply i).tendsto _).comp hM)
    have herr : Tendsto (fun n => (err (b n) i j : ℚ_[ℓ])) atTop
        (𝓝 (z.2.2 i j : ℚ_[ℓ])) := by
      have hc : Continuous (fun t : Matrix ι ι ℤ_[ℓ] × (ι → ℤ_[ℓ]) ×
          Matrix ι ι ℤ_[ℓ] => (t.2.2 i j : ℚ_[ℓ])) := by fun_prop
      exact (hc.tendsto z).comp hz
    simpa only [zero_mul, sub_zero, Matrix.col, Matrix.transpose_apply, rationalMatrix] using
      hentry.sub (hp.mul herr)
  · exact .of_forall fun n => hW (b n) j

end SupersingularCurves.Geometry.PadicLattice
