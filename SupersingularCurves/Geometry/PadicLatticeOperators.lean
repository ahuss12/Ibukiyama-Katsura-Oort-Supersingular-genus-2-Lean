/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.PadicLatticeCompactness

/-! # Compact limits on the rationalization of an actual integral lattice -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SupersingularCurves.Geometry.PadicLattice
open Module
open scoped TensorProduct nonZeroDivisors
variable (ℓ : ℕ) [Fact ℓ.Prime]
variable {ι T : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup T] [Module ℤ_[ℓ] T]

theorem toMatrix_baseChange (b : Basis ι ℤ_[ℓ] T) (f : Module.End ℤ_[ℓ] T) :
    LinearMap.toMatrix (b.baseChange ℚ_[ℓ]) (b.baseChange ℚ_[ℓ])
      (f.baseChange ℚ_[ℓ]) = rationalMatrix ℓ (LinearMap.toMatrix b b f) := by
  ext i j
  simp [LinearMap.toMatrix_apply, Basis.baseChange_apply,
    LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul, rationalMatrix,
    Algebra.smul_def]

theorem equivFun_baseChange_tmul (b : Basis ι ℤ_[ℓ] T) (x : T) :
    (b.baseChange ℚ_[ℓ]).equivFun ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x) =
      fun i => (b.repr x i : ℚ_[ℓ]) := by
  ext i
  simp [Basis.equivFun_apply, Basis.baseChange_repr_tmul, Algebra.smul_def]

/-- Integral operators whose errors approach `W`, and which have a fixed
nonzero image with integral preimages, yield a nonzero rational operator in
the same rational operator subspace with image contained in `W`. -/
theorem exists_nonzero_mem_range_le_of_integral_errors
    (b : Basis ι ℤ_[ℓ] T)
    (S : Submodule ℚ_[ℓ] (Module.End ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] T)))
    (W : Submodule ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] T))
    (f : ℕ → Module.End ℤ_[ℓ] T) (a : ℕ → ℕ) (ha : StrictMono a)
    (w : ℚ_[ℓ] ⊗[ℤ_[ℓ]] T) (hw : w ≠ 0) (y : ℕ → T)
    (hS : ∀ n, (f n).baseChange ℚ_[ℓ] ∈ S)
    (hpre : ∀ n, (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] f n (y n) = w)
    (herr : ∀ n x, ∃ e : T,
      (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] (f n x - (ℓ : ℤ_[ℓ]) ^ a n • e) ∈ W) :
    ∃ u ∈ S, u ≠ 0 ∧ LinearMap.range u ≤ W := by
  classical
  let bq := b.baseChange ℚ_[ℓ]
  let cq := bq.equivFun
  let cm := LinearMap.toMatrix bq bq
  choose er her using fun n j => herr n (b j)
  have hcoord : ∀ n, cm ((f n).baseChange ℚ_[ℓ]) =
      rationalMatrix ℓ (LinearMap.toMatrix b b (f n)) := fun n => toMatrix_baseChange ℓ b (f n)
  obtain ⟨v, hvS, hvne, hvW⟩ := exists_nonzero_mem_range_le ℓ
    (S.map cm.toLinearMap) (W.map cq.toLinearMap)
    (fun n => LinearMap.toMatrix b b (f n)) (fun n i => b.repr (y n) i)
    (fun n i j => b.repr (er n j) i) a ha (cq w)
    (fun h => hw (cq.injective (h.trans cq.map_zero.symm)))
    (fun n => ⟨(f n).baseChange ℚ_[ℓ], hS n, hcoord n⟩)
    (fun n => by
      rw [← hcoord n, ← equivFun_baseChange_tmul ℓ b (y n)]
      change (LinearMap.toMatrix bq bq ((f n).baseChange ℚ_[ℓ])).mulVec
        (bq.repr ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] y n)) = cq w
      rw [LinearMap.toMatrix_mulVec_repr, LinearMap.baseChange_tmul, hpre n]
      rfl)
    (fun n j => by
      refine ⟨(1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]]
        (f n (b j) - (ℓ : ℤ_[ℓ]) ^ a n • er n j), her n j, ?_⟩
      ext i
      simp [cq, bq, equivFun_baseChange_tmul, LinearMap.toMatrix_apply,
        map_sub, map_smul, Algebra.smul_def])
  obtain ⟨u, huS, huv⟩ := hvS
  refine ⟨u, huS, ?_, ?_⟩
  · intro hu
    apply hvne
    rw [← huv, hu, map_zero]
  · rintro _ ⟨x, rfl⟩
    have hx : cq (u x) ∈ W.map cq.toLinearMap := by
      apply hvW
      refine ⟨cq x, ?_⟩
      rw [← huv]
      exact LinearMap.toMatrix_mulVec_repr bq bq u x
    obtain ⟨z, hz, hzx⟩ := hx
    exact cq.injective hzx ▸ hz

/-- Membership in `U + ℓ^n T` supplies an actual integral error vector. -/
theorem exists_integral_error_of_mem_lattice
    (U : Submodule ℤ_[ℓ] T)
    (W : Submodule ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] T))
    (hUW : ∀ u ∈ U, (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] u ∈ W)
    (n : ℕ) (x : T)
    (hx : x ∈ U ⊔ (IsLocalRing.maximalIdeal ℤ_[ℓ] ^ n) •
      (⊤ : Submodule ℤ_[ℓ] T)) :
    ∃ e : T, (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] (x - (ℓ : ℤ_[ℓ]) ^ n • e) ∈ W := by
  obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow,
    Submodule.ideal_span_singleton_smul] at hz
  obtain ⟨e, _, rfl⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.mp hz
  exact ⟨e, by simpa only [add_sub_cancel_right] using hUW u hu⟩

/-- Clearing denominators supplies a nonzero integral vector in any nonzero
rational subspace. No basis or auxiliary representation is assumed. -/
theorem exists_nonzero_integral_vector
    (W : Submodule ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] T)) (hW : W ≠ ⊥) :
    ∃ w : T, (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] w ∈ W ∧
      (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] w ≠ 0 := by
  obtain ⟨v, hv, hvne⟩ := W.ne_bot_iff.mp hW
  obtain ⟨⟨w, s⟩, hs⟩ := IsLocalizedModule.surj (ℤ_[ℓ])⁰
    (TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] T 1) v
  have hsq : (algebraMap ℤ_[ℓ] ℚ_[ℓ] s : ℚ_[ℓ]) ≠ 0 :=
    (IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ]).ne
      (mem_nonZeroDivisors_iff_ne_zero.mp s.2)
  change (s : ℤ_[ℓ]) • v = (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] w at hs
  rw [← IsScalarTower.algebraMap_smul ℚ_[ℓ]] at hs
  exact ⟨w, hs ▸ W.smul_mem _ hv, hs ▸ smul_ne_zero hsq hvne⟩

end SupersingularCurves.Geometry.PadicLattice
