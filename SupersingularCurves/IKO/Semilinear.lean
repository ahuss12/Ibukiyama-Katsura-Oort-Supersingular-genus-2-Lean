/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import Mathlib

/-!
# The semilinear convention behind IKO Lemma 1.1

This is linear algebra on coordinate vectors. Identifying it with the
Cartier operator of a curve requires a separate regular-differential basis
theorem. In particular, this file does not define supersingularity.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.IKO

open Matrix

variable {K : Type*} [Field K]

def twistMatrix (σ : K ≃+* K) (M : Matrix (Fin 2) (Fin 2) K) :=
  M.map σ

/-- The coordinate action is σ⁻¹(Mv), with the inverse applied entrywise. -/
def semilinearAction (σ : K ≃+* K) (M : Matrix (Fin 2) (Fin 2) K)
    (v : Fin 2 → K) : Fin 2 → K :=
  fun i => σ.symm ((M.mulVec v) i)

theorem semilinearAction_add (σ : K ≃+* K) (M : Matrix (Fin 2) (Fin 2) K)
    (v w : Fin 2 → K) :
    semilinearAction σ M (v + w) = semilinearAction σ M v + semilinearAction σ M w := by
  ext i
  simp [semilinearAction, Matrix.mulVec_add]

theorem semilinearAction_smul (σ : K ≃+* K) (M : Matrix (Fin 2) (Fin 2) K)
    (a : K) (v : Fin 2 → K) :
    semilinearAction σ M (a • v) = σ.symm a • semilinearAction σ M v := by
  ext i
  simp [semilinearAction, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    mul_add, add_mul]
  ring

/-- The order is σ(M)M. Replacing it by an ordinary square loses the twist. -/
theorem semilinearAction_square (σ : K ≃+* K) (M : Matrix (Fin 2) (Fin 2) K)
    (v : Fin 2 → K) :
    semilinearAction σ M (semilinearAction σ M v) =
      semilinearAction (σ.trans σ) (twistMatrix σ M * M) v := by
  ext i
  simp [semilinearAction, twistMatrix, Matrix.mulVec, Matrix.mul_apply,
    dotProduct, Fin.sum_univ_two, mul_add, add_mul]
  ring

theorem semilinearAction_zero_iff (σ : K ≃+* K) (M : Matrix (Fin 2) (Fin 2) K) :
    (∀ v, semilinearAction σ M v = 0) ↔ M = 0 := by
  constructor
  · intro h
    ext i j
    fin_cases j
    · have hi := congrFun (h ![1, 0]) i
      simpa [semilinearAction, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hi
    · have hi := congrFun (h ![0, 1]) i
      simpa [semilinearAction, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hi
  · rintro rfl
    intro v
    ext i
    simp [semilinearAction, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem semilinearAction_square_zero_iff (σ : K ≃+* K)
    (M : Matrix (Fin 2) (Fin 2) K) :
    (∀ v, semilinearAction σ M (semilinearAction σ M v) = 0) ↔
      twistMatrix σ M * M = 0 := by
  simp only [semilinearAction_square]
  exact semilinearAction_zero_iff (σ.trans σ) _

theorem frobenius_twistMatrix (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K]
    (M : Matrix (Fin 2) (Fin 2) K) :
    twistMatrix (frobeniusEquiv K p) M = M.map (fun a => a ^ p) := by
  rfl

/-- A nonzero matrix can give a square-zero semilinear action. -/
theorem nonzero_square_zero_example (σ : K ≃+* K) :
    let N : Matrix (Fin 2) (Fin 2) K := !![0, 0; 1, 0]
    N ≠ 0 ∧ ∀ v, semilinearAction σ N (semilinearAction σ N v) = 0 := by
  dsimp
  constructor
  · intro h
    have he := congrFun (congrFun h 1) 0
    simpa using he
  · rw [semilinearAction_square_zero_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [twistMatrix, Matrix.mul_apply, Fin.sum_univ_two]

end SupersingularCurves.IKO
