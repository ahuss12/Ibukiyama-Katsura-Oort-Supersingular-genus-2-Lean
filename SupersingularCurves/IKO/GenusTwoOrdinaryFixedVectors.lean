/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.IKO.GenusTwoFixedVectors

/-!
# The ordinary fixed-vector criterion for every two-by-two Cartier matrix

Fixed vectors satisfy `Mv = v^p`. Eliminating one coordinate gives a
degree-`p²` polynomial whose derivative is a nonzero scalar exactly when
the matrix determinant is nonzero. The converse uses the separability criterion for attaining the degree
bound on distinct roots.
The proof counts actual fixed vectors over an algebraically closed field.
-/

set_option autoImplicit false
noncomputable section
namespace SupersingularCurves.IKO
open Polynomial Matrix
variable {K : Type*} [Field K] [IsAlgClosed K]

omit [IsAlgClosed K] in
private theorem card_scalarRoots_zero (q : ℕ) (hq : q ≠ 0) :
    Nat.card (scalarRoots q (0 : K)) = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨⟨0, by simp [hq]⟩, ?_⟩
  intro z
  apply Subtype.ext
  change z.val = 0
  by_contra hz
  exact (pow_ne_zero q hz) (by simpa using z.property)

variable (p : ℕ) [Fact p.Prime] [CharP K p]

private def frobeniusTrinomialRoots (A B : K) :=
  {x : K // x ^ (p * p) - A * x ^ p + B * x = 0}

private theorem card_frobeniusTrinomialRoots_eq_prime_sq_iff (A B : K) :
    Nat.card (frobeniusTrinomialRoots p A B) = p ^ 2 ↔ B ≠ 0 := by
  classical
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hpp : p < p * p := by nlinarith
  let f : K[X] := X ^ (p * p) - C A * X ^ p + C B * X
  have hdeg : f.natDegree = p * p := by
    dsimp [f]
    compute_degree! <;> (try simp [ne_of_gt hpp, hp.ne']) <;> omega
  have hf : f ≠ 0 := by
    intro h
    simp [h] at hdeg
    nlinarith
  have hderiv : derivative f = C B := by
    simp [f, derivative_X_pow]
  let e : frobeniusTrinomialRoots p A B ≃ f.rootSet K :=
    Equiv.subtypeEquivRight (fun z => by
      simp [mem_rootSet_of_ne hf, f])
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, pow_two, ← hdeg,
    card_rootSet_eq_natDegree_iff_of_splits hf (IsAlgClosed.splits_domain f)]
  constructor
  · intro hsep
    have h := hsep.aeval_derivative_ne_zero (x := (0 : K)) (by
      simp [f, show p ≠ 0 by omega, show p * p ≠ 0 by nlinarith])
    simpa [hderiv] using h
  · intro hB
    rw [separable_def, hderiv]
    refine ⟨0, C B⁻¹, ?_⟩
    simp [← C_mul, hB]

private def offDiagonalFixedEquiv (a b c d : K) (hb : b ≠ 0) :
    fixedVectors p !![a, b; c, d] ≃
      frobeniusTrinomialRoots p
        (a ^ p + d * b ^ p / b) ((a * d - b * c) * b ^ p / b) where
  toFun v := ⟨v.val 0, by
    have hv := (mem_fixedVectors_iff p _ v.val).mp v.property
    have h0 : a * v.val 0 + b * v.val 1 = (v.val 0) ^ p := by
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hv 0
    have h1 : c * v.val 0 + d * v.val 1 = (v.val 1) ^ p := by
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hv 1
    have h0p := congrArg (fun z : K => z ^ p) h0
    rw [add_pow_char, mul_pow, mul_pow, ← pow_mul, ← h1] at h0p
    field_simp
    linear_combination -b * h0p + d * b ^ p * h0⟩
  invFun x := ⟨![x.val, (x.val ^ p - a * x.val) / b], by
    apply (mem_fixedVectors_iff p _ _).mpr
    intro i
    fin_cases i
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      change a * x.val + b * ((x.val ^ p - a * x.val) / b) = x.val ^ p
      field_simp
      ring
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      change c * x.val + d * ((x.val ^ p - a * x.val) / b) =
        ((x.val ^ p - a * x.val) / b) ^ p
      have he := x.property
      rw [div_pow, sub_pow_char, mul_pow, ← pow_mul]
      apply (eq_div_iff (pow_ne_zero p hb)).mpr
      field_simp at he ⊢
      linear_combination -he⟩
  left_inv v := by
    apply Subtype.ext
    ext i
    fin_cases i
    · rfl
    · have hv := (mem_fixedVectors_iff p _ v.val).mp v.property 0
      have h0 : a * v.val 0 + b * v.val 1 = (v.val 0) ^ p := by
        simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hv
      change ((v.val 0) ^ p - a * v.val 0) / b = v.val 1
      apply (div_eq_iff hb).mpr
      linear_combination -h0
  right_inv x := rfl

private theorem card_offDiagonalFixed_eq_prime_sq_iff (a b c d : K) (hb : b ≠ 0) :
    Nat.card (fixedVectors p !![a, b; c, d]) = p ^ 2 ↔
      a * d - b * c ≠ 0 := by
  rw [Nat.card_congr (offDiagonalFixedEquiv p a b c d hb),
    card_frobeniusTrinomialRoots_eq_prime_sq_iff]
  simp [hb, pow_ne_zero p hb]

private def swapFixedEquiv (a b c d : K) :
    fixedVectors p !![a, b; c, d] ≃ fixedVectors p !![d, c; b, a] where
  toFun v := ⟨![v.val 1, v.val 0], by
    have h := (mem_fixedVectors_iff p _ v.val).mp v.property
    apply (mem_fixedVectors_iff p _ _).mpr
    intro i
    fin_cases i
    · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, add_comm] using h 1
    · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, add_comm] using h 0⟩
  invFun v := ⟨![v.val 1, v.val 0], by
    have h := (mem_fixedVectors_iff p _ v.val).mp v.property
    apply (mem_fixedVectors_iff p _ _).mpr
    intro i
    fin_cases i
    · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, add_comm] using h 1
    · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, add_comm] using h 0⟩
  left_inv v := by apply Subtype.ext; ext i; fin_cases i <;> rfl
  right_inv v := by apply Subtype.ext; ext i; fin_cases i <;> rfl

private theorem card_diagonalFixed_eq_prime_sq_iff (a d : K) :
    Nat.card (fixedVectors p !![a, 0; 0, d]) = p ^ 2 ↔ a * d ≠ 0 := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  rw [Nat.card_congr (diagonalFixedEquiv p a d), Nat.card_prod]
  by_cases ha : a = 0 <;> by_cases hd : d = 0
  · simp [ha, hd, card_scalarRoots_zero p (show p ≠ 0 by omega)]
    nlinarith
  · rw [ha, card_scalarRoots_zero p (by omega),
      card_scalarRoots p hp (CharP.cast_eq_zero K p) d hd]
    simp
    nlinarith
  · rw [hd, card_scalarRoots_zero p (by omega),
      card_scalarRoots p hp (CharP.cast_eq_zero K p) a ha]
    simp
    nlinarith
  · rw [card_scalarRoots p hp (CharP.cast_eq_zero K p) a ha,
      card_scalarRoots p hp (CharP.cast_eq_zero K p) d hd]
    simp [ha, hd, pow_two]

/-- An arbitrary two-dimensional Cartier action has exactly `p²` fixed
vectors precisely when its coefficient matrix has nonzero determinant. -/
theorem card_fixedVectors_eq_prime_sq_iff_det_ne_zero
    (M : Matrix (Fin 2) (Fin 2) K) :
    Nat.card (fixedVectors p M) = p ^ 2 ↔ M.det ≠ 0 := by
  have hM : M = !![M 0 0, M 0 1; M 1 0, M 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hM, Matrix.det_fin_two]
  by_cases hb : M 0 1 = 0
  · by_cases hc : M 1 0 = 0
    · simpa [hb, hc] using card_diagonalFixed_eq_prime_sq_iff p (M 0 0) (M 1 1)
    · rw [Nat.card_congr (swapFixedEquiv p (M 0 0) (M 0 1) (M 1 0) (M 1 1)),
        card_offDiagonalFixed_eq_prime_sq_iff p _ _ _ _ hc]
      simp [mul_comm]
  · exact card_offDiagonalFixed_eq_prime_sq_iff p _ _ _ _ hb

end SupersingularCurves.IKO
