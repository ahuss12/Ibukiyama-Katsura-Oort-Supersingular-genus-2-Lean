/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.IKO.Semilinear

/-!
# Counting Cartier fixed vectors over an algebraically closed field

Fixed vectors of the inverse-Frobenius action satisfy `Mv = v^p`.
For a nonzero diagonal or antidiagonal two-by-two matrix of the forms
occurring in IKO, the fixed set has exactly `p^2` elements. The proof
counts the distinct roots of `X^q - aX`; it does not assume a p-rank
classification or a general semilinear descent theorem.
-/

set_option autoImplicit false
noncomputable section
namespace SupersingularCurves.IKO
open Polynomial Matrix
variable {K : Type*} [Field K]

/-- Roots of a scalar Frobenius equation, including zero. -/
def scalarRoots (q : ℕ) (a : K) := {z : K // z ^ q = a * z}

theorem card_scalarRoots [IsAlgClosed K] (q : ℕ) (hq : 1 < q)
    (hqK : (q : K) = 0) (a : K) (ha : a ≠ 0) :
    Nat.card (scalarRoots q a) = q := by
  classical
  let f : K[X] := X ^ q - C a * X
  have hdeg : f.natDegree = q := by
    dsimp [f]
    rw [natDegree_sub_eq_left_of_natDegree_lt, natDegree_X_pow]
    calc
      (C a * X).natDegree ≤ 1 := by compute_degree
      _ < (X ^ q : K[X]).natDegree := by simpa using hq
  have hf : f ≠ 0 := by
    intro h
    simp [h] at hdeg
    omega
  have hsep : f.Separable := by
    rw [separable_def]
    have hderiv : derivative f = C (-a) := by
      simp [f, derivative_X_pow, hqK]
    rw [hderiv]
    refine ⟨0, C (-a)⁻¹, ?_⟩
    simp [← C_mul, ha]
  let e : scalarRoots q a ≃ f.rootSet K :=
    Equiv.subtypeEquivRight (fun z => by
      simp [mem_rootSet_of_ne hf, f, sub_eq_zero])
  rw [Nat.card_congr e, Nat.card_eq_fintype_card,
    card_rootSet_eq_natDegree hsep (IsAlgClosed.splits_domain f), hdeg]

variable (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K]

/-- The additive subgroup of vectors fixed by inverse-Frobenius Cartier. -/
def fixedVectors (M : Matrix (Fin 2) (Fin 2) K) : AddSubgroup (Fin 2 → K) where
  carrier := {v | semilinearAction (frobeniusEquiv K p) M v = v}
  zero_mem' := by
    change semilinearAction (frobeniusEquiv K p) M 0 = 0
    ext i
    simp [semilinearAction]
  add_mem' hv hw := by
    change semilinearAction (frobeniusEquiv K p) M _ = _ at hv hw ⊢
    rw [semilinearAction_add, hv, hw]
  neg_mem' {v} hv := by
    change semilinearAction (frobeniusEquiv K p) M v = v at hv
    change semilinearAction (frobeniusEquiv K p) M (-v) = -v
    have h := semilinearAction_smul (frobeniusEquiv K p) M (-1) v
    simpa [hv] using h

theorem mem_fixedVectors_iff (M : Matrix (Fin 2) (Fin 2) K) (v : Fin 2 → K) :
    v ∈ fixedVectors p M ↔ ∀ i, (M.mulVec v) i = (v i) ^ p := by
  change (fun i => (frobeniusEquiv K p).symm ((M.mulVec v) i)) = v ↔ _
  rw [funext_iff]
  apply forall_congr'
  intro i
  exact (frobeniusEquiv K p).symm_apply_eq

theorem card_fixedVectors_zero :
    Nat.card (fixedVectors (K := K) p (0 : Matrix (Fin 2) (Fin 2) K)) = 1 := by
  have hzero : ∀ v : fixedVectors (K := K) p (0 : Matrix (Fin 2) (Fin 2) K), v = 0 := by
    intro v
    apply Subtype.ext
    have h := v.property
    change semilinearAction (frobeniusEquiv K p) 0 v.val = v.val at h
    change v.val = 0
    ext i
    simpa [semilinearAction] using congrFun h.symm i
  let : Subsingleton (fixedVectors (K := K) p (0 : Matrix (Fin 2) (Fin 2) K)) :=
    ⟨fun v w => (hzero v).trans (hzero w).symm⟩
  exact Nat.card_unique

def diagonalFixedEquiv (a b : K) :
    fixedVectors p !![a, 0; 0, b] ≃ scalarRoots p a × scalarRoots p b where
  toFun v := ⟨⟨v.val 0, by
      have h := (mem_fixedVectors_iff p _ v.val).mp v.property 0
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h.symm⟩,
    ⟨v.val 1, by
      have h := (mem_fixedVectors_iff p _ v.val).mp v.property 1
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h.symm⟩⟩
  invFun z := ⟨![z.1.val, z.2.val], by
    apply (mem_fixedVectors_iff p _ _).mpr
    intro i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      z.1.property, z.2.property]⟩
  left_inv v := by apply Subtype.ext; ext i; fin_cases i <;> rfl
  right_inv z := by cases z; rfl

theorem card_fixedVectors_diagonal [IsAlgClosed K] (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    Nat.card (fixedVectors p !![a, 0; 0, b]) = p ^ 2 := by
  rw [Nat.card_congr (diagonalFixedEquiv p a b), Nat.card_prod,
    card_scalarRoots p (Fact.out : p.Prime).one_lt (CharP.cast_eq_zero K p) a ha,
    card_scalarRoots p (Fact.out : p.Prime).one_lt (CharP.cast_eq_zero K p) b hb,
    pow_two]

/-- Eliminating the second coordinate gives `x^(p*p) = a^p*b*x`. -/
def antidiagonalFixedEquiv (a b : K) (ha : a ≠ 0) :
    fixedVectors p !![0, a; b, 0] ≃ scalarRoots (p * p) (a ^ p * b) where
  toFun v := ⟨v.val 0, by
    have h := (mem_fixedVectors_iff p _ v.val).mp v.property
    have h0 : a * v.val 1 = (v.val 0) ^ p := by
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h 0
    have h1 : b * v.val 0 = (v.val 1) ^ p := by
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h 1
    rw [pow_mul, ← h0, mul_pow, ← h1, mul_assoc]⟩
  invFun z := ⟨![z.val, a⁻¹ * z.val ^ p], by
    apply (mem_fixedVectors_iff p _ _).mpr
    intro i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, ha]
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      change b * z.val + 0 * (a⁻¹ * z.val ^ p) = (a⁻¹ * z.val ^ p) ^ p
      rw [zero_mul, add_zero, mul_pow, inv_pow, ← pow_mul, z.property]
      simp [← mul_assoc, pow_ne_zero p ha]⟩
  left_inv v := by
    apply Subtype.ext
    ext i
    fin_cases i
    · rfl
    · have h := (mem_fixedVectors_iff p _ v.val).mp v.property 0
      have h0 : a * v.val 1 = (v.val 0) ^ p := by
        simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h
      change a⁻¹ * (v.val 0) ^ p = v.val 1
      rw [← h0]
      simp [ha]
  right_inv z := rfl

theorem card_fixedVectors_antidiagonal [IsAlgClosed K]
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    Nat.card (fixedVectors p !![0, a; b, 0]) = p ^ 2 := by
  rw [Nat.card_congr (antidiagonalFixedEquiv p a b ha)]
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hpp : 1 < p * p := by nlinarith
  rw [card_scalarRoots (p * p) hpp (by simp)
    (a ^ p * b) (mul_ne_zero (pow_ne_zero p ha) hb), pow_two]

end SupersingularCurves.IKO
