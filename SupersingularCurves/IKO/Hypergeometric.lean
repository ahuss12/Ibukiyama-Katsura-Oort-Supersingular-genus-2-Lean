/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Portions adapted from work Copyright (c) 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import Mathlib

/-!
# The differential-equation argument in IKO Proposition 1.14

This is the algebraic part of the main proof in IKO, equations (1.31)--(1.34).
A polynomial solution of degree less than the characteristic has no repeated
root away from 0 and 1. The degree hypothesis is essential in positive
characteristic. No analytic hypergeometric or gamma function is assumed.

The derivative-propagation and algebraic-closure proofs generalize the
vendored FLT proof `S_Polynomial_separable_deuringPolynomial_map.lean`.
Exact source attribution and adaptations are recorded in
`provenance/hypergeometric-generalization.json`.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.IKO
open Polynomial

variable {K : Type*} [Field K]

/-- The hypergeometric operator after differentiating k times. -/
def hypergeometricOp (a b c : K) (k : ℕ) (f : K[X]) : K[X] :=
  X * (1 - X) * derivative (derivative f) +
    (C (c + k) - C (a + b + 2 * k + 1) * X) * derivative f -
    C ((a + k) * (b + k)) * f

theorem derivative_hypergeometricOp (a b c : K) (k : ℕ) (f : K[X]) :
    derivative (hypergeometricOp a b c k f) =
      hypergeometricOp a b c (k + 1) (derivative f) := by
  simp only [hypergeometricOp, derivative_sub, derivative_add, derivative_mul,
    derivative_X, derivative_one, derivative_C]
  simp only [Nat.cast_add, Nat.cast_one, map_add, map_mul, map_one, map_ofNat, map_natCast]
  ring

theorem eval_hypergeometricOp (a b c : K) (k : ℕ) (f : K[X]) (t : K) :
    (hypergeometricOp a b c k f).eval t =
      t * (1 - t) * (derivative (derivative f)).eval t +
        (c + k - (a + b + 2 * k + 1) * t) * (derivative f).eval t -
        ((a + k) * (b + k)) * f.eval t := by
  simp [hypergeometricOp]

theorem coeff_hypergeometricOp_zero (a b c : K) (f : K[X]) (n : ℕ) :
    (hypergeometricOp a b c 0 f).coeff n =
      ((n : K) + 1) * (n + c) * f.coeff (n + 1) -
        (n + a) * (n + b) * f.coeff n := by
  have hnorm : hypergeometricOp a b c 0 f =
      derivative (X * derivative f) + C (c - 1) * derivative f -
        X * derivative (X * derivative f) - C (a + b) * (X * derivative f) -
        C (a * b) * f := by
    simp only [hypergeometricOp, Nat.cast_zero, add_zero, mul_zero,
      derivative_mul, derivative_X]
    simp only [map_add, map_sub, map_mul, map_one]
    ring
  rw [hnorm]
  rcases n with _ | n
  · simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_derivative,
      coeff_X_mul, coeff_X_mul_zero, Nat.cast_zero]
    ring
  · simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_derivative,
      coeff_X_mul, Nat.cast_succ]
    ring

theorem hypergeometricOp_iterate_derivative (a b c : K) (f : K[X])
    (heq : hypergeometricOp a b c 0 f = 0) (k : ℕ) :
    hypergeometricOp a b c k (derivative^[k] f) = 0 := by
  induction k with
  | zero => simpa using heq
  | succ k ih =>
      rw [Function.iterate_succ_apply', ← derivative_hypergeometricOp, ih, map_zero]

theorem iterate_derivative_natDegree (f : K[X]) :
    derivative^[f.natDegree] f = C ((f.natDegree.factorial : K) * f.leadingCoeff) := by
  have hd : (derivative^[f.natDegree] f).natDegree ≤ 0 := by
    simpa using natDegree_iterate_derivative f f.natDegree
  rw [eq_C_of_natDegree_le_zero hd, coeff_iterate_derivative, zero_add,
    Nat.descFactorial_self]
  simp [nsmul_eq_mul]

/-- An ordinary point of the differential equation cannot be a repeated root.
The polynomial's degree must be strictly below p. -/
theorem not_isRoot_derivative_of_hypergeometric (p : ℕ) [Fact p.Prime] [CharP K p]
    (a b c : K) (f : K[X]) (hf : f ≠ 0) (hdeg : f.natDegree < p)
    (heq : hypergeometricOp a b c 0 f = 0)
    {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) (ht : f.IsRoot t) :
    ¬ (derivative f).IsRoot t := by
  intro ht'
  have hne : t * (1 - t) ≠ 0 := mul_ne_zero ht0 (sub_ne_zero.mpr ht1.symm)
  have step : ∀ k, (derivative^[k] f).eval t = 0 →
      (derivative^[k + 1] f).eval t = 0 → (derivative^[k + 2] f).eval t = 0 := by
    intro k hk hk1
    have e := congrArg (eval t) (hypergeometricOp_iterate_derivative a b c f heq k)
    rw [eval_hypergeometricOp, eval_zero] at e
    simp only [Function.iterate_succ_apply'] at hk1 ⊢
    rw [hk, hk1, mul_zero, mul_zero, sub_zero, add_zero] at e
    exact (mul_eq_zero.mp e).resolve_left hne
  have hall : ∀ k, (derivative^[k] f).eval t = 0 := by
    intro k
    induction k using Nat.twoStepInduction with
    | zero => simpa using ht.eq_zero
    | one => simpa using ht'.eq_zero
    | more k hk hk1 => exact step k hk hk1
  have htop := hall f.natDegree
  rw [iterate_derivative_natDegree, eval_C] at htop
  have hfac : (f.natDegree.factorial : K) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff K p, (Fact.out : p.Prime).dvd_factorial] at h
    omega
  exact (mul_ne_zero hfac (leadingCoeff_ne_zero.mpr hf)) htop

theorem map_hypergeometricOp {L : Type*} [Field L] (φ : K →+* L)
    (a b c : K) (k : ℕ) (f : K[X]) :
    (hypergeometricOp a b c k f).map φ =
      hypergeometricOp (φ a) (φ b) (φ c) k (f.map φ) := by
  simp [hypergeometricOp, derivative_map, map_ofNat]

/-- The root argument applies after algebraic closure, so the conclusion is
separability over any field of characteristic p. -/
theorem separable_of_hypergeometric (p : ℕ) [Fact p.Prime] [CharP K p]
    (a b c : K) (f : K[X]) (hdeg : f.natDegree < p)
    (heq : hypergeometricOp a b c 0 f = 0)
    (h0 : f.eval 0 ≠ 0) (h1 : f.eval 1 ≠ 0) : f.Separable := by
  classical
  let L := AlgebraicClosure K
  let φ := algebraMap K L
  have hf : f ≠ 0 := by rintro rfl; simp at h0
  have hf' : f.map φ ≠ 0 := map_ne_zero hf
  have heq' : hypergeometricOp (φ a) (φ b) (φ c) 0 (f.map φ) = 0 := by
    simpa only [map_hypergeometricOp, Polynomial.map_zero] using congrArg (Polynomial.map φ) heq
  have h0' : (f.map φ).eval 0 ≠ 0 := by
    intro h
    apply h0
    apply φ.injective
    simpa [φ, eval_map, ← coeff_zero_eq_eval_zero] using h
  have h1' : (f.map φ).eval 1 ≠ 0 := by
    intro h
    apply h1
    apply φ.injective
    simpa [φ, eval_map] using h
  rw [← separable_map φ, ← nodup_roots_iff_of_splits hf' (IsAlgClosed.splits _),
    Multiset.nodup_iff_count_le_one]
  intro t
  rw [count_roots]
  by_contra h
  obtain ⟨ht, ht'⟩ := (one_lt_rootMultiplicity_iff_isRoot hf').mp (not_le.mp h)
  have ht0 : t ≠ 0 := by rintro rfl; exact h0' ht.eq_zero
  have ht1 : t ≠ 1 := by rintro rfl; exact h1' ht.eq_zero
  exact not_isRoot_derivative_of_hypergeometric p (φ a) (φ b) (φ c) (f.map φ) hf'
    (by simpa using hdeg) heq' ht0 ht1 ht ht'

end SupersingularCurves.IKO
