/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.IKO.SimpleRoots

/-!
# The four differential equations in IKO (1.34)

These are (1.31) with the four parameter triples in (1.34), after clearing
denominators. The equations are homogeneous, so they hold for the original
g and h as well as the paper's normalized G and H.
-/

set_option autoImplicit false
noncomputable section
namespace SupersingularCurves.IKO
open Polynomial
variable {K : Type*} [Field K]

theorem scaled_hypergeometric_equation (a b c q u v w : K) (f : K[X])
    (hu : q * c = u) (hv : q * (a + b + 1) = v) (hw : q * (a * b) = w)
    (hf : hypergeometricOp a b c 0 f = 0) :
    C q * (X * (1 - X)) * derivative (derivative f) +
      (C u - C v * X) * derivative f - C w * f = 0 := by
  calc
    _ = C q * hypergeometricOp a b c 0 f := by
      rw [← hu, ← hv, ← hw]
      simp only [hypergeometricOp, Nat.cast_zero, mul_zero, add_zero, map_mul]
      ring
    _ = 0 := by rw [hf, mul_zero]

variable (p : ℕ) [Fact p.Prime] [CharP K p]

theorem cast_half_index (hp3 : 3 ≤ p) :
    (2 : K) * (((p - 1) / 2 : ℕ) : K) + 1 = 0 := by
  obtain ⟨k, hk⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hn : 2 * ((p - 1) / 2) + 1 = p := by omega
  have h := congrArg (Nat.cast (R := K)) hn
  push_cast at h
  simpa only [CharP.cast_eq_zero K p] using h

/-- Parameters (1/2, 1/3, 5/6), with denominators cleared. -/
theorem gPolynomial_equation_mod_six_one (hp5 : 5 ≤ p) (hp6 : p % 6 = 1) :
    (6 : K[X]) * (X * (1 - X)) * derivative (derivative (gPolynomial p)) +
      (5 - 11 * X) * derivative (gPolynomial p) - gPolynomial p = 0 := by
  let m := (p - 1) / 2
  let s := (p + 1) / 6
  have hm : (2 : K) * m + 1 = 0 := cast_half_index p (by omega)
  have hn : 6 * s + 1 = p := by dsimp [s]; omega
  have hs : (6 : K) * s + 1 = 0 := by
    have h := congrArg (Nat.cast (R := K)) hn
    push_cast at h
    simpa only [CharP.cast_eq_zero K p] using h
  have hc : (6 : K) * ((s : K) + 1) = 5 := by linear_combination hs
  have hab : (6 : K) * (-(m : K) + ((s : K) - m) + 1) = 11 := by
    linear_combination hs - 6 * hm
  have hp : (6 : K) * (-(m : K) * ((s : K) - m)) = 1 := by
    linear_combination (3 * (m : K) - 1) * hm - (m : K) * hs
  simpa only [map_ofNat, map_one, one_mul] using
    scaled_hypergeometric_equation (-(m : K)) ((s : K) - m) ((s : K) + 1)
      6 5 11 1 (gPolynomial p) hc hab hp (gPolynomial_hypergeometric p Fact.out (by omega))

/-- Parameters (1/2, 2/3, 7/6), with denominators cleared. -/
theorem gPolynomial_equation_mod_six_five (hp5 : 5 ≤ p) (hp6 : p % 6 = 5) :
    (6 : K[X]) * (X * (1 - X)) * derivative (derivative (gPolynomial p)) +
      (7 - 13 * X) * derivative (gPolynomial p) - 2 * gPolynomial p = 0 := by
  let m := (p - 1) / 2
  let s := (p + 1) / 6
  have hm : (2 : K) * m + 1 = 0 := cast_half_index p (by omega)
  have hn : 6 * s = p + 1 := by dsimp [s]; omega
  have hs : (6 : K) * s - 1 = 0 := by
    have h := congrArg (Nat.cast (R := K)) hn
    push_cast at h
    rw [CharP.cast_eq_zero K p] at h
    linear_combination h
  have hc : (6 : K) * ((s : K) + 1) = 7 := by linear_combination hs
  have hab : (6 : K) * (-(m : K) + ((s : K) - m) + 1) = 13 := by
    linear_combination hs - 6 * hm
  have hp : (6 : K) * (-(m : K) * ((s : K) - m)) = 2 := by
    linear_combination (3 * (m : K) - 2) * hm - (m : K) * hs
  simpa only [map_ofNat] using
    scaled_hypergeometric_equation (-(m : K)) ((s : K) - m) ((s : K) + 1)
      6 7 13 2 (gPolynomial p) hc hab hp (gPolynomial_hypergeometric p Fact.out (by omega))

/-- Parameters (1/2, 1/4, 3/4), with denominators cleared. -/
theorem hPolynomial_equation_mod_four_one (hp3 : 3 ≤ p) (hp4 : p % 4 = 1) :
    (8 : K[X]) * (X * (1 - X)) * derivative (derivative (hPolynomial p)) +
      (6 - 14 * X) * derivative (hPolynomial p) - hPolynomial p = 0 := by
  let m := (p - 1) / 2
  let s := (p + 1) / 4
  have hm : (2 : K) * m + 1 = 0 := cast_half_index p hp3
  have hn : 4 * s + 1 = p := by dsimp [s]; omega
  have hs : (4 : K) * s + 1 = 0 := by
    have h := congrArg (Nat.cast (R := K)) hn
    push_cast at h
    simpa only [CharP.cast_eq_zero K p] using h
  have hc : (8 : K) * ((s : K) + 1) = 6 := by linear_combination 2 * hs
  have hab : (8 : K) * (-(m : K) + ((s : K) - m) + 1) = 14 := by
    linear_combination 2 * hs - 8 * hm
  have hp : (8 : K) * (-(m : K) * ((s : K) - m)) = 1 := by
    linear_combination (4 * (m : K) - 1) * hm - 2 * (m : K) * hs
  simpa only [map_ofNat, map_one, one_mul] using
    scaled_hypergeometric_equation (-(m : K)) ((s : K) - m) ((s : K) + 1)
      8 6 14 1 (hPolynomial p) hc hab hp (hPolynomial_hypergeometric p Fact.out hp3)

/-- Parameters (1/2, 3/4, 5/4), with denominators cleared. -/
theorem hPolynomial_equation_mod_four_three (hp3 : 3 ≤ p) (hp4 : p % 4 = 3) :
    (8 : K[X]) * (X * (1 - X)) * derivative (derivative (hPolynomial p)) +
      (10 - 18 * X) * derivative (hPolynomial p) - 3 * hPolynomial p = 0 := by
  let m := (p - 1) / 2
  let s := (p + 1) / 4
  have hm : (2 : K) * m + 1 = 0 := cast_half_index p hp3
  have hn : 4 * s = p + 1 := by dsimp [s]; omega
  have hs : (4 : K) * s - 1 = 0 := by
    have h := congrArg (Nat.cast (R := K)) hn
    push_cast at h
    rw [CharP.cast_eq_zero K p] at h
    linear_combination h
  have hc : (8 : K) * ((s : K) + 1) = 10 := by linear_combination 2 * hs
  have hab : (8 : K) * (-(m : K) + ((s : K) - m) + 1) = 18 := by
    linear_combination 2 * hs - 8 * hm
  have hp : (8 : K) * (-(m : K) * ((s : K) - m)) = 3 := by
    linear_combination (4 * (m : K) - 3) * hm - 2 * (m : K) * hs
  simpa only [map_ofNat] using
    scaled_hypergeometric_equation (-(m : K)) ((s : K) - m) ((s : K) + 1)
      8 10 18 3 (hPolynomial p) hc hab hp (hPolynomial_hypergeometric p Fact.out hp3)

end SupersingularCurves.IKO
