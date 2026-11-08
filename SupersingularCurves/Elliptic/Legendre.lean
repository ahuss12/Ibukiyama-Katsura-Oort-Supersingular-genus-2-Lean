/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Elliptic.Supersingular
import Theorems.Thm_WeierstrassCurve_hasseInvariant_legendreCurve
import Theorems.Thm_Polynomial_separable_deuringPolynomial_map

/-!
# The Legendre example over the ground field

The main theorem concerns a nonsingular Weierstrass curve, its geometric
p-torsion, and the explicit Deuring polynomial. All three are actual library
objects. Finite fields and perfect fields are included in the general field
statement. The sign and factor 4 follow the upstream Hasse normalization.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.Elliptic

open Polynomial WeierstrassCurve
open scoped Classical

variable {K : Type*} [Field K]

/-- The Deuring/Hasse polynomial, with integer coefficients reduced into K. -/
def hassePolynomial (p : ℕ) : K[X] :=
  (Polynomial.deuringPolynomial p).map (Int.castRingHom K)

theorem legendre_isElliptic (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp2 : p ≠ 2) (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (WeierstrassCurve.legendreCurve t).IsElliptic := by
  have h2 : (2 : K) ≠ 0 := by
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp
      ((CharP.cast_eq_zero_iff K p 2).mp h))
  exact P2MW.S_WeierstrassCurve_hasseInvariant_legendreCurve.WeierstrassCurve.isElliptic_legendreCurve
    t h2 ht0 ht1

/-- The geometric Legendre criterion; t = 0 and t = 1 are excluded explicitly. -/
theorem legendre_isSupersingular_iff (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp2 : p ≠ 2) (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    IsSupersingular p (WeierstrassCurve.legendreCurve t) ↔
      (hassePolynomial p : K[X]).eval t = 0 := by
  let := legendre_isElliptic p hp2 t ht0 ht1
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have h2 : (2 : K) ≠ 0 := by
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp
      ((CharP.cast_eq_zero_iff K p 2).mp h))
  have h4 : (-4 : K) ≠ 0 := by
    have h4' : (4 : K) = 2 ^ 2 := by ring
    rw [neg_ne_zero, h4']
    exact pow_ne_zero _ h2
  rw [isSupersingular_iff_hasseInvariant_eq_zero p hp2,
    WeierstrassCurve.hasseInvariant_legendreCurve hpodd]
  simp only [hassePolynomial, mul_eq_zero, pow_ne_zero _ h4, false_or]

theorem hassePolynomial_separable (p : ℕ) [Fact p.Prime] [CharP K p] :
    (hassePolynomial p : K[X]).Separable :=
  Polynomial.separable_deuringPolynomial_map p

/-- A concrete geometric example: y² = x³ - x in characteristic three. -/
theorem legendre_neg_one_supersingular_char_three [CharP K 3] :
    IsSupersingular 3 (WeierstrassCurve.legendreCurve (-1 : K)) := by
  have ht1 : (-1 : K) ≠ 1 := by
    intro h
    have h2 : (2 : K) = 0 := by linear_combination -h
    have : 3 ∣ 2 := (CharP.cast_eq_zero_iff K 3 2).mp h2
    norm_num at this
  rw [legendre_isSupersingular_iff 3 (by decide) (-1) (by simp) ht1]
  norm_num [hassePolynomial, Polynomial.deuringPolynomial, Finset.sum_range_succ]

end SupersingularCurves.Elliptic
