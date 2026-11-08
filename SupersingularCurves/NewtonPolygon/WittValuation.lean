/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.NewtonPolygon.Basic

/-!
# The actual discrete valuation on the fraction field of Witt vectors

This supplies the coefficient valuation for isocrystal Newton polygons. It is
the valuation associated to the maximal ideal of the Witt-vector DVR, normalized
so that the order of p is one. The value assigned to zero is immaterial to the
Newton polygon because zero coefficients are omitted.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.NewtonPolygon
open Polynomial WittVector IsDiscreteValuationRing
open scoped Isocrystal WithZero

variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [CharP k p] [PerfectRing k p]

/-- The genuine discrete valuation of `Frac(W(k))` at its maximal ideal. -/
def wittValuation : Valuation K(p, k) ℤᵐ⁰ :=
  (IsDiscreteValuationRing.maximalIdeal (WittVector p k)).valuation K(p, k)

/-- Additive order, obtained from the genuine multiplicative valuation. -/
def wittOrder (x : K(p, k)) : ℚ := -((WithZero.log (wittValuation p k x) : ℤ) : ℚ)

theorem wittValuation_prime :
    wittValuation p k (p : K(p, k)) = WithZero.exp (-1 : ℤ) := by
  change (IsDiscreteValuationRing.maximalIdeal (WittVector p k)).valuation K(p, k)
    (p : K(p, k)) = _
  rw [← map_natCast (algebraMap (WittVector p k) K(p, k)) p,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  apply (IsDiscreteValuationRing.maximalIdeal (WittVector p k)).intValuation_singleton
    (WittVector.irreducible p (k := k)).ne_zero
  exact (WittVector.irreducible p (k := k)).maximalIdeal_eq

@[simp] theorem wittOrder_one : wittOrder p k 1 = 0 := by
  simp [wittOrder]

@[simp] theorem wittOrder_prime : wittOrder p k (p : K(p, k)) = 1 := by
  simp [wittOrder, wittValuation_prime]

@[simp] theorem wittOrder_neg (x : K(p, k)) : wittOrder p k (-x) = wittOrder p k x := by
  simp [wittOrder]

theorem wittOrder_pow (x : K(p, k)) (n : ℕ) :
    wittOrder p k (x ^ n) = (n : ℚ) * wittOrder p k x := by
  simp [wittOrder, map_pow, WithZero.log_pow]

theorem wittOrder_zpow (x : K(p, k)) (n : ℤ) :
    wittOrder p k (x ^ n) = (n : ℚ) * wittOrder p k x := by
  simp [wittOrder, map_zpow₀, WithZero.log_zpow]

@[simp] theorem wittOrder_prime_zpow (n : ℤ) :
    wittOrder p k ((p : K(p, k)) ^ n) = n := by
  rw [wittOrder_zpow, wittOrder_prime, mul_one]

/-- The previous coefficient-hull construction, now over the actual Witt field. -/
def witt (r : ℕ) [NeZero r] (f : K(p, k)[X]) : Set (ℚ × ℚ) :=
  ofPolynomial (fun a => wittOrder p k a / r) f

end SupersingularCurves.NewtonPolygon
