/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Portions adapted from work Copyright (c) 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.IKO.BinomialPolynomial
import SupersingularCurves.IKO.Polynomials

/-!
# IKO Proposition 1.14: simple roots of g and h

We follow the differential-equation proof in IKO Section 1.4. The binomial
coefficient recurrence proves equation (1.31) directly for the unnormalized
polynomials. This is valid because the differential equation is homogeneous.
The auxiliary gamma-function presentation is not needed for the algebraic
proof. The alternative geometric argument in Remark 1.15 is not used.

The final distinct-root count proofs use the same separability-to-cardinality
argument as the vendored Deuring-polynomial proof; see the provenance record.
-/

set_option autoImplicit false
noncomputable section
namespace SupersingularCurves.IKO
open Polynomial
variable {K : Type*} [Field K]

theorem gPolynomial_eq_binomialPolynomial (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    (gPolynomial p : K[X]) = binomialPolynomial ((p - 1) / 2) ((p + 1) / 6) := by
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two (by omega)
  have hn : p / 3 = (p - 1) / 2 - (p + 1) / 6 := by omega
  simp only [gPolynomial, binomialPolynomial, hn, map_mul]

theorem hPolynomial_eq_binomialPolynomial (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    (hPolynomial p : K[X]) = binomialPolynomial ((p - 1) / 2) ((p + 1) / 4) := by
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two (by omega)
  have hn : p / 4 = (p - 1) / 2 - (p + 1) / 4 := by omega
  simp only [hPolynomial, binomialPolynomial, hn, map_mul]

theorem gPolynomial_hypergeometric (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    hypergeometricOp (-(((p - 1) / 2 : ℕ) : K))
      ((((p + 1) / 6 : ℕ) : K) - ((p - 1) / 2 : ℕ))
      ((((p + 1) / 6 : ℕ) : K) + 1) 0 (gPolynomial p) = 0 := by
  rw [gPolynomial_eq_binomialPolynomial p hp hp3]
  exact hypergeometricOp_binomialPolynomial _ _

theorem hPolynomial_hypergeometric (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    hypergeometricOp (-(((p - 1) / 2 : ℕ) : K))
      ((((p + 1) / 4 : ℕ) : K) - ((p - 1) / 2 : ℕ))
      ((((p + 1) / 4 : ℕ) : K) + 1) 0 (hPolynomial p) = 0 := by
  rw [hPolynomial_eq_binomialPolynomial p hp hp3]
  exact hypergeometricOp_binomialPolynomial _ _

variable (p : ℕ) [Fact p.Prime] [CharP K p]

/-- IKO Proposition 1.14, family (a), over any field of the given characteristic. -/
theorem gPolynomial_separable (hp5 : 5 ≤ p) : (gPolynomial p : K[X]).Separable := by
  rw [gPolynomial_eq_binomialPolynomial p Fact.out (by omega)]
  apply binomialPolynomial_separable p
  · omega
  · omega

/-- IKO Proposition 1.14, family (b), including characteristic three. -/
theorem hPolynomial_separable (hp3 : 3 ≤ p) : (hPolynomial p : K[X]).Separable := by
  rw [hPolynomial_eq_binomialPolynomial p Fact.out hp3]
  apply binomialPolynomial_separable p
  · omega
  · omega

theorem natDegree_gPolynomial (hp5 : 5 ≤ p) : (gPolynomial p : K[X]).natDegree = p / 3 := by
  rw [gPolynomial_eq_binomialPolynomial p Fact.out (by omega),
    natDegree_binomialPolynomial p _ _ (by omega) (by omega)]
  obtain ⟨k, hk⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  omega

theorem natDegree_hPolynomial (hp3 : 3 ≤ p) : (hPolynomial p : K[X]).natDegree = p / 4 := by
  rw [hPolynomial_eq_binomialPolynomial p Fact.out hp3,
    natDegree_binomialPolynomial p _ _ (by omega) (by omega)]
  obtain ⟨k, hk⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  omega

theorem gPolynomial_eval_zero_ne_zero (hp5 : 5 ≤ p) :
    (gPolynomial p : K[X]).eval 0 ≠ 0 := by
  rw [gPolynomial_eq_binomialPolynomial p Fact.out (by omega), eval_zero_binomialPolynomial]
  exact cast_choose_ne_zero_of_lt p (by omega) (by omega)

theorem hPolynomial_eval_zero_ne_zero (hp3 : 3 ≤ p) :
    (hPolynomial p : K[X]).eval 0 ≠ 0 := by
  rw [hPolynomial_eq_binomialPolynomial p Fact.out hp3, eval_zero_binomialPolynomial]
  exact cast_choose_ne_zero_of_lt p (by omega) (by omega)

theorem gPolynomial_eval_one_ne_zero (hp5 : 5 ≤ p) :
    (gPolynomial p : K[X]).eval 1 ≠ 0 := by
  rw [gPolynomial_eq_binomialPolynomial p Fact.out (by omega),
    eval_one_binomialPolynomial _ _ (by omega)]
  exact cast_choose_ne_zero_of_lt p (by omega) (by omega)

theorem hPolynomial_eval_one_ne_zero (hp3 : 3 ≤ p) :
    (hPolynomial p : K[X]).eval 1 ≠ 0 := by
  rw [hPolynomial_eq_binomialPolynomial p Fact.out hp3,
    eval_one_binomialPolynomial _ _ (by omega)]
  exact cast_choose_ne_zero_of_lt p (by omega) (by omega)

theorem gPolynomial_root_admissible (hp5 : 5 ≤ p) {t : K}
    (ht : (gPolynomial p : K[X]).IsRoot t) : t ≠ 0 ∧ t ≠ 1 := by
  constructor
  · rintro rfl; exact gPolynomial_eval_zero_ne_zero p hp5 ht.eq_zero
  · rintro rfl; exact gPolynomial_eval_one_ne_zero p hp5 ht.eq_zero

theorem hPolynomial_root_admissible (hp3 : 3 ≤ p) {t : K}
    (ht : (hPolynomial p : K[X]).IsRoot t) : t ≠ 0 ∧ t ≠ 1 := by
  constructor
  · rintro rfl; exact hPolynomial_eval_zero_ne_zero p hp3 ht.eq_zero
  · rintro rfl; exact hPolynomial_eval_one_ne_zero p hp3 ht.eq_zero

theorem card_roots_gPolynomial [IsAlgClosed K] [DecidableEq K] (hp5 : 5 ≤ p) :
    (gPolynomial p : K[X]).roots.toFinset.card = p / 3 := by
  rw [Multiset.toFinset_card_of_nodup (nodup_roots (gPolynomial_separable p hp5)),
    ← natDegree_gPolynomial (K := K) p hp5]
  exact splits_iff_card_roots.mp (IsAlgClosed.splits _)

theorem card_roots_hPolynomial [IsAlgClosed K] [DecidableEq K] (hp3 : 3 ≤ p) :
    (hPolynomial p : K[X]).roots.toFinset.card = p / 4 := by
  rw [Multiset.toFinset_card_of_nodup (nodup_roots (hPolynomial_separable p hp3)),
    ← natDegree_hPolynomial (K := K) p hp3]
  exact splits_iff_card_roots.mp (IsAlgClosed.splits _)

end SupersingularCurves.IKO
