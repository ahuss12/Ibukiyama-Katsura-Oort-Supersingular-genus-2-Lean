/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.IKO.RegularBasis
import SupersingularCurves.IKO.FixedVectors
import SupersingularCurves.PicardTorsion.Equivalence
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_isAlgClosed

/-!
# Actual divisor-class p-torsion in the two IKO families

The complete regular bases and Cartier formulas identify the logarithmic
correspondence with the explicit matrix fixed sets. For admissible parameters
over an algebraically closed field the actual divisor-class p-torsion has
one element at a root of `gPolynomial` or `hPolynomial`, and `p^2` elements
otherwise. All field, genus, basis, regularity, and constant-field inputs
are proved for the constructed families.

These results concern the existing quotient of divisors by principal
divisors. They do not assert that a representing Jacobian has been
constructed, or that the geometric equivalences in IKO Lemma 1.1 are proved.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SupersingularCurves.IKO
open AlgebraicCurve KaehlerDifferential Matrix
open SupersingularCurves.Differentials SupersingularCurves.PicardTorsion

variable {K : Type*} [Field K]

private theorem prime_mod_six_torsion (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    p % 6 = 1 ∨ p % 6 = 5 := by
  have h2 : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr (by omega)
  have h3 : ¬3 ∣ p := by
    intro h
    have := (Nat.dvd_prime hp).mp h
    omega
  omega

section Coordinates
variable {F : Type*} [Field F] [Algebra K F]
  [PerfectField K] [IsCurveOver K F] (p : ℕ) [Fact p.Prime] [CharP K p]
  (x : F) [FiniteDimensional (IntermediateField.adjoin K {x}) F]

/-- A proved full regular basis transports Cartier fixed points additively. -/
def regularFixedCoordinatesEquiv
    (e : (Fin 2 → K) ≃ₗ[K] regularDifferentials K F)
    (M : Matrix (Fin 2) (Fin 2) K)
    (hcompat : ∀ ω, e.symm (regularCartier p x ω) =
      semilinearAction (frobeniusEquiv K p) M (e.symm ω)) :
    regularFixed (K := K) p x ≃+ fixedVectors p M where
  toFun ω := ⟨e.symm ω.val, by
    change semilinearAction (frobeniusEquiv K p) M (e.symm ω.val) = e.symm ω.val
    rw [← hcompat, (mem_regularFixed_iff p x ω.val).mp ω.property]⟩
  invFun v := ⟨e v.val, by
    apply (mem_regularFixed_iff p x _).mpr
    apply e.symm.injective
    rw [hcompat, LinearEquiv.symm_apply_apply]
    exact v.property⟩
  left_inv ω := Subtype.ext (e.apply_symm_apply ω.val)
  right_inv v := Subtype.ext (e.symm_apply_apply v.val)
  map_add' ω η := Subtype.ext (e.symm.map_add ω.val η.val)
end Coordinates

variable [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]

theorem card_familyA_fixedVectors (hp5 : 5 ≤ p) (t : K) (ht0 : t ≠ 0) :
    Nat.card (fixedVectors p (coefficientMatrix p (familyA t))) =
      if (gPolynomial p).eval t = 0 then 1 else p ^ 2 := by
  by_cases hg : (gPolynomial p).eval t = 0
  · rw [if_pos hg, (coefficientMatrix_familyA_zero_iff p Fact.out hp5 t).mpr hg]
    exact card_fixedVectors_zero p
  · rw [if_neg hg]
    rcases prime_mod_six_torsion p Fact.out hp5 with hc | hc
    · rw [coefficientMatrix_familyA_formula_one p (by omega) hc]
      exact card_fixedVectors_diagonal p _ _ (mul_ne_zero (pow_ne_zero _ ht0) hg) hg
    · rw [coefficientMatrix_familyA_formula_five p hc]
      exact card_fixedVectors_antidiagonal p _ _
        (neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ ht0) hg)) (neg_ne_zero.mpr hg)

theorem card_familyB_fixedVectors (hp3 : 3 ≤ p) (t : K) (ht0 : t ≠ 0) :
    Nat.card (fixedVectors p (coefficientMatrix p (familyB t))) =
      if (hPolynomial p).eval t = 0 then 1 else p ^ 2 := by
  by_cases hh : (hPolynomial p).eval t = 0
  · rw [if_pos hh, (coefficientMatrix_familyB_zero_iff p Fact.out hp3 t).mpr hh]
    exact card_fixedVectors_zero p
  · rw [if_neg hh]
    have hs : (-1 : K) ^ (p / 4) * (hPolynomial p).eval t ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hh
    have hp2 : p % 2 = 1 :=
      (Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr (by omega)
    have hc : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases hc with hc | hc
    · rw [coefficientMatrix_familyB_formula_one p hp3 hc]
      exact card_fixedVectors_diagonal p _ _ (mul_ne_zero (pow_ne_zero _ ht0) hs) hs
    · rw [coefficientMatrix_familyB_formula_three p hc]
      exact card_fixedVectors_antidiagonal p _ _ (mul_ne_zero (pow_ne_zero _ ht0) hs) hs

variable [NeZero (2 : K)]

omit p [Fact p.Prime] [CharP K p] in
theorem familyA_constantsAreBase (t : K) (h3 : (3 : K) ≠ 0) (ht1 : t ≠ 1) :
    ConstantsAreBase K (familyAModel t h3 ht1).FunctionField := by
  classical
  exact constantsAreBase_of_isAlgClosed K (familyAModel t h3 ht1).FunctionField

omit p [Fact p.Prime] [CharP K p] in
theorem familyB_constantsAreBase (t : K) (ht0 : t ≠ 0) :
    ConstantsAreBase K (familyBModel t ht0).FunctionField := by
  classical
  exact constantsAreBase_of_isAlgClosed K (familyBModel t ht0).FunctionField

/-- An additive equivalence from the independently defined p-torsion quotient
to the explicit fixed vectors, with no basis or constant-field assumption. -/
def familyATorsionEquiv (hp5 : 5 ≤ p) (t : K)
    (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    Pic0.torsion K (familyAModel t h3 ht1).FunctionField p ≃+
      fixedVectors p (coefficientMatrix p (familyA t)) :=
  (logarithmEquiv p (familyAModel t h3 ht1).x (familyA_constantsAreBase t h3 ht1)).trans
    (regularFixedCoordinatesEquiv p (familyAModel t h3 ht1).x
      (familyARegularEquiv t h3 ht0 ht1) _
      (familyA_regularCartier_coordinates p hp5 t h3 ht0 ht1))

def familyBTorsionEquiv (hp3 : 3 ≤ p) (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    Pic0.torsion K (familyBModel t ht0).FunctionField p ≃+
      fixedVectors p (coefficientMatrix p (familyB t)) :=
  (logarithmEquiv p (familyBModel t ht0).x (familyB_constantsAreBase t ht0)).trans
    (regularFixedCoordinatesEquiv p (familyBModel t ht0).x
      (familyBRegularEquiv t ht0 ht1) _ (familyB_regularCartier_coordinates p hp3 t ht0 ht1))

/-- Exact cardinality of the actual degree-zero divisor-class p-torsion
for family A, for every prime at least five and admissible parameter. -/
theorem card_familyA_torsion (hp5 : 5 ≤ p) (t : K)
    (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    Nat.card (Pic0.torsion K (familyAModel t h3 ht1).FunctionField p) =
      if (gPolynomial p).eval t = 0 then 1 else p ^ 2 := by
  rw [Nat.card_congr (familyATorsionEquiv p hp5 t h3 ht0 ht1).toEquiv]
  exact card_familyA_fixedVectors p hp5 t ht0

/-- Exact cardinality for family B, including characteristic three. -/
theorem card_familyB_torsion (hp3 : 3 ≤ p) (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    Nat.card (Pic0.torsion K (familyBModel t ht0).FunctionField p) =
      if (hPolynomial p).eval t = 0 then 1 else p ^ 2 := by
  rw [Nat.card_congr (familyBTorsionEquiv p hp3 t ht0 ht1).toEquiv]
  exact card_familyB_fixedVectors p hp3 t ht0

/-- The positive cardinality is a genuine finite count, not the `Nat.card`
value zero that an infinite type would have. -/
theorem familyA_torsion_finite (hp5 : 5 ≤ p) (t : K)
    (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    Finite (Pic0.torsion K (familyAModel t h3 ht1).FunctionField p) := by
  apply Nat.finite_of_card_ne_zero
  rw [card_familyA_torsion p hp5 t h3 ht0 ht1]
  split_ifs <;> simp [(Fact.out : p.Prime).ne_zero]

theorem familyB_torsion_finite (hp3 : 3 ≤ p) (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    Finite (Pic0.torsion K (familyBModel t ht0).FunctionField p) := by
  apply Nat.finite_of_card_ne_zero
  rw [card_familyB_torsion p hp3 t ht0 ht1]
  split_ifs <;> simp [(Fact.out : p.Prime).ne_zero]

/-- Trivial actual p-torsion is characterized by the family-A parameter polynomial. -/
theorem familyA_torsion_eq_zero_iff (hp5 : 5 ≤ p) (t : K)
    (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (∀ q : Pic0.torsion K (familyAModel t h3 ht1).FunctionField p, q = 0) ↔
      (gPolynomial p).eval t = 0 := by
  have hcard := card_familyA_torsion p hp5 t h3 ht0 ht1
  constructor
  · intro hz
    have hc := Nat.card_eq_one_iff_exists.mpr ⟨0, hz⟩
    rw [hc] at hcard
    by_contra hg
    rw [if_neg hg] at hcard
    nlinarith
  · intro hg q
    rw [if_pos hg] at hcard
    exact (Nat.card_eq_one_iff_unique.mp hcard).1.elim q 0

theorem familyB_torsion_eq_zero_iff (hp3 : 3 ≤ p) (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (∀ q : Pic0.torsion K (familyBModel t ht0).FunctionField p, q = 0) ↔
      (hPolynomial p).eval t = 0 := by
  have hcard := card_familyB_torsion p hp3 t ht0 ht1
  constructor
  · intro hz
    have hc := Nat.card_eq_one_iff_exists.mpr ⟨0, hz⟩
    rw [hc] at hcard
    by_contra hh
    rw [if_neg hh] at hcard
    nlinarith
  · intro hh q
    rw [if_pos hh] at hcard
    exact (Nat.card_eq_one_iff_unique.mp hcard).1.elim q 0

/-- A special-family equivalence; it is not asserted for arbitrary curves. -/
theorem familyA_torsion_eq_zero_iff_regularCartier_zero (hp5 : 5 ≤ p) (t : K)
    (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (∀ q : Pic0.torsion K (familyAModel t h3 ht1).FunctionField p, q = 0) ↔
      ∀ ω : regularDifferentials K (familyAModel t h3 ht1).FunctionField,
        regularCartier p (familyAModel t h3 ht1).x ω = 0 := by
  rw [familyA_torsion_eq_zero_iff p hp5 t h3 ht0 ht1,
    familyA_all_regularCartier_zero_iff p hp5 t h3 ht0 ht1]

theorem familyB_torsion_eq_zero_iff_regularCartier_zero (hp3 : 3 ≤ p) (t : K)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (∀ q : Pic0.torsion K (familyBModel t ht0).FunctionField p, q = 0) ↔
      ∀ ω : regularDifferentials K (familyBModel t ht0).FunctionField,
        regularCartier p (familyBModel t ht0).x ω = 0 := by
  rw [familyB_torsion_eq_zero_iff p hp3 t ht0 ht1,
    familyB_all_regularCartier_zero_iff p hp3 t ht0 ht1]

end SupersingularCurves.IKO
