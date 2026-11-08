/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import Mathlib

/-!
# Newton polygons of valued polynomials

The polygon is the lower boundary of the convex hull of the points
`(i, v(aᵢ))` for nonzero coefficients. It is a set of rational points on the
polygonal graph, not an arbitrary list of slopes. Zero coefficients are omitted.
For rational coefficients `padic` uses the genuine p-adic valuation, normalized
by an explicit positive extension degree `r` (so `v(p^r) = 1`).

`ofEndomorphism` applies this construction to the reverse characteristic
polynomial. This is the convention with positive slopes for reciprocal roots.
Attaching such an endomorphism to a curve's crystalline cohomology is a separate
geometric theorem, not an assumption hidden in this definition.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.NewtonPolygon
open Polynomial Set

/-- Lowest points in each vertical fibre of a set. -/
def lowerBoundary (s : Set (ℚ × ℚ)) : Set (ℚ × ℚ) :=
  {P | P ∈ s ∧ ∀ Q ∈ s, Q.1 = P.1 → P.2 ≤ Q.2}

/-- Nonzero coefficient points; the value assigned to zero is never used. -/
def coefficientPoints {R : Type*} [Semiring R] (v : R → ℚ) (f : R[X]) : Set (ℚ × ℚ) :=
  {P | ∃ i : ℕ, f.coeff i ≠ 0 ∧ P = ((i : ℚ), v (f.coeff i))}

/-- The lower convex polygon of the valued coefficients. -/
def ofPolynomial {R : Type*} [Semiring R] (v : R → ℚ) (f : R[X]) : Set (ℚ × ℚ) :=
  lowerBoundary (convexHull ℚ (coefficientPoints v f))

/-- The p-adic valuation divided by `r`, for a base field of cardinality `p^r`. -/
def normalizedValuation (p r : ℕ) (a : ℚ) : ℚ := (padicValRat p a : ℚ) / r

/-- Normalized p-adic Newton polygon of a rational polynomial. -/
def padic (p : ℕ) [Fact p.Prime] (r : ℕ) [NeZero r] (f : ℚ[X]) : Set (ℚ × ℚ) :=
  ofPolynomial (normalizedValuation p r) f

/-- The slope-one-half polygon in dimension `g`, from `(0,0)` to `(2g,g)`. -/
def supersingular (g : ℕ) : Set (ℚ × ℚ) :=
  segment ℚ (0, 0) ((2 * g : ℕ), (g : ℚ))

/-- Having the supersingular shape is a condition on a polygon. No assertion
about an abelian variety follows until its Frobenius polygon is identified. -/
def HasSupersingularShape (g : ℕ) (N : Set (ℚ × ℚ)) : Prop := N = supersingular g

theorem lowerBoundary_subset (s : Set (ℚ × ℚ)) : lowerBoundary s ⊆ s :=
  fun _ h => h.1

theorem lowerBoundary_vertical_unique {s : Set (ℚ × ℚ)}
    {P Q : ℚ × ℚ} (hP : P ∈ lowerBoundary s) (hQ : Q ∈ lowerBoundary s)
    (hx : P.1 = Q.1) : P = Q := by
  apply Prod.ext hx
  exact le_antisymm (hP.2 Q hQ.1 hx.symm) (hQ.2 P hP.1 hx)

/-- Convex combinations preserve an affine equation. -/
theorem convex_affineLine (m b : ℚ) :
    Convex ℚ {P : ℚ × ℚ | P.2 = m * P.1 + b} := by
  intro P hP Q hQ a c ha hc hac
  change a * P.2 + c * Q.2 = m * (a * P.1 + c * Q.1) + b
  change P.2 = m * P.1 + b at hP
  change Q.2 = m * Q.1 + b at hQ
  rw [hP, hQ]
  nlinarith [congrArg (fun z : ℚ => z * b) hac]

theorem lowerBoundary_convexHull_of_affine {s : Set (ℚ × ℚ)} {m b : ℚ}
    (h : ∀ P ∈ s, P.2 = m * P.1 + b) :
    lowerBoundary (convexHull ℚ s) = convexHull ℚ s := by
  have hline : ∀ P ∈ convexHull ℚ s, P.2 = m * P.1 + b :=
    fun P hP => convexHull_min h (convex_affineLine m b) hP
  apply Set.Subset.antisymm (lowerBoundary_subset _)
  intro P hP
  refine ⟨hP, fun Q hQ hx => ?_⟩
  rw [hline P hP, hline Q hQ, hx]

/-- A pair of coefficient points with different abscissas gives exactly its segment. -/
theorem lowerBoundary_convexHull_pair {P Q : ℚ × ℚ} (hx : P.1 ≠ Q.1) :
    lowerBoundary (convexHull ℚ {P, Q}) = segment ℚ P Q := by
  rw [lowerBoundary_convexHull_of_affine
    (m := (Q.2 - P.2) / (Q.1 - P.1))
    (b := P.2 - (Q.2 - P.2) / (Q.1 - P.1) * P.1)]
  · exact convexHull_pair P Q
  · intro R hR
    rcases Set.mem_insert_iff.mp hR with rfl | hR
    · ring
    · have hRQ := Set.mem_singleton_iff.mp hR
      subst R
      have hd : Q.1 - P.1 ≠ 0 := sub_ne_zero.mpr hx.symm
      field_simp
      <;> ring

theorem coefficientPoints_binomial (v : ℚ → ℚ) {n : ℕ} (hn : n ≠ 0)
    {a : ℚ} (ha : a ≠ 0) :
    coefficientPoints v (1 + C a * X ^ n) = {(0, v 1), ((n : ℚ), v a)} := by
  ext P
  constructor
  · rintro ⟨i, hi, rfl⟩
    by_cases h0 : i = 0
    · subst i
      simp [coeff_add, coeff_one, hn, Ne.symm hn]
    · by_cases hin : i = n
      · subst i
        simp [coeff_add, coeff_one, hn, Ne.symm hn]
      · simp [coeff_add, coeff_one, h0, hin, Ne.symm hin] at hi
  · intro hP
    rcases Set.mem_insert_iff.mp hP with rfl | hP
    · exact ⟨0, by simp [coeff_add, coeff_one, hn, Ne.symm hn],
        by simp [coeff_add, coeff_one, hn, Ne.symm hn]⟩
    · obtain rfl := Set.mem_singleton_iff.mp hP
      exact ⟨n, by simpa [coeff_add, coeff_one, hn, Ne.symm hn] using ha,
        by simp [coeff_add, coeff_one, hn, Ne.symm hn]⟩

theorem ofPolynomial_binomial (v : ℚ → ℚ) {n : ℕ} (hn : n ≠ 0)
    {a : ℚ} (ha : a ≠ 0) :
    ofPolynomial v (1 + C a * X ^ n) = segment ℚ (0, v 1) ((n : ℚ), v a) := by
  rw [ofPolynomial, coefficientPoints_binomial v hn ha]
  apply lowerBoundary_convexHull_pair
  simpa using (Nat.cast_ne_zero.mpr hn : (n : ℚ) ≠ 0).symm

theorem normalizedValuation_one (p r : ℕ) : normalizedValuation p r 1 = 0 := by
  simp [normalizedValuation, padicValRat.one]

theorem normalizedValuation_prime_pow (p : ℕ) [Fact p.Prime]
    (r : ℕ) [NeZero r] (g : ℕ) :
    normalizedValuation p r ((p : ℚ) ^ (r * g)) = g := by
  have hr : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  simp only [normalizedValuation, padicValRat.pow, padicValRat.self (Fact.out : p.Prime).one_lt]
  push_cast
  field_simp

/-- A proved family of slope-one-half polynomial Newton polygons in every
positive dimension, with arbitrary finite-field normalization. -/
theorem padic_binomial_supersingular (p : ℕ) [Fact p.Prime]
    (r : ℕ) [NeZero r] {g : ℕ} (hg : g ≠ 0) :
    padic p r (1 + C ((p : ℚ) ^ (r * g)) * X ^ (2 * g)) = supersingular g := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [padic, ofPolynomial_binomial _ (Nat.mul_ne_zero (by decide) hg) (pow_ne_zero _ hp),
    normalizedValuation_one, normalizedValuation_prime_pow]
  rfl

theorem supersingular_half_slope (g : ℕ) {P : ℚ × ℚ}
    (hP : P ∈ supersingular g) : P.2 = P.1 / 2 := by
  have h : ∀ Q ∈ ({(0, 0), (((2 * g : ℕ) : ℚ), (g : ℚ))} : Set (ℚ × ℚ)),
      Q.2 = (1 / 2 : ℚ) * Q.1 + 0 := by
    intro Q hQ
    rcases Set.mem_insert_iff.mp hQ with rfl | hQ
    · norm_num
    · obtain rfl := Set.mem_singleton_iff.mp hQ
      push_cast
      ring
  have hline := convexHull_min h (convex_affineLine (1 / 2) 0)
  rw [convexHull_pair] at hline
  have he := hline hP
  change P.2 = (1 / 2 : ℚ) * P.1 + 0 at he
  linarith

/-- A genuine linear-algebra construction from an endomorphism. -/
def ofEndomorphism (p : ℕ) [Fact p.Prime] (r : ℕ) [NeZero r]
    {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (F : Module.End ℚ V) : Set (ℚ × ℚ) :=
  padic p r F.charpoly.reverse

/-- Changing the vector-space coordinates does not change this Newton polygon. -/
theorem ofEndomorphism_conj (p : ℕ) [Fact p.Prime] (r : ℕ) [NeZero r]
    {V W : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (e : V ≃ₗ[ℚ] W) (F : Module.End ℚ V) :
    ofEndomorphism p r (e.conj F) = ofEndomorphism p r F := by
  simp only [ofEndomorphism, LinearEquiv.charpoly_conj]

end SupersingularCurves.NewtonPolygon
