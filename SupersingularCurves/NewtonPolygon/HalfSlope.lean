/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.NewtonPolygon.Isocrystal

/-!
# The standard slope-one-half F-isocrystal

The Frobenius is `(x,y) ↦ (σ(y), p σ(x))` on the actual Witt fraction field.
It is a bijective semilinear map, not a matrix over the residue field. Over the
prime field its Newton polygon is proved from its Frobenius characteristic
polynomial and the actual Witt valuation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SupersingularCurves.NewtonPolygon
open WittVector Polynomial Matrix
open scoped Isocrystal

variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [CharP k p] [PerfectRing k p]

/-- The underlying two-dimensional Witt vector space. -/
def HalfSlope : Type _ := K(p, k) × K(p, k)
  deriving AddCommGroup, Module K(p, k)

instance halfSlopeIsocrystal : Isocrystal p k (HalfSlope p k) where
  toModule := inferInstanceAs (Module K(p, k) (K(p, k) × K(p, k)))
  frob :=
    { toFun := fun x => (φ(p, k) x.2, (p : K(p, k)) * φ(p, k) x.1)
      invFun := fun x =>
        ((WittVector.FractionRing.frobenius p k).symm ((p : K(p, k))⁻¹ * x.2),
         (WittVector.FractionRing.frobenius p k).symm x.1)
      left_inv := by
        rintro ⟨x, y⟩
        apply Prod.ext <;> simp [WittVector.FractionRing.frobeniusRingHom,
          WittVector.FractionRing.p_nonzero p k]
      right_inv := by
        rintro ⟨x, y⟩
        apply Prod.ext <;> simp [WittVector.FractionRing.frobeniusRingHom,
          WittVector.FractionRing.p_nonzero p k]
      map_add' := by
        rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
        change (φ(p, k) (x₂ + y₂), (p : K(p, k)) * φ(p, k) (x₁ + y₁)) =
          (φ(p, k) x₂ + φ(p, k) y₂,
           (p : K(p, k)) * φ(p, k) x₁ + (p : K(p, k)) * φ(p, k) y₁)
        simp [map_add, mul_add]
      map_smul' := by
        rintro a ⟨x, y⟩
        change (φ(p, k) (a * y), (p : K(p, k)) * φ(p, k) (a * x)) =
          (φ(p, k) a * φ(p, k) y, φ(p, k) a * ((p : K(p, k)) * φ(p, k) x))
        apply Prod.ext <;> simp [map_mul] <;> ring }

instance halfSlopeFiniteDimensional : FiniteDimensional K(p, k) (HalfSlope p k) :=
  inferInstanceAs (FiniteDimensional K(p, k) (K(p, k) × K(p, k)))

theorem halfSlope_finrank : Module.finrank K(p, k) (HalfSlope p k) = 2 := by
  change Module.finrank K(p, k) (K(p, k) × K(p, k)) = 2
  simp

theorem halfSlope_frobenius_apply (x : HalfSlope p k) :
    Φ(p, k) x = (φ(p, k) x.2, (p : K(p, k)) * φ(p, k) x.1) := rfl

/-- The standard block has F² equal to p times scalar Frobenius squared. -/
theorem halfSlope_frobenius_twice (x : HalfSlope p k) :
    Φ(p, k) (Φ(p, k) x) =
      ((p : K(p, k)) * φ(p, k) (φ(p, k) x.1),
       (p : K(p, k)) * φ(p, k) (φ(p, k) x.2)) := by
  simp only [halfSlope_frobenius_apply, map_mul, map_natCast]

theorem fractionFrobenius_primeField (x : K(p, ZMod p)) : φ(p, ZMod p) x = x := by
  simpa using fractionFrobenius_iterate p (ZMod p) (r := 1) (by simp) x

/-- Standard coordinates with the isocrystal type retained in the codomain. -/
def halfSlopeBasisEquiv : (Fin 2 → K(p, k)) ≃ₗ[K(p, k)] HalfSlope p k :=
  LinearEquiv.finTwoArrow K(p, k) K(p, k)

/-- The actual prime-field Frobenius, in the standard two-vector basis. -/
theorem halfSlope_frobeniusPower_conj :
    (halfSlopeBasisEquiv p (ZMod p)).conj
      (!![0, 1; (p : K(p, ZMod p)), 0] : Matrix (Fin 2) (Fin 2) K(p, ZMod p)).toLin' =
      (frobeniusPower p (ZMod p) (V := HalfSlope p (ZMod p)) 1 (by simp)).toLinearMap := by
  apply LinearMap.ext
  intro x
  change (((!![0, 1; (p : K(p, ZMod p)), 0] *ᵥ ![x.1, x.2]) 0),
    ((!![0, 1; (p : K(p, ZMod p)), 0] *ᵥ ![x.1, x.2]) 1)) =
    (φ(p, ZMod p) x.2, (p : K(p, ZMod p)) * φ(p, ZMod p) x.1)
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, fractionFrobenius_primeField]

theorem halfSlope_frobeniusPower_charpoly :
    (frobeniusPower p (ZMod p) (V := HalfSlope p (ZMod p)) 1 (by simp)).toLinearMap.charpoly =
      X ^ 2 - C (p : K(p, ZMod p)) := by
  rw [← halfSlope_frobeniusPower_conj, LinearEquiv.charpoly_conj, Matrix.charpoly_toLin']
  simp [Matrix.charpoly_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two, sub_eq_add_neg]

/-- Coefficient-hull formula over any field, needed for Witt coefficients. -/
theorem coefficientPoints_binomial_general {R : Type*} [Field R]
    (v : R → ℚ) {n : ℕ} (hn : n ≠ 0) {a : R} (ha : a ≠ 0) :
    coefficientPoints v (1 + C a * X ^ n) = {(0, v 1), ((n : ℚ), v a)} := by
  ext P
  constructor
  · rintro ⟨i, hi, rfl⟩
    by_cases h0 : i = 0
    · subst i; simp [coeff_add, coeff_one, Ne.symm hn]
    · by_cases hin : i = n
      · subst i; simp [coeff_add, coeff_one, hn]
      · simp [coeff_add, coeff_one, h0, hin] at hi
  · intro hP
    rcases Set.mem_insert_iff.mp hP with rfl | hP
    · exact ⟨0, by simp [coeff_add, coeff_one, Ne.symm hn],
        by simp [coeff_add, coeff_one, Ne.symm hn]⟩
    · obtain rfl := Set.mem_singleton_iff.mp hP
      exact ⟨n, by simpa [coeff_add, coeff_one, hn] using ha,
        by simp [coeff_add, coeff_one, hn]⟩

theorem ofPolynomial_binomial_general {R : Type*} [Field R]
    (v : R → ℚ) {n : ℕ} (hn : n ≠ 0) {a : R} (ha : a ≠ 0) :
    ofPolynomial v (1 + C a * X ^ n) = segment ℚ (0, v 1) ((n : ℚ), v a) := by
  rw [ofPolynomial, coefficientPoints_binomial_general v hn ha]
  apply lowerBoundary_convexHull_pair
  simpa using (Nat.cast_ne_zero.mpr hn : (n : ℚ) ≠ 0).symm

/-- A Newton polygon computed from an actual semilinear F-isocrystal. -/
theorem halfSlope_newton :
    ofIsocrystal p (ZMod p) 1 (by simp) (HalfSlope p (ZMod p)) = supersingular 1 := by
  unfold ofIsocrystal
  rw [halfSlope_frobeniusPower_charpoly]
  have hrev : (X ^ 2 - C (p : K(p, ZMod p))).reverse =
      1 + C (-(p : K(p, ZMod p))) * X ^ 2 := by
    have h1 : (1 : K(p, ZMod p)[X]).reverse = 1 := by
      simpa only [Polynomial.C_1] using reverse_C (1 : K(p, ZMod p))
    have hx : (X ^ 2 : K(p, ZMod p)[X]).reverse = 1 := by
      simpa only [mul_one, h1] using reverse_X_pow_mul (1 : K(p, ZMod p)[X]) 2
    rw [sub_eq_add_neg, ← map_neg, reverse_add_C]
    simp [hx]
  rw [hrev, witt, ofPolynomial_binomial_general _ (by decide : 2 ≠ 0)
    (neg_ne_zero.mpr (WittVector.FractionRing.p_nonzero p (ZMod p)))]
  simp only [wittOrder_one, wittOrder_neg, wittOrder_prime, Nat.cast_one, div_one]
  rfl

end SupersingularCurves.NewtonPolygon
