/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.IKO.RegularFamilies

/-!
# Coordinates inside the actual regular-differential space

The map below lands in regularDifferentials, not just rational differentials.
Its range has dimension two, and actual regular Cartier acts by the IKO
matrix. Surjectivity onto all regular differentials is not assumed or asserted.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.IKO

open AlgebraicCurve KaehlerDifferential Polynomial
open SupersingularCurves.Differentials SupersingularCurves.Hyperelliptic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def regularDifferentialCombination (x y : F)
    (h0 : y⁻¹ • D K F x ∈ regularDifferentials K F)
    (h1 : x • (y⁻¹ • D K F x) ∈ regularDifferentials K F) :
    (Fin 2 → K) →ₗ[K] regularDifferentials K F :=
  (differentialCombination x y).codRestrict (regularDifferentials K F)
    (fun v => (regularDifferentials K F).add_mem
      ((regularDifferentials K F).smul_mem (v 0) h0)
      ((regularDifferentials K F).smul_mem (v 1) h1))

theorem regularDifferentialCombination_coe (x y : F) (h0 h1) (v : Fin 2 → K) :
    (regularDifferentialCombination x y h0 h1 v : Ω[F⁄K]) =
      differentialCombination x y v := rfl

theorem regularDifferentialCombination_injective (x y : F) (h0 h1)
    (htr : Transcendental K x) (hdx : D K F x ≠ 0) (hy0 : y ≠ 0) :
    Function.Injective (regularDifferentialCombination (K := K) x y h0 h1) := by
  intro v w h
  exact differentialCombination_injective x y htr hdx hy0 (congrArg Subtype.val h)

theorem regularDifferentialCombination_finrank_range (x y : F) (h0 h1)
    (htr : Transcendental K x) (hdx : D K F x ≠ 0) (hy0 : y ≠ 0) :
    Module.finrank K (LinearMap.range (regularDifferentialCombination (K := K) x y h0 h1)) = 2 := by
  rw [LinearMap.finrank_range_of_inj
    (regularDifferentialCombination_injective x y h0 h1 htr hdx hy0)]
  simp

theorem regularCartier_differentialCombination [PerfectField K] [IsCurveOver K F]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (x : F) [FiniteDimensional (IntermediateField.adjoin K {x}) F]
    (hpodd : p % 2 = 1) (f : K[X]) (hf : f.natDegree ≤ 6)
    (y : F) (hy : y ^ 2 = aeval x f) (hy0 : y ≠ 0) (h0 h1) (v : Fin 2 → K) :
    regularCartier p x (regularDifferentialCombination x y h0 h1 v) =
      regularDifferentialCombination x y h0 h1
        (semilinearAction (frobeniusEquiv K p) (coefficientMatrix p f) v) := by
  apply Subtype.ext
  exact cartier_differentialCombination p x hpodd f hf y hy hy0 v

theorem familyAModel_pair_regular [PerfectField K]
    (t : K) (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    let a := familyAModel t h3 ht1
    a.y⁻¹ • D K a.FunctionField a.x ∈ regularDifferentials K a.FunctionField ∧
      a.x • (a.y⁻¹ • D K a.FunctionField a.x) ∈ regularDifferentials K a.FunctionField := by
  let a := familyAModel t h3 ht1
  exact familyA_pair_regular a.x t h3 ht0 ht1 a.y a.equation_in_functionField
    a.x_ne_zero a.y_ne_zero

theorem familyBModel_pair_regular [PerfectField K]
    (t : K) (h2 : (2 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    let a := familyBModel t ht0
    a.y⁻¹ • D K a.FunctionField a.x ∈ regularDifferentials K a.FunctionField ∧
      a.x • (a.y⁻¹ • D K a.FunctionField a.x) ∈ regularDifferentials K a.FunctionField := by
  let a := familyBModel t ht0
  exact familyB_pair_regular a.x t h2 ht0 ht1 a.y a.equation_in_functionField
    a.x_ne_zero a.y_ne_zero

def familyARegularCoordinates [PerfectField K]
    (t : K) (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (Fin 2 → K) →ₗ[K] regularDifferentials K (familyAModel t h3 ht1).FunctionField :=
  regularDifferentialCombination _ _ (familyAModel_pair_regular t h3 ht0 ht1).1
    (familyAModel_pair_regular t h3 ht0 ht1).2

def familyBRegularCoordinates [PerfectField K]
    (t : K) (h2 : (2 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (Fin 2 → K) →ₗ[K] regularDifferentials K (familyBModel t ht0).FunctionField :=
  regularDifferentialCombination _ _ (familyBModel_pair_regular t h2 ht0 ht1).1
    (familyBModel_pair_regular t h2 ht0 ht1).2

theorem familyARegularCoordinates_injective [PerfectField K] [NeZero (2 : K)]
    (t : K) (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    Function.Injective (familyARegularCoordinates t h3 ht0 ht1) :=
  regularDifferentialCombination_injective _ _ _ _
    (familyAModel t h3 ht1).transcendental_x (familyAModel t h3 ht1).dx_ne_zero
    (familyAModel t h3 ht1).y_ne_zero

theorem familyBRegularCoordinates_injective [PerfectField K] [NeZero (2 : K)]
    (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    Function.Injective (familyBRegularCoordinates t (NeZero.ne _) ht0 ht1) :=
  regularDifferentialCombination_injective _ _ _ _
    (familyBModel t ht0).transcendental_x (familyBModel t ht0).dx_ne_zero
    (familyBModel t ht0).y_ne_zero

theorem familyARegularCoordinates_finrank_range [PerfectField K] [NeZero (2 : K)]
    (t : K) (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    Module.finrank K (LinearMap.range (familyARegularCoordinates t h3 ht0 ht1)) = 2 := by
  rw [LinearMap.finrank_range_of_inj (familyARegularCoordinates_injective t h3 ht0 ht1)]
  simp

theorem familyBRegularCoordinates_finrank_range [PerfectField K] [NeZero (2 : K)]
    (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    Module.finrank K (LinearMap.range (familyBRegularCoordinates t (NeZero.ne _) ht0 ht1)) = 2 := by
  rw [LinearMap.finrank_range_of_inj (familyBRegularCoordinates_injective t ht0 ht1)]
  simp

/-- Cartier on the constructed family-(a) field, with regularity hypotheses discharged. -/
theorem familyA_regularCartier_action [PerfectField K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp5 : 5 ≤ p)
    (t : K) (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (v : Fin 2 → K) :
    regularCartier p (familyAModel t h3 ht1).x (familyARegularCoordinates t h3 ht0 ht1 v) =
      familyARegularCoordinates t h3 ht0 ht1
        (semilinearAction (frobeniusEquiv K p) (coefficientMatrix p (familyA t)) v) := by
  have hp : p.Prime := Fact.out
  exact regularCartier_differentialCombination p _
    (hp.mod_two_eq_one_iff_ne_two.mpr (by omega)) _ (natDegree_familyA_le t) _
    (familyAModel t h3 ht1).equation_in_functionField (familyAModel t h3 ht1).y_ne_zero _ _ v

theorem familyB_regularCartier_action [PerfectField K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp3 : 3 ≤ p)
    (t : K) (h2 : (2 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (v : Fin 2 → K) :
    regularCartier p (familyBModel t ht0).x (familyBRegularCoordinates t h2 ht0 ht1 v) =
      familyBRegularCoordinates t h2 ht0 ht1
        (semilinearAction (frobeniusEquiv K p) (coefficientMatrix p (familyB t)) v) := by
  have hp : p.Prime := Fact.out
  exact regularCartier_differentialCombination p _
    (hp.mod_two_eq_one_iff_ne_two.mpr (by omega)) _ (natDegree_familyB_le t) _
    (familyBModel t ht0).equation_in_functionField (familyBModel t ht0).y_ne_zero _ _ v

/-- This tests regular Cartier on the proved two-dimensional subspace, not on all forms. -/
theorem familyA_regularCartier_zero_iff [PerfectField K] [NeZero (2 : K)]
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp5 : 5 ≤ p)
    (t : K) (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (∀ v : Fin 2 → K, regularCartier p (familyAModel t h3 ht1).x
      (familyARegularCoordinates t h3 ht0 ht1 v) = 0) ↔ (gPolynomial p).eval t = 0 := by
  simp only [familyA_regularCartier_action p hp5 t h3 ht0 ht1,
    ← map_zero (familyARegularCoordinates t h3 ht0 ht1),
    (familyARegularCoordinates_injective t h3 ht0 ht1).eq_iff]
  exact familyA_semilinear_zero_iff _ p Fact.out hp5 t

theorem familyB_regularCartier_zero_iff [PerfectField K] [NeZero (2 : K)]
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp3 : 3 ≤ p)
    (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (∀ v : Fin 2 → K, regularCartier p (familyBModel t ht0).x
      (familyBRegularCoordinates t (NeZero.ne _) ht0 ht1 v) = 0) ↔ (hPolynomial p).eval t = 0 := by
  simp only [familyB_regularCartier_action p hp3 t (NeZero.ne _) ht0 ht1,
    ← map_zero (familyBRegularCoordinates t (NeZero.ne _) ht0 ht1),
    (familyBRegularCoordinates_injective t ht0 ht1).eq_iff]
  exact familyB_semilinear_zero_iff _ p Fact.out hp3 t

theorem familyA_regularCartier_square_zero_iff [PerfectField K] [NeZero (2 : K)]
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp5 : 5 ≤ p)
    (t : K) (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (∀ v : Fin 2 → K, regularCartier p (familyAModel t h3 ht1).x
      (regularCartier p (familyAModel t h3 ht1).x
        (familyARegularCoordinates t h3 ht0 ht1 v)) = 0) ↔ (gPolynomial p).eval t = 0 := by
  simp only [familyA_regularCartier_action p hp5 t h3 ht0 ht1,
    ← map_zero (familyARegularCoordinates t h3 ht0 ht1),
    (familyARegularCoordinates_injective t h3 ht0 ht1).eq_iff]
  exact familyA_semilinear_square_zero_iff _ p Fact.out hp5 t ht0

theorem familyB_regularCartier_square_zero_iff [PerfectField K] [NeZero (2 : K)]
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp3 : 3 ≤ p)
    (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (∀ v : Fin 2 → K, regularCartier p (familyBModel t ht0).x
      (regularCartier p (familyBModel t ht0).x
        (familyBRegularCoordinates t (NeZero.ne _) ht0 ht1 v)) = 0) ↔ (hPolynomial p).eval t = 0 := by
  simp only [familyB_regularCartier_action p hp3 t (NeZero.ne _) ht0 ht1,
    ← map_zero (familyBRegularCoordinates t (NeZero.ne _) ht0 ht1),
    (familyBRegularCoordinates_injective t ht0 ht1).eq_iff]
  exact familyB_semilinear_square_zero_iff _ p Fact.out hp3 t ht0

end SupersingularCurves.IKO
