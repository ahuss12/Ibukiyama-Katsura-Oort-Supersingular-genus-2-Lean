/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Differentials.Hyperelliptic
import SupersingularCurves.IKO.MatrixCriteria

/-!
# IKO's matrix acts on actual differentials

The coordinate map sends (a,b) to a dx/y + b x dx/y. We prove that it
intertwines the constructed Cartier operator and the semilinear IKO matrix.
Under explicit transcendence and nonvanishing assumptions it is injective.
Consequently the matrix criteria apply to this two-dimensional span of
rational differentials. No assertion about a basis of *all regular*
differentials, or about Jacobians, is built into these statements.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.IKO

open AlgebraicCurve KaehlerDifferential Polynomial Matrix
open SupersingularCurves.Differentials

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Coordinates in the span of the actual forms dx/y and x dx/y. -/
def differentialCombination (x y : F) : (Fin 2 → K) →ₗ[K] Ω[F⁄K] where
  toFun v := v 0 • (y⁻¹ • D K F x) + v 1 • (x • (y⁻¹ • D K F x))
  map_add' := by
    intro v w
    simp only [Pi.add_apply, add_smul]
    abel
  map_smul' := by
    intro a v
    simp [smul_add, smul_smul]

/-- Transcendence and dx ≠ 0 prove independence of these two rational forms. -/
theorem differentialCombination_eq_zero_iff (x y : F)
    (htr : Transcendental K x) (hdx : D K F x ≠ 0) (hy0 : y ≠ 0)
    (v : Fin 2 → K) : differentialCombination x y v = 0 ↔ v = 0 := by
  constructor
  · intro hv
    have hω : y⁻¹ • D K F x ≠ 0 := smul_ne_zero (inv_ne_zero hy0) hdx
    have hz : aeval x (C (v 0) + C (v 1) * X) • (y⁻¹ • D K F x) = 0 := by
      simpa [differentialCombination, map_add, map_mul, aeval_C, aeval_X,
        add_smul, mul_smul, algebraMap_smul] using hv
    have hc : aeval x (C (v 0) + C (v 1) * X) = 0 :=
      (smul_eq_zero.mp hz).resolve_right hω
    have hpoly : C (v 0) + C (v 1) * X = (0 : K[X]) :=
      (transcendental_iff_injective.mp htr) (by simpa using hc)
    ext i
    fin_cases i
    · have h := congrArg (fun q : K[X] => q.coeff 0) hpoly
      simpa using h
    · have h := congrArg (fun q : K[X] => q.coeff 1) hpoly
      simpa using h
  · rintro rfl
    exact map_zero _

theorem differentialCombination_injective (x y : F)
    (htr : Transcendental K x) (hdx : D K F x ≠ 0) (hy0 : y ≠ 0) :
    Function.Injective (differentialCombination (K := K) x y) := by
  intro v w h
  apply sub_eq_zero.mp
  apply (differentialCombination_eq_zero_iff x y htr hdx hy0 (v - w)).mp
  rw [map_sub, h, sub_self]

variable [PerfectField K] [IsCurveOver K F]
  (p : ℕ) [Fact p.Prime] [CharP K p]
  (x : F) [FiniteDimensional (IntermediateField.adjoin K {x}) F]

/-- The IKO coefficient matrix computes the actual Cartier action on this span. -/
theorem cartier_differentialCombination (hpodd : p % 2 = 1) (f : K[X])
    (hf : f.natDegree ≤ 6) (y : F) (hy : y ^ 2 = aeval x f) (hy0 : y ≠ 0)
    (v : Fin 2 → K) :
    cartier p x (differentialCombination x y v) =
      differentialCombination x y
        (semilinearAction (frobeniusEquiv K p) (coefficientMatrix p f) v) := by
  change cartier p x (v 0 • (y⁻¹ • D K F x) +
    v 1 • (x • (y⁻¹ • D K F x))) = _
  rw [map_add, cartier_smul, cartier_smul,
    cartier_dx_div_y_two_coefficients p x hpodd f hf y hy hy0,
    cartier_x_dx_div_y_two_coefficients p x hpodd f hf y hy hy0]
  simp [differentialCombination,
    semilinearAction, coefficientMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, add_smul, smul_add, smul_smul]
  module

/-- This two-dimensional rational differential span is stable under Cartier. -/
theorem cartier_mem_differentialSpan (hpodd : p % 2 = 1) (f : K[X])
    (hf : f.natDegree ≤ 6) (y : F) (hy : y ^ 2 = aeval x f) (hy0 : y ≠ 0)
    {ω : Ω[F⁄K]} (hω : ω ∈ LinearMap.range (differentialCombination (K := K) x y)) :
    cartier p x ω ∈ LinearMap.range (differentialCombination (K := K) x y) := by
  obtain ⟨v, rfl⟩ := hω
  exact ⟨_, (cartier_differentialCombination p x hpodd f hf y hy hy0 v).symm⟩

/-- Vanishing of actual Cartier on the displayed span is equivalent to M = 0. -/
theorem cartier_differentialSpan_zero_iff (hpodd : p % 2 = 1) (f : K[X])
    (hf : f.natDegree ≤ 6) (y : F) (hy : y ^ 2 = aeval x f) (hy0 : y ≠ 0)
    (htr : Transcendental K x) (hdx : D K F x ≠ 0) :
    (∀ v : Fin 2 → K, cartier p x (differentialCombination x y v) = 0) ↔
      coefficientMatrix p f = 0 := by
  simp only [cartier_differentialCombination p x hpodd f hf y hy hy0,
    differentialCombination_eq_zero_iff x y htr hdx hy0]
  exact semilinearAction_zero_iff _ _

/-- Squaring actual Cartier gives the Frobenius-twisted matrix product. -/
theorem cartier_differentialSpan_square_zero_iff (hpodd : p % 2 = 1) (f : K[X])
    (hf : f.natDegree ≤ 6) (y : F) (hy : y ^ 2 = aeval x f) (hy0 : y ≠ 0)
    (htr : Transcendental K x) (hdx : D K F x ≠ 0) :
    (∀ v : Fin 2 → K, cartier p x (cartier p x (differentialCombination x y v)) = 0) ↔
      (coefficientMatrix p f).map (fun a => a ^ p) * coefficientMatrix p f = 0 := by
  simp only [cartier_differentialCombination p x hpodd f hf y hy hy0,
    differentialCombination_eq_zero_iff x y htr hdx hy0]
  rw [semilinearAction_square_zero_iff, frobenius_twistMatrix]

end SupersingularCurves.IKO
