/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.IKO.GeometricObstructions
import SupersingularCurves.IKO.SimpleRoots

/-!
# Finite geometric superspecial parameter loci

The sets below use superspeciality of the actual smooth proper curves. The
root counts proved in checkpoint 10 now bound these geometric parameter sets.
Only containment and upper bounds are claimed; equality requires the missing
converse to the geometric obstruction. Parameters are not isomorphism classes.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SupersingularCurves.IKO
open Polynomial

variable {K : Type*} [Field K] [IsAlgClosed K] [NeZero (2 : K)]
  (p : ℕ) [Fact p.Prime] [CharP K p]

/-- Admissible parameters whose family-A curve is geometrically superspecial. -/
def familyASuperspecialParameters : Set K :=
  {t | ∃ (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1),
    Geometry.CurveModel.IsSuperspecial p (familyACurve t h3 ht0 ht1)}

/-- Admissible parameters whose family-B curve is geometrically superspecial. -/
def familyBSuperspecialParameters : Set K :=
  {t | ∃ (ht0 : t ≠ 0) (ht1 : t ≠ 1),
    Geometry.CurveModel.IsSuperspecial p (familyBCurve t ht0 ht1)}

theorem familyASuperspecialParameters_subset_roots (hp5 : 5 ≤ p) :
    familyASuperspecialParameters (K := K) p ⊆
      ↑(gPolynomial p : K[X]).roots.toFinset := by
  rintro t ⟨h3, ht0, ht1, h⟩
  apply Multiset.mem_toFinset.mpr
  apply (Polynomial.mem_roots (fun hz =>
    gPolynomial_eval_zero_ne_zero (K := K) p hp5 (by rw [hz]; simp))).mpr
  exact familyA_isSuperspecial_imp_root p hp5 t h3 ht0 ht1 h

theorem familyBSuperspecialParameters_subset_roots (hp3 : 3 ≤ p) :
    familyBSuperspecialParameters (K := K) p ⊆
      ↑(hPolynomial p : K[X]).roots.toFinset := by
  rintro t ⟨ht0, ht1, h⟩
  apply Multiset.mem_toFinset.mpr
  apply (Polynomial.mem_roots (fun hz =>
    hPolynomial_eval_zero_ne_zero (K := K) p hp3 (by rw [hz]; simp))).mpr
  exact familyB_isSuperspecial_imp_root p hp3 t ht0 ht1 h

theorem familyASuperspecialParameters_finite (hp5 : 5 ≤ p) :
    (familyASuperspecialParameters (K := K) p).Finite :=
  (Finset.finite_toSet _).subset (familyASuperspecialParameters_subset_roots p hp5)

theorem familyBSuperspecialParameters_finite (hp3 : 3 ≤ p) :
    (familyBSuperspecialParameters (K := K) p).Finite :=
  (Finset.finite_toSet _).subset (familyBSuperspecialParameters_subset_roots p hp3)

/-- An upper bound for actual geometric superspecial parameters, not a count
of isomorphism classes and not an assertion that every root is superspecial. -/
theorem ncard_familyASuperspecialParameters_le (hp5 : 5 ≤ p) :
    (familyASuperspecialParameters (K := K) p).ncard ≤ p / 3 := by
  have h := Set.ncard_le_ncard (familyASuperspecialParameters_subset_roots (K := K) p hp5)
    (Finset.finite_toSet _)
  simpa only [Set.ncard_coe_finset, card_roots_gPolynomial p hp5] using h

theorem ncard_familyBSuperspecialParameters_le (hp3 : 3 ≤ p) :
    (familyBSuperspecialParameters (K := K) p).ncard ≤ p / 4 := by
  have h := Set.ncard_le_ncard (familyBSuperspecialParameters_subset_roots (K := K) p hp3)
    (Finset.finite_toSet _)
  simpa only [Set.ncard_coe_finset, card_roots_hPolynomial p hp3] using h

end SupersingularCurves.IKO
