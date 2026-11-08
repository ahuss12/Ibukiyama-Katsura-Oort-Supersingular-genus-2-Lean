/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.JacobianConstruction
import SupersingularCurves.IKO.TorsionCriteria

/-!
# Actual Jacobians and their geometric p-torsion in the IKO families

The representing Jacobian and its group-compatible divisor-class identification
are constructed first. The earlier Cartier/divisor-class calculations then give
exact geometric point counts, p-ranks, and the ordinary locus of these actual
abelian varieties. The superspecial/isogeny classification is not an input.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SupersingularCurves.IKO
open AlgebraicCurve AlgebraicGeometry
open SupersingularCurves.Geometry SupersingularCurves.Differentials

variable {K : Type*} [Field K] [IsAlgClosed K] [NeZero (2 : K)]

/-- The family-A Picard-representing Jacobian, with its actual divisor-class map. -/
def familyAJacobian (t : K) (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    JacobianRealization (familyACurve t h3 ht0 ht1)
      (familyAModel t h3 ht1).curveModelBasepoint :=
  constructJacobian
    ⟨(familyAModel t h3 ht1).x, (familyAModel t h3 ht1).transcendental_x,
      (familyAModel t h3 ht1).finiteDimensional_coordinate⟩
    (familyACurve t h3 ht0 ht1) (familyAModel t h3 ht1).curveModelBasepoint

/-- The family-B Picard-representing Jacobian. -/
def familyBJacobian (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    JacobianRealization (familyBCurve t ht0 ht1)
      (familyBModel t ht0).curveModelBasepoint :=
  constructJacobian
    ⟨(familyBModel t ht0).x, (familyBModel t ht0).transcendental_x,
      (familyBModel t ht0).finiteDimensional_coordinate⟩
    (familyBCurve t ht0 ht1) (familyBModel t ht0).curveModelBasepoint

theorem familyAJacobian_dimension (t : K) (h3 : (3 : K) ≠ 0)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    SmoothOfRelativeDimension 2 (familyAJacobian t h3 ht0 ht1).jacobian.designation.toBase := by
  have h := (familyAJacobian t h3 ht0 ht1).jacobian.smooth
  rw [familyA_genus t h3 ht0 ht1] at h
  exact h

theorem familyBJacobian_dimension (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    SmoothOfRelativeDimension 2 (familyBJacobian t ht0 ht1).jacobian.designation.toBase := by
  have h := (familyBJacobian t ht0 ht1).jacobian.smooth
  rw [familyB_genus t ht0 ht1] at h
  exact h

variable (p : ℕ) [Fact p.Prime] [CharP K p]

/-- The earlier divisor-class count is now a count on an actual Jacobian. -/
theorem card_familyAJacobian_torsion (hp5 : 5 ≤ p) (t : K)
    (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    Nat.card ((familyAJacobian t h3 ht0 ht1).jacobian.abelianVariety.torsionPoints p) =
      if (gPolynomial p).eval t = 0 then 1 else p ^ 2 := by
  rw [card_torsionPoints_eq_picard _ (familyAJacobian t h3 ht0 ht1).picardPoints]
  exact card_familyA_torsion p hp5 t h3 ht0 ht1

theorem card_familyBJacobian_torsion (hp3 : 3 ≤ p) (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    Nat.card ((familyBJacobian t ht0 ht1).jacobian.abelianVariety.torsionPoints p) =
      if (hPolynomial p).eval t = 0 then 1 else p ^ 2 := by
  rw [card_torsionPoints_eq_picard _ (familyBJacobian t ht0 ht1).picardPoints]
  exact card_familyB_torsion p hp3 t ht0 ht1

theorem familyAJacobian_torsion_finite (hp5 : 5 ≤ p) (t : K)
    (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    Finite ((familyAJacobian t h3 ht0 ht1).jacobian.abelianVariety.torsionPoints p) := by
  apply Nat.finite_of_card_ne_zero
  rw [card_familyAJacobian_torsion p hp5 t h3 ht0 ht1]
  split_ifs <;> simp [(Fact.out : p.Prime).ne_zero]

theorem familyBJacobian_torsion_finite (hp3 : 3 ≤ p) (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    Finite ((familyBJacobian t ht0 ht1).jacobian.abelianVariety.torsionPoints p) := by
  apply Nat.finite_of_card_ne_zero
  rw [card_familyBJacobian_torsion p hp3 t ht0 ht1]
  split_ifs <;> simp [(Fact.out : p.Prime).ne_zero]

/-- The geometric p-rank of family A is zero or two, according to the parameter. -/
theorem familyAJacobian_pRank (hp5 : 5 ≤ p) (t : K)
    (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (familyAJacobian t h3 ht0 ht1).jacobian.abelianVariety.HasPRankOver p
      (if (gPolynomial p).eval t = 0 then 0 else 2) := by
  refine ⟨familyAJacobian_torsion_finite p hp5 t h3 ht0 ht1, ?_⟩
  rw [card_familyAJacobian_torsion p hp5 t h3 ht0 ht1]
  split_ifs <;> simp

theorem familyBJacobian_pRank (hp3 : 3 ≤ p) (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (familyBJacobian t ht0 ht1).jacobian.abelianVariety.HasPRankOver p
      (if (hPolynomial p).eval t = 0 then 0 else 2) := by
  refine ⟨familyBJacobian_torsion_finite p hp3 t ht0 ht1, ?_⟩
  rw [card_familyBJacobian_torsion p hp3 t ht0 ht1]
  split_ifs <;> simp

theorem familyAJacobian_pRank_zero_iff (hp5 : 5 ≤ p) (t : K)
    (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (familyAJacobian t h3 ht0 ht1).jacobian.abelianVariety.HasPRankOver p 0 ↔
      (gPolynomial p).eval t = 0 := by
  have hf := familyAJacobian_pRank p hp5 t h3 ht0 ht1
  constructor
  · intro hz
    have he := AbelianVariety.hasPRankOver_unique _ p hf hz
    by_contra h
    simp [h] at he
  · intro h
    simpa [h] using hf

theorem familyBJacobian_pRank_zero_iff (hp3 : 3 ≤ p) (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (familyBJacobian t ht0 ht1).jacobian.abelianVariety.HasPRankOver p 0 ↔
      (hPolynomial p).eval t = 0 := by
  have hf := familyBJacobian_pRank p hp3 t ht0 ht1
  constructor
  · intro hz
    have he := AbelianVariety.hasPRankOver_unique _ p hf hz
    by_contra h
    simp [h] at he
  · intro h
    simpa [h] using hf

/-- Ordinary locus of the actual family-A Jacobian, in the geometric p-rank definition. -/
theorem familyAJacobian_ordinary_iff (hp5 : 5 ≤ p) (t : K)
    (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (familyAJacobian t h3 ht0 ht1).jacobian.abelianVariety.IsOrdinaryOver p ↔
      (gPolynomial p).eval t ≠ 0 := by
  unfold AbelianVariety.IsOrdinaryOver
  have hr := congrArg ((familyAJacobian t h3 ht0 ht1).jacobian.abelianVariety.HasPRankOver p)
    (familyA_genus t h3 ht0 ht1)
  rw [hr]
  have hf := familyAJacobian_pRank p hp5 t h3 ht0 ht1
  constructor
  · intro ho h
    have he := AbelianVariety.hasPRankOver_unique _ p hf ho
    simp [h] at he
  · intro h
    simpa [h] using hf

theorem familyBJacobian_ordinary_iff (hp3 : 3 ≤ p) (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (familyBJacobian t ht0 ht1).jacobian.abelianVariety.IsOrdinaryOver p ↔
      (hPolynomial p).eval t ≠ 0 := by
  unfold AbelianVariety.IsOrdinaryOver
  have hr := congrArg ((familyBJacobian t ht0 ht1).jacobian.abelianVariety.HasPRankOver p)
    (familyB_genus t ht0 ht1)
  rw [hr]
  have hf := familyBJacobian_pRank p hp3 t ht0 ht1
  constructor
  · intro ho h
    have he := AbelianVariety.hasPRankOver_unique _ p hf ho
    simp [h] at he
  · intro h
    simpa [h] using hf

/-- A criterion on actual geometric p-torsion; no superspecial/isogeny classification is assumed. -/
theorem familyAJacobian_pRank_zero_iff_cartier_zero (hp5 : 5 ≤ p) (t : K)
    (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (familyAJacobian t h3 ht0 ht1).jacobian.abelianVariety.HasPRankOver p 0 ↔
      ∀ ω : regularDifferentials K (familyAModel t h3 ht1).FunctionField,
        regularCartier p (familyAModel t h3 ht1).x ω = 0 := by
  rw [familyAJacobian_pRank_zero_iff p hp5 t h3 ht0 ht1,
    familyA_all_regularCartier_zero_iff p hp5 t h3 ht0 ht1]

theorem familyBJacobian_pRank_zero_iff_cartier_zero (hp3 : 3 ≤ p) (t : K)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (familyBJacobian t ht0 ht1).jacobian.abelianVariety.HasPRankOver p 0 ↔
      ∀ ω : regularDifferentials K (familyBModel t ht0).FunctionField,
        regularCartier p (familyBModel t ht0).x ω = 0 := by
  rw [familyBJacobian_pRank_zero_iff p hp3 t ht0 ht1,
    familyB_all_regularCartier_zero_iff p hp3 t ht0 ht1]

end SupersingularCurves.IKO
