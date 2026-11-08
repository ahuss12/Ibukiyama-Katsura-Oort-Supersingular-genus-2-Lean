/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Hyperelliptic.FunctionField
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndex_eq_div_gcd_natAbs_ord_of_isSplittingField_X_pow_sub_C
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg

/-!
# Ramification of separable quadratic models

The Kummer and finite-fibre arguments generalize the user's earlier quartic
ramification construction. The branch set here is computed from the actual
roots of a separable polynomial of degree five or six, with infinity included.
-/

set_option autoImplicit false
noncomputable section
namespace SupersingularCurves.Hyperelliptic.SimpleRootModel
open Polynomial AlgebraicCurve AlgebraicCurve.RationalFunctionField
open scoped Classical
variable {K : Type*} [Field K] [IsAlgClosed K] [NeZero (2 : K)] (a : SimpleRootModel K)

local instance : IsCurveOver K (RatFunc K) := isCurveOver_ratFunc K
local instance : IsGalois (RatFunc K) a.FunctionField :=
  IsGalois.of_separable_splitting_field a.separable_polynomial
attribute [local instance] AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors

/-- Kummer ramification in the constructed quadratic field. -/
theorem ramificationIndex_formula (w : Place K a.FunctionField) :
    w.ramificationIndex (RatFunc K) =
      2 / Nat.gcd 2 ((w.restrict (RatFunc K)).ord a.radicand).natAbs := by
  letI : IsSplittingField (RatFunc K) a.FunctionField (X ^ 2 - C a.radicand) :=
    a.polynomial_eq ▸ a.splittingField
  exact w.ramificationIndex_eq_div_gcd_natAbs_ord_of_isSplittingField_X_pow_sub_C
    2 (NeZero.ne _) a.radicand a.radicand_ne_zero a.finrank_functionField

theorem rootMultiplicity_of_separable (hf : a.f.Separable) (c : K) :
    a.f.rootMultiplicity c = if a.f.IsRoot c then 1 else 0 := by
  classical
  split_ifs with hc
  · have hpos := (rootMultiplicity_pos hf.ne_zero).mpr hc
    have hle := rootMultiplicity_le_one_of_separable hf c
    omega
  · exact rootMultiplicity_eq_zero hc

theorem ramificationIndex_finite (hf : a.f.Separable) (c : K)
    (w : Place K a.FunctionField) (hw : w.restrict (RatFunc K) = placeOfPoint K c) :
    w.ramificationIndex (RatFunc K) = if a.f.IsRoot c then 2 else 1 := by
  classical
  rw [a.ramificationIndex_formula, hw, radicand,
    ord_placeOfPoint_algebraMap c hf.ne_zero, a.rootMultiplicity_of_separable hf c]
  split_ifs <;> norm_num

theorem ramificationIndex_infinity (hf : a.f.Separable)
    (hd : a.f.natDegree = 5 ∨ a.f.natDegree = 6)
    (w : Place K a.FunctionField) (hw : w.restrict (RatFunc K) = placeInfty K) :
    w.ramificationIndex (RatFunc K) = if a.f.natDegree = 5 then 2 else 1 := by
  classical
  rw [a.ramificationIndex_formula, hw, radicand,
    ord_placeInfty_algebraMap hf.ne_zero]
  rcases hd with hd | hd <;> norm_num [hd]

theorem ramificationIndex_one_or_two (hf : a.f.Separable)
    (hd : a.f.natDegree = 5 ∨ a.f.natDegree = 6) (w : Place K a.FunctionField) :
    w.ramificationIndex (RatFunc K) = 1 ∨ w.ramificationIndex (RatFunc K) = 2 := by
  classical
  rcases eq_placeOfPoint_or_eq_placeInfty K (w.restrict (RatFunc K)) with ⟨c, hc⟩ | hi
  · rw [a.ramificationIndex_finite hf c w hc]
    split_ifs <;> simp
  · rw [a.ramificationIndex_infinity hf hd w hi]
    split_ifs <;> simp

theorem tame (hf : a.f.Separable) (hd : a.f.natDegree = 5 ∨ a.f.natDegree = 6)
    (w : Place K a.FunctionField) : (w.ramificationIndex (RatFunc K) : K) ≠ 0 := by
  rcases a.ramificationIndex_one_or_two hf hd w with h | h
  · simp [h]
  · simpa [h] using (NeZero.ne (2 : K))

theorem inertiaDeg_eq_one (w : Place K a.FunctionField) :
    w.inertiaDeg (RatFunc K) = 1 := by
  have h := w.deg_restrict_mul_inertiaDeg (F := RatFunc K)
  simpa only [IsCurveOver.deg_eq_one_of_isAlgClosed, one_mul] using h

theorem sum_ramificationIndex_fiber (v : Place K (RatFunc K)) :
    ∑ w ∈ v.fiber a.FunctionField, (w.ramificationIndex (RatFunc K) : ℤ) = 2 := by
  have h := v.sum_ramificationIndex_mul_inertiaDeg (F' := a.FunctionField)
  simpa only [a.inertiaDeg_eq_one, Nat.cast_one, mul_one, a.finrank_functionField,
    Nat.cast_ofNat] using h

theorem card_fiber_mul_ramificationIndex (v : Place K (RatFunc K)) (e : ℕ)
    (he : ∀ w : Place K a.FunctionField, w.restrict (RatFunc K) = v →
      w.ramificationIndex (RatFunc K) = e) :
    (v.fiber a.FunctionField).card * e = 2 := by
  have h := a.sum_ramificationIndex_fiber v
  have hs : (∑ w ∈ v.fiber a.FunctionField, (w.ramificationIndex (RatFunc K) : ℤ)) =
      ((v.fiber a.FunctionField).card : ℤ) * e := by
    calc
      _ = ∑ _w ∈ v.fiber a.FunctionField, (e : ℤ) :=
        Finset.sum_congr rfl fun w hw => by rw [he w (Place.mem_fiber.mp hw)]
      _ = _ := by simp
  rw [hs] at h
  exact_mod_cast h

theorem card_fiber_root (hf : a.f.Separable) (c : K) (hc : a.f.IsRoot c) :
    ((placeOfPoint K c).fiber a.FunctionField).card = 1 := by
  have h := a.card_fiber_mul_ramificationIndex (placeOfPoint K c) 2
    (fun w hw => by rw [a.ramificationIndex_finite hf c w hw, if_pos hc])
  omega

theorem card_fiber_infinity (hf : a.f.Separable)
    (hd : a.f.natDegree = 5 ∨ a.f.natDegree = 6) :
    ((placeInfty K).fiber a.FunctionField).card = if a.f.natDegree = 5 then 1 else 2 := by
  have h := a.card_fiber_mul_ramificationIndex (placeInfty K)
    (if a.f.natDegree = 5 then 2 else 1) (a.ramificationIndex_infinity hf hd)
  split_ifs at * <;> omega

theorem ramification_contribution_fiber (v : Place K (RatFunc K)) :
    ∑ w ∈ v.fiber a.FunctionField, ((w.ramificationIndex (RatFunc K) : ℤ) - 1) =
      2 - (v.fiber a.FunctionField).card := by
  rw [Finset.sum_sub_distrib, a.sum_ramificationIndex_fiber]
  simp

/-- Finite roots and infinity; an unramified infinity contributes zero. -/
def branchPlaces : Finset (Place K (RatFunc K)) := by
  classical
  exact insert (placeInfty K) (a.f.roots.toFinset.image (placeOfPoint K))

theorem ramificationIndex_eq_one_outside (hf : a.f.Separable)
    (w : Place K a.FunctionField) (hw : w.restrict (RatFunc K) ∉ a.branchPlaces) :
    w.ramificationIndex (RatFunc K) = 1 := by
  classical
  rcases eq_placeOfPoint_or_eq_placeInfty K (w.restrict (RatFunc K)) with ⟨c, hc⟩ | hi
  · have hn : ¬ a.f.IsRoot c := by
      intro hr
      apply hw
      simp only [branchPlaces, hc, Finset.mem_insert, Finset.mem_image, Multiset.mem_toFinset]
      exact Or.inr ⟨c, (mem_roots hf.ne_zero).mpr hr, rfl⟩
    rw [a.ramificationIndex_finite hf c w hc, if_neg hn]
  · exact False.elim (hw (by simp [branchPlaces, hi]))

/-- The total ramification is six for a separable quintic or sextic. -/
theorem total_ramification (hf : a.f.Separable)
    (hd : a.f.natDegree = 5 ∨ a.f.natDegree = 6) :
    ∑ᶠ w : Place K a.FunctionField, ((w.ramificationIndex (RatFunc K) : ℤ) - 1) = 6 := by
  classical
  have hs : Function.support (fun w : Place K a.FunctionField =>
      (w.ramificationIndex (RatFunc K) : ℤ) - 1) ⊆
      (a.branchPlaces.biUnion fun v => v.fiber a.FunctionField : Finset _) := by
    intro w hw
    apply Finset.mem_biUnion.mpr
    refine ⟨w.restrict (RatFunc K), ?_, Place.mem_fiber.mpr rfl⟩
    by_contra hnot
    exact hw (by simp [a.ramificationIndex_eq_one_outside hf w hnot])
  have hdis : (a.branchPlaces : Set (Place K (RatFunc K))).PairwiseDisjoint
      (fun v => v.fiber a.FunctionField) := by
    intro v _ u _ hne
    apply Finset.disjoint_left.mpr
    intro w hv hu
    exact hne ((Place.mem_fiber.mp hv).symm.trans (Place.mem_fiber.mp hu))
  rw [finsum_eq_sum_of_support_subset _ hs, Finset.sum_biUnion hdis]
  simp_rw [a.ramification_contribution_fiber]
  have hinf : placeInfty K ∉ a.f.roots.toFinset.image (placeOfPoint K) := by
    simp only [Finset.mem_image, not_exists, not_and]
    intro c _ hc
    exact placeOfPoint_ne_placeInfty K c hc
  rw [branchPlaces, Finset.sum_insert hinf,
    Finset.sum_image (fun c _ d _ h => (placeOfPoint_injective K) h)]
  have hsum : (∑ c ∈ a.f.roots.toFinset,
      (2 - (((placeOfPoint K c).fiber a.FunctionField).card : ℤ))) = a.f.natDegree := by
    calc
      _ = ∑ _c ∈ a.f.roots.toFinset, (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [a.card_fiber_root hf c ((mem_roots hf.ne_zero).mp (Multiset.mem_toFinset.mp hc))]
        norm_num
      _ = _ := by
        simp [Multiset.toFinset_card_of_nodup (nodup_roots hf), IsAlgClosed.card_roots_eq_natDegree]
  rw [hsum, a.card_fiber_infinity hf hd]
  rcases hd with hd | hd <;> norm_num [hd]

end SupersingularCurves.Hyperelliptic.SimpleRootModel
