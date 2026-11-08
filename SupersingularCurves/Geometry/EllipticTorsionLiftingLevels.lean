/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.EllipticTorsionRealizationDivisibility

/-!
# The actual consecutive torsion levels

For an actual abelian variety this constructs multiplication
A[n*m] → A[n] as the base change of [m]. In particular A[p²] → A[p]
is finite, faithfully flat, and has degree p^(2g) even in characteristic p.
Its identity fibre is the actual multiplication-by-m kernel.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.TorsionLevels
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian
open scoped CategoryTheory.MonObj

variable {K : Type u} [Field K] {g : ℕ} (A : AbelianVariety K g)

private theorem pow_left {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (n : ℕ) (x : Over.mk t ⟶ A.group.X) :
    (x ^ n).left = x.left ≫ (GroupScheme.law A.group).schemeNsmul n := by
  have h := congrArg Subtype.val (GroupScheme.nsmul_eq_pow A.group t n x)
  rw [SchemeFrobenius.nsmul_point] at h
  exact h.symm

/-- Multiplication maps compose with their actual scheme structure. -/
theorem multiplication_comp (n m : ℕ) :
    (GroupScheme.law A.group).schemeNsmul n ≫
      (GroupScheme.law A.group).schemeNsmul m =
        (GroupScheme.law A.group).schemeNsmul (n * m) := by
  have h := congrArg (fun f : A.group.X ⟶ A.group.X => f.left)
    (pow_mul (𝟙 A.group.X) n m)
  rw [pow_left, pow_left, pow_left] at h
  change 𝟙 A.group.X.left ≫ (GroupScheme.law A.group).schemeNsmul (n * m) =
    (𝟙 A.group.X.left ≫ (GroupScheme.law A.group).schemeNsmul n) ≫
      (GroupScheme.law A.group).schemeNsmul m at h
  rw [Category.id_comp, Category.id_comp] at h
  exact h.symm

abbrev kernel (n : ℕ) : Scheme.{u} := (GroupScheme.law A.group).schemeKer n
abbrev base (n : ℕ) : kernel A n ⟶ Spec (CommRingCat.of K) :=
  (GroupScheme.law A.group).schemeKerStr n
abbrev inclusion (n : ℕ) : kernel A n ⟶ A.group.X.left :=
  pullback.fst ((GroupScheme.law A.group).schemeNsmul n) (GroupScheme.zero A.group).1

theorem inclusion_over (n : ℕ) : inclusion A n ≫ A.group.X.hom = base A n := by
  rw [← (GroupScheme.law A.group).schemeNsmul_over n, ← Category.assoc]
  change (pullback.fst _ _ ≫ (GroupScheme.law A.group).schemeNsmul n) ≫ _ = _
  rw [pullback.condition, Category.assoc, (GroupScheme.zero A.group).2,
    Category.comp_id]
  rfl

/-- Multiplication by m on the actual nm-torsion, including nonreduced points. -/
def multiplication (n m : ℕ) : kernel A (n * m) ⟶ kernel A n :=
  pullback.lift (inclusion A (n * m) ≫ (GroupScheme.law A.group).schemeNsmul m)
    (base A (n * m)) (by
      rw [Category.assoc, multiplication_comp, Nat.mul_comm m n]
      exact pullback.condition)

@[reassoc (attr := simp)]
theorem multiplication_inclusion (n m : ℕ) :
    multiplication A n m ≫ inclusion A n =
      inclusion A (n * m) ≫ (GroupScheme.law A.group).schemeNsmul m :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem multiplication_over (n m : ℕ) :
    multiplication A n m ≫ base A n = base A (n * m) :=
  pullback.lift_snd _ _ _

/-- The consecutive-level projection is a scheme-theoretic base change of [m]. -/
theorem multiplication_isPullback (n m : ℕ) :
    IsPullback (inclusion A (n * m)) (multiplication A n m)
      ((GroupScheme.law A.group).schemeNsmul m) (inclusion A n) := by
  apply IsPullback.of_bot (v₂₁ := base A n)
    (v₂₂ := (GroupScheme.law A.group).schemeNsmul n)
    (h₃₁ := (GroupScheme.zero A.group).1)
  · rw [multiplication_over, multiplication_comp, Nat.mul_comm m n]
    exact IsPullback.of_hasPullback _ _
  · exact (multiplication_inclusion A n m).symm
  · exact IsPullback.of_hasPullback _ _

/-- The actual identity in the n-torsion. -/
def zero (n : ℕ) : Spec (CommRingCat.of K) ⟶ kernel A n :=
  pullback.lift (GroupScheme.zero A.group).1 (𝟙 _) (by
    rw [Category.id_comp, ← SchemeFrobenius.nsmul_point]
    exact congrArg Subtype.val ((GroupScheme.law A.group).nsmul_unit (𝟙 _) n))

@[reassoc (attr := simp)]
theorem zero_inclusion (n : ℕ) : zero A n ≫ inclusion A n = (GroupScheme.zero A.group).1 :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem zero_over (n : ℕ) : zero A n ≫ base A n = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- The actual m-torsion lies in the nm-torsion. -/
def smallerToLarger (n m : ℕ) : kernel A m ⟶ kernel A (n * m) :=
  pullback.lift (inclusion A m) (base A m) (by
    rw [Nat.mul_comm n m, ← multiplication_comp, ← Category.assoc]
    change (pullback.fst _ _ ≫ (GroupScheme.law A.group).schemeNsmul m) ≫ _ = _
    rw [pullback.condition, Category.assoc]
    congr 1
    rw [← SchemeFrobenius.nsmul_point]
    exact congrArg Subtype.val ((GroupScheme.law A.group).nsmul_unit (𝟙 _) n))

@[reassoc (attr := simp)]
theorem smallerToLarger_inclusion (n m : ℕ) :
    smallerToLarger A n m ≫ inclusion A (n * m) = inclusion A m :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem smallerToLarger_over (n m : ℕ) :
    smallerToLarger A n m ≫ base A (n * m) = base A m :=
  pullback.lift_snd _ _ _

/-- The fibre over the identity of A[n*m] → A[n] is the actual A[m]. -/
theorem identity_fibre_isPullback (n m : ℕ) :
    IsPullback (smallerToLarger A n m) (base A m)
      (multiplication A n m) (zero A n) := by
  apply IsPullback.of_right (h₁₂ := inclusion A (n * m))
    (h₂₂ := inclusion A n) (v₁₃ := (GroupScheme.law A.group).schemeNsmul m)
  · rw [smallerToLarger_inclusion, zero_inclusion]
    exact IsPullback.of_hasPullback _ _
  · apply pullback.hom_ext (f := (GroupScheme.law A.group).schemeNsmul n)
      (g := (GroupScheme.zero A.group).1)
    · simp only [Category.assoc, multiplication_inclusion, smallerToLarger_inclusion_assoc,
        zero_inclusion]
      exact pullback.condition
    · change (smallerToLarger A n m ≫ multiplication A n m) ≫ base A n =
        (base A m ≫ zero A n) ≫ base A n
      rw [Category.assoc, multiplication_over, smallerToLarger_over, Category.assoc,
        zero_over, Category.comp_id]
  · exact multiplication_isPullback A n m

variable [IsAlgClosed K]

/-- Finiteness of the actual projection, with no invertibility restriction on m. -/
theorem multiplication_isFinite (n m : ℕ) (hm : m ≠ 0) :
    IsFinite (multiplication A n m) := by
  letI := (A.multiplication_finite_flat_degree m hm).2.2.1
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @IsFinite) (multiplication_isPullback A n m) inferInstance

theorem multiplication_flat (n m : ℕ) (hm : m ≠ 0) :
    Flat (multiplication A n m) := by
  letI := (A.multiplication_finite_flat_degree m hm).2.2.2.1
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @Flat) (multiplication_isPullback A n m) inferInstance

theorem multiplication_surjective (n m : ℕ) (hm : m ≠ 0) :
    Surjective (multiplication A n m) := by
  letI : Surjective ((GroupScheme.law A.group).schemeNsmul m) :=
    ⟨(A.multiplication_finite_flat_degree m hm).2.2.2.2.1⟩
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @Surjective) (multiplication_isPullback A n m) inferInstance

/-- The length of every fibre of the actual transition is m^(2g). -/
theorem multiplication_finrank (n m : ℕ) (hm : m ≠ 0) (x : kernel A n) :
    (multiplication A n m).finrank x = m ^ (2 * g) := by
  letI := (A.multiplication_finite_flat_degree m hm).2.2.1
  letI := (A.multiplication_finite_flat_degree m hm).2.2.2.1
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ (multiplication_isPullback A n m)]
  exact (A.multiplication_finite_flat_degree m hm).2.2.2.2.2 _

end SupersingularCurves.Geometry.TorsionLevels
