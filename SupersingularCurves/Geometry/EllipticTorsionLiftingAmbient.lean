/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.EllipticTorsionLiftingSchemeComparison
import SupersingularCurves.Geometry.FrobeniusDifferentialTwist

/-!
# Actual ambient Verschiebung on consecutive torsion levels

Untwisting the already constructed relative Verschiebung gives the actual
inverse-Frobenius semilinear scheme endomorphism. It restricts to every
scheme-theoretic torsion level, compatibly with inclusion. The Frobenius
composition identity on the p-squared level is proved from ambient geometry.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.TorsionLevels
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GoodReductionJacobian SchemeFrobenius PerfectFieldVerschiebung

variable {K : Type u} [Field K] [IsAlgClosed K] {g : ℕ}
  (A : AbelianVariety K g) (p : ℕ) [Fact p.Prime] [CharP K p]

local instance : Smooth A.group.X.hom :=
  SmoothOfRelativeDimension.smooth g A.group.X.hom

/-- The actual ambient inverse-Frobenius semilinear Verschiebung. -/
def ambientVerschiebung : A.group.X.left ⟶ A.group.X.left :=
  inv (projection p A.group.X.hom) ≫
    PerfectFieldVerschiebung.verschiebung p A.group.X.hom (GroupScheme.law A.group)
      A.groupScheme_law_commutative

theorem absolute_ambientVerschiebung :
    absolute p A.group.X.hom ≫ ambientVerschiebung A p =
      (GroupScheme.law A.group).schemeNsmul p := by
  rw [ambientVerschiebung, ← relative_projection, Category.assoc,
    IsIso.hom_inv_id_assoc, frobenius_verschiebung]

theorem ambientVerschiebung_absolute :
    ambientVerschiebung A p ≫ absolute p A.group.X.hom =
      (GroupScheme.law A.group).schemeNsmul p := by
  rw [← absolute_ambientVerschiebung]
  exact (Scheme.frobenius_comp (ambientVerschiebung A p) p 1
    (Fact.out : p.Prime) _ _).symm

theorem ambientVerschiebung_over :
    ambientVerschiebung A p ≫ A.group.X.hom =
      A.group.X.hom ≫ inv (baseMap p K) := by
  rw [ambientVerschiebung, Category.assoc, verschiebung_over,
    inverse_projection_over, inverse_baseMap]

private instance ambientFrobenius_epi : Epi (absolute p A.group.X.hom) := by
  letI : Epi (relative p A.group.X.hom) := by
    letI := (finite_flat_surjective p A.group.X.hom).2.1
    letI := (finite_flat_surjective p A.group.X.hom).2.2.2
    exact Flat.epi_of_flat_of_surjective _
  rw [← relative_projection]
  infer_instance

/-- The ambient semilinear map commutes with all actual multiplication maps. -/
theorem multiplication_ambientVerschiebung (n : ℕ) :
    (GroupScheme.law A.group).schemeNsmul n ≫ ambientVerschiebung A p =
      ambientVerschiebung A p ≫ (GroupScheme.law A.group).schemeNsmul n := by
  apply (cancel_epi (absolute p A.group.X.hom)).mp
  have hf := Scheme.frobenius_comp ((GroupScheme.law A.group).schemeNsmul n)
    p 1 (Fact.out : p.Prime) (globalChar p A.group.X.hom) (globalChar p A.group.X.hom)
  change absolute p A.group.X.hom ≫ (GroupScheme.law A.group).schemeNsmul n =
    (GroupScheme.law A.group).schemeNsmul n ≫ absolute p A.group.X.hom at hf
  rw [← Category.assoc, hf, Category.assoc, absolute_ambientVerschiebung,
    ← Category.assoc, absolute_ambientVerschiebung, multiplication_comp,
    multiplication_comp, Nat.mul_comm n p]

/-- The identity section is preserved with the correct inverse field twist. -/
theorem zero_ambientVerschiebung :
    (GroupScheme.zero A.group).1 ≫ ambientVerschiebung A p =
      inv (baseMap p K) ≫ (GroupScheme.zero A.group).1 := by
  apply (cancel_epi (baseMap p K)).mp
  have hz := Scheme.frobenius_comp (GroupScheme.zero A.group).1 p 1
    (Fact.out : p.Prime) (Scheme.natCast_eq_zero_ΓSpec (CharP.cast_eq_zero K p))
    (globalChar p A.group.X.hom)
  rw [baseMap_eq_absolute] at hz
  change baseMap p K ≫ (GroupScheme.zero A.group).1 =
    (GroupScheme.zero A.group).1 ≫ absolute p A.group.X.hom at hz
  rw [← Category.assoc, hz, Category.assoc, absolute_ambientVerschiebung,
    IsIso.hom_inv_id_assoc, ← SchemeFrobenius.nsmul_point]
  exact congrArg Subtype.val ((GroupScheme.law A.group).nsmul_unit (𝟙 _) p)

/-- Actual semilinear Verschiebung restricted to the whole n-torsion scheme. -/
def ambientOnLevel (n : ℕ) : kernel A n ⟶ kernel A n :=
  pullback.lift (inclusion A n ≫ ambientVerschiebung A p)
    (base A n ≫ inv (baseMap p K)) (by
      rw [Category.assoc, ← multiplication_ambientVerschiebung, ← Category.assoc]
      change (pullback.fst _ _ ≫ (GroupScheme.law A.group).schemeNsmul n) ≫ _ = _
      rw [pullback.condition, Category.assoc, zero_ambientVerschiebung, Category.assoc]
      rfl)

@[reassoc (attr := simp)]
theorem ambientOnLevel_inclusion (n : ℕ) :
    ambientOnLevel A p n ≫ inclusion A n = inclusion A n ≫ ambientVerschiebung A p :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem ambientOnLevel_over (n : ℕ) :
    ambientOnLevel A p n ≫ base A n = base A n ≫ inv (baseMap p K) :=
  pullback.lift_snd _ _ _

/-- The actual ambient restrictions commute with the actual level inclusion. -/
theorem ambientOnLevel_smallerToLarger (n m : ℕ) :
    ambientOnLevel A p m ≫ smallerToLarger A n m =
      smallerToLarger A n m ≫ ambientOnLevel A p (n * m) := by
  apply (cancel_mono (inclusion A (n * m))).mp
  simp only [Category.assoc, smallerToLarger_inclusion, ambientOnLevel_inclusion,
    smallerToLarger_inclusion_assoc]

/-- Actual Frobenius followed by ambient Verschiebung on A[p²] is [p]. -/
theorem absolute_ambientOnSquare :
    absolute p (base A (p * p)) ≫ ambientOnLevel A p (p * p) =
      squareMultiplication A p := by
  apply (cancel_mono (inclusion A (p * p))).mp
  have hf := Scheme.frobenius_comp (inclusion A (p * p)) p 1
    (Fact.out : p.Prime) (globalChar p (base A (p * p))) (globalChar p A.group.X.hom)
  change absolute p (base A (p * p)) ≫ inclusion A (p * p) =
    inclusion A (p * p) ≫ absolute p A.group.X.hom at hf
  rw [Category.assoc, ambientOnLevel_inclusion, ← Category.assoc, hf,
    Category.assoc, absolute_ambientVerschiebung, squareMultiplication_inclusion]

/-- The remaining finite construction is uniquely determined once it is
natural for the actual projection and satisfies its canonical VF identity. -/
theorem ambientOnLevel_eq_of_canonical (W₁ : kernel A (p * p) ⟶ kernel A (p * p))
    (W₀ : kernel A p ⟶ kernel A p)
    (hW : multiplication A p p ≫ W₀ = W₁ ≫ multiplication A p p)
    (hWF : W₁ ≫ absolute p (base A (p * p)) = squareMultiplication A p) :
    ambientOnLevel A p p = W₀ :=
  eq_of_two_level_absoluteFrobenius A p (ambientOnLevel A p (p * p)) W₁
    (ambientOnLevel A p p) W₀ (ambientOnLevel_smallerToLarger A p p p)
    hW hWF (absolute_ambientOnSquare A p)

end SupersingularCurves.Geometry.TorsionLevels
