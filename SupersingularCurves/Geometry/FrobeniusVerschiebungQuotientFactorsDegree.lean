/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusVerschiebungQuotientDegree
import SupersingularCurves.Geometry.FrobeniusVerschiebungQuotientDescent
import SupersingularCurves.Geometry.FrobeniusFactorIsomorphism

/-!
# Degrees of the actual residual Frobenius and Verschiebung factors

The constructed finite-flat quotient factors both actual maps. Its residual
maps are finite, flat and surjective, and their degrees multiply with the
actual subgroup order to give p^g. For a p-rank-zero surface with nonzero
Verschiebung differential, both residual maps therefore have degree p.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open NeronModelInfra GoodReductionJacobian SchemeFrobenius PerfectFieldVerschiebung

variable {K : Type u} [Field K] [IsAlgClosed K]
  {p : ℕ} [Fact p.Prime] [CharP K p] {g : ℕ} {A : AbelianVariety K g}
  (D : QuotientData p A)

local instance source_smoothOfRelativeDimension : SmoothOfRelativeDimension g (base p A) :=
  (sourceAbelianVariety (p := p) (A := A)).smooth

local instance source_smooth : Smooth (base p A) :=
  SmoothOfRelativeDimension.smooth g (base p A)

instance frobeniusFactor_isFinite : IsFinite D.frobeniusFactor.1 := by
  have : IsProper (D.frobeniusFactor.1 ≫ SchemeFrobenius.toBase p (base p A)) := by
    rw [D.frobeniusFactor.2]
    infer_instance
  have : IsSeparated (SchemeFrobenius.toBase p (base p A)) := by
    change IsSeparated (pullback.snd (pullback.snd A.group.X.hom (baseMap p K))
      (baseMap p K))
    infer_instance
  have : IsProper D.frobeniusFactor.1 :=
    IsProper.of_comp D.frobeniusFactor.1 (SchemeFrobenius.toBase p (base p A))
  have : IsFinite (D.quotientMap ≫ D.frobeniusFactor.1) := by
    rw [D.quotientMap_frobeniusFactor]
    exact (finite_flat_surjective p (base p A)).1
  exact FiniteFlatFactor.isFinite D.quotientMap D.frobeniusFactor.1

instance frobeniusFactor_flat : Flat D.frobeniusFactor.1 := by
  have : Flat (D.quotientMap ≫ D.frobeniusFactor.1) := by
    rw [D.quotientMap_frobeniusFactor]
    exact (finite_flat_surjective p (base p A)).2.1
  exact Flat.of_comp_of_flat_of_surjective D.quotientMap D.frobeniusFactor.1

instance frobeniusFactor_surjective : Surjective D.frobeniusFactor.1 := by
  have : Surjective (D.quotientMap ≫ D.frobeniusFactor.1) := by
    rw [D.quotientMap_frobeniusFactor]
    exact (finite_flat_surjective p (base p A)).2.2.2
  exact Surjective.of_comp D.quotientMap D.frobeniusFactor.1

instance verschiebungFactor_isFinite : IsFinite D.verschiebungFactor.1 := by
  have : IsProper (D.verschiebungFactor.1 ≫ A.group.X.hom) := by
    rw [D.verschiebungFactor.2]
    infer_instance
  have : IsProper D.verschiebungFactor.1 :=
    IsProper.of_comp D.verschiebungFactor.1 A.group.X.hom
  have : IsFinite (D.quotientMap ≫ D.verschiebungFactor.1) := by
    rw [D.quotientMap_verschiebungFactor]
    exact A.verschiebung_isFinite p
  exact FiniteFlatFactor.isFinite D.quotientMap D.verschiebungFactor.1

instance verschiebungFactor_flat : Flat D.verschiebungFactor.1 := by
  have : Flat (D.quotientMap ≫ D.verschiebungFactor.1) := by
    rw [D.quotientMap_verschiebungFactor]
    exact A.verschiebung_flat p
  exact Flat.of_comp_of_flat_of_surjective D.quotientMap D.verschiebungFactor.1

instance verschiebungFactor_surjective : Surjective D.verschiebungFactor.1 := by
  have : Surjective (D.quotientMap ≫ D.verschiebungFactor.1) := by
    rw [D.quotientMap_verschiebungFactor]
    exact A.verschiebung_surjective p
  exact Surjective.of_comp D.quotientMap D.verschiebungFactor.1

/-- The actual subgroup order times the residual Frobenius degree is p^g. -/
theorem subgroup_order_mul_frobeniusFactor_finrank
    (z : Twist p (base p A)) :
    (toBase p A).finrank (IsLocalRing.closedPoint K) *
      D.frobeniusFactor.1.finrank z = p ^ g := by
  have h := Scheme.Hom.finrank_comp_of_finrank_eq_const
    D.quotientMap D.frobeniusFactor.1
    ((toBase p A).finrank (IsLocalRing.closedPoint K)) D.finrank_eq_subgroup z
  rw [D.quotientMap_frobeniusFactor] at h
  exact h.symm.trans (relative_finrank p (base p A) g z)

/-- The actual subgroup order times the residual Verschiebung degree is p^g. -/
theorem subgroup_order_mul_verschiebungFactor_finrank (z : A.group.X.left) :
    (toBase p A).finrank (IsLocalRing.closedPoint K) *
      D.verschiebungFactor.1.finrank z = p ^ g := by
  have h := Scheme.Hom.finrank_comp_of_finrank_eq_const
    D.quotientMap D.verschiebungFactor.1
    ((toBase p A).finrank (IsLocalRing.closedPoint K)) D.finrank_eq_subgroup z
  rw [D.quotientMap_verschiebungFactor] at h
  exact h.symm.trans (A.verschiebung_finrank p z)

/-- The actual residual Frobenius factor has degree p in the nonzero
differential p-rank-zero surface branch. -/
theorem frobeniusFactor_finrank_eq_prime (hg : g = 2)
    (hA : A.HasPRankOver p 0)
    (hV : GroupScheme.verschiebungCotangent p A.group
      (GroupScheme.law_commutative A.group) ≠ 0) (z : Twist p (base p A)) :
    D.frobeniusFactor.1.finrank z = p := by
  have h := Scheme.Hom.finrank_comp_of_finrank_eq_const
    D.quotientMap D.frobeniusFactor.1 p
    (D.finrank_eq_prime_of_dimension_two hg hA hV) z
  have hpow : p ^ g = p * p := by rw [hg, pow_two]
  rw [D.quotientMap_frobeniusFactor, relative_finrank p (base p A) g z,
    hpow] at h
  exact (Nat.mul_left_cancel (Fact.out : p.Prime).pos h).symm

/-- The actual residual Verschiebung factor has degree p in the nonzero
differential p-rank-zero surface branch. -/
theorem verschiebungFactor_finrank_eq_prime (hg : g = 2)
    (hA : A.HasPRankOver p 0)
    (hV : GroupScheme.verschiebungCotangent p A.group
      (GroupScheme.law_commutative A.group) ≠ 0) (z : A.group.X.left) :
    D.verschiebungFactor.1.finrank z = p := by
  have h := Scheme.Hom.finrank_comp_of_finrank_eq_const
    D.quotientMap D.verschiebungFactor.1 p
    (D.finrank_eq_prime_of_dimension_two hg hA hV) z
  have hpow : p ^ g = p * p := by rw [hg, pow_two]
  rw [D.quotientMap_verschiebungFactor, A.verschiebung_finrank p z, hpow] at h
  exact (Nat.mul_left_cancel (Fact.out : p.Prime).pos h).symm

end SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData
