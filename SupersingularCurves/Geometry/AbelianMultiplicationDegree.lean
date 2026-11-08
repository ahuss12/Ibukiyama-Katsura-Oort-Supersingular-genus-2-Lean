/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.VerschiebungNaturality
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_schemeKerStr_and_finrank_eq_pow_and_finrank_schemeNsmul_eq_pow
import SupersingularCurves.Geometry.FrobeniusDegree
import Theorems.Thm_AlgebraicGeometry_Flat_of_comp_of_flat_of_surjective
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_finrank_comp_of_finrank_eq_const

/-!
# Multiplication and Verschiebung on actual abelian varieties

Multiplication by every positive integer is finite, flat, surjective, and has
degree `n^(2g)`. The input geometric property bundle is proved from the actual
abelian variety. In particular, the theorem includes multiplication by the
characteristic; invertibility of the integer is not assumed.

The two actual Frobenius--Verschiebung composition identities then prove that
Verschiebung is finite, flat, and surjective. The relative Frobenius degree
`p^g` is proved through smooth local coordinates, and multiplicativity gives
the same degree for Verschiebung. This file does not assert the supersingular
or superspecial classification.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.AbelianVariety
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open NeronModelInfra GoodReductionJacobian

variable {K : Type u} [Field K] {g : ℕ} (A : AbelianVariety K g)

local instance : Smooth A.group.X.hom :=
  SmoothOfRelativeDimension.smooth g A.group.X.hom

/-- Commutativity of the existing scheme group law on all test schemes. -/
theorem groupScheme_law_commutative : (GroupScheme.law A.group).IsCommutative := by
  intro T t x y
  exact relativeGroupLawOfGrpObj_mul_comm_of_isCommMonObj A.comm t x y

/-- The genuine geometric abelian-scheme hypotheses follow from the definition
of an abelian variety. -/
theorem abelianSchemePropertyBundle : AbelianSchemePropertyBundle K A.group.X.hom where
  smooth := SmoothOfRelativeDimension.smooth g A.group.X.hom
  proper := inferInstance
  connectedFibres := A.group.X.hom.isConnected_preimage_singleton
  hasGroupLaw := ⟨GroupScheme.law A.group⟩

/-- Scheme-theoretic multiplication, including characteristic-divisible
integers, has the expected degree on every fibre. -/
theorem multiplication_finite_flat_degree [IsAlgClosed K] (n : ℕ) (hn : n ≠ 0) :
    IsFinite ((GroupScheme.law A.group).schemeKerStr n) ∧
      ((GroupScheme.law A.group).schemeKerStr n).finrank (IsLocalRing.closedPoint K) =
        n ^ (2 * g) ∧
      IsFinite ((GroupScheme.law A.group).schemeNsmul n) ∧
      Flat ((GroupScheme.law A.group).schemeNsmul n) ∧
      Function.Surjective ((GroupScheme.law A.group).schemeNsmul n) ∧
      ∀ x : A.group.X.left, ((GroupScheme.law A.group).schemeNsmul n).finrank x =
        n ^ (2 * g) :=
  GoodReductionJacobian.RelativeGroupLaw.isFinite_schemeKerStr_and_finrank_eq_pow_and_finrank_schemeNsmul_eq_pow
    K A.group.X.hom (GroupScheme.law A.group) A.groupScheme_law_commutative
    A.abelianSchemePropertyBundle g n hn

open SchemeFrobenius PerfectFieldVerschiebung

variable [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]

/-- The actual Frobenius twist has the same abelian geometric properties. -/
theorem twist_abelianSchemePropertyBundle :
    AbelianSchemePropertyBundle K (toBase p A.group.X.hom) where
  smooth := by
    change Smooth (pullback.snd A.group.X.hom (baseMap p K))
    infer_instance
  proper := by
    change IsProper (pullback.snd A.group.X.hom (baseMap p K))
    infer_instance
  connectedFibres := by
    haveI : GeometricallyConnected (toBase p A.group.X.hom) := by
      change GeometricallyConnected (pullback.snd A.group.X.hom (baseMap p K))
      infer_instance
    exact (toBase p A.group.X.hom).isConnected_preimage_singleton
  hasGroupLaw := ⟨twistLaw p A.group.X.hom (GroupScheme.law A.group)⟩

/-- Verschiebung is a finite scheme morphism, proved from multiplication on
the actual Frobenius twist and the composition `V ≫ F = [p]`. -/
theorem verschiebung_isFinite :
    IsFinite (verschiebung p A.group.X.hom (GroupScheme.law A.group)
      A.groupScheme_law_commutative) := by
  haveI : SmoothOfRelativeDimension g (toBase p A.group.X.hom) := by
    exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
      (IsPullback.of_hasPullback A.group.X.hom (baseMap p K)) A.smooth
  have h :=
    GoodReductionJacobian.RelativeGroupLaw.isFinite_schemeKerStr_and_finrank_eq_pow_and_finrank_schemeNsmul_eq_pow
      K (toBase p A.group.X.hom) (twistLaw p A.group.X.hom (GroupScheme.law A.group))
      (twistLaw_commutative p A.group.X.hom (GroupScheme.law A.group)
        A.groupScheme_law_commutative) (A.twist_abelianSchemePropertyBundle p) g p
      (Fact.out : p.Prime).ne_zero
  haveI : IsFinite (relative p A.group.X.hom) := (finite_flat_surjective p A.group.X.hom).1
  haveI : IsFinite (verschiebung p A.group.X.hom (GroupScheme.law A.group)
      A.groupScheme_law_commutative ≫ relative p A.group.X.hom) := by
    rw [verschiebung_frobenius]
    exact h.2.2.1
  exact IsFinite.of_comp _ (relative p A.group.X.hom)

/-- Every geometric point is hit by actual Verschiebung, because `[p]` is
surjective and factors as `F ≫ V`. -/
theorem verschiebung_surjective :
    Surjective (verschiebung p A.group.X.hom (GroupScheme.law A.group)
      A.groupScheme_law_commutative) := by
  have hn := (A.multiplication_finite_flat_degree p (Fact.out : p.Prime).ne_zero).2.2.2.2.1
  constructor
  intro y
  obtain ⟨x, hx⟩ := hn y
  refine ⟨relative p A.group.X.hom x, ?_⟩
  change (relative p A.group.X.hom ≫
    verschiebung p A.group.X.hom (GroupScheme.law A.group)
      A.groupScheme_law_commutative) x = y
  rw [frobenius_verschiebung]
  exact hx

/-- Flatness of Verschiebung descends along the actual faithfully flat
relative Frobenius, using `F ≫ V = [p]`. -/
theorem verschiebung_flat :
    Flat (verschiebung p A.group.X.hom (GroupScheme.law A.group)
      A.groupScheme_law_commutative) := by
  have hF := finite_flat_surjective p A.group.X.hom
  haveI : Flat (relative p A.group.X.hom) := hF.2.1
  haveI : Surjective (relative p A.group.X.hom) := hF.2.2.2
  haveI : Flat (relative p A.group.X.hom ≫
      verschiebung p A.group.X.hom (GroupScheme.law A.group)
        A.groupScheme_law_commutative) := by
    rw [frobenius_verschiebung]
    exact (A.multiplication_finite_flat_degree p (Fact.out : p.Prime).ne_zero).2.2.2.1
  exact Flat.of_comp_of_flat_of_surjective (relative p A.group.X.hom) _

/-- The scheme-theoretic relative Frobenius has degree `p^g`, obtained from
smooth coordinates rather than inferred from its point map. -/
theorem relativeFrobenius_finrank (y : Twist p A.group.X.hom) :
    (relative p A.group.X.hom).finrank y = p ^ g :=
  relative_finrank p A.group.X.hom g y

/-- The actual Verschiebung has degree `p^g` on every fibre. -/
theorem verschiebung_finrank (y : A.group.X.left) :
    (verschiebung p A.group.X.hom (GroupScheme.law A.group)
      A.groupScheme_law_commutative).finrank y = p ^ g := by
  haveI : IsFinite (relative p A.group.X.hom) := (finite_flat_surjective p A.group.X.hom).1
  haveI : Flat (relative p A.group.X.hom) := (finite_flat_surjective p A.group.X.hom).2.1
  haveI := A.verschiebung_isFinite p
  haveI := A.verschiebung_flat p
  have h := Scheme.Hom.finrank_comp_of_finrank_eq_const
    (relative p A.group.X.hom)
    (verschiebung p A.group.X.hom (GroupScheme.law A.group) A.groupScheme_law_commutative)
    (p ^ g) (A.relativeFrobenius_finrank p) y
  rw [frobenius_verschiebung,
    (A.multiplication_finite_flat_degree p (Fact.out : p.Prime).ne_zero).2.2.2.2.2 y] at h
  have hpos : 0 < p ^ g := pow_pos (Fact.out : p.Prime).pos g
  have hpow : p ^ (2 * g) = p ^ g * p ^ g := by
    rw [two_mul, pow_add]
  rw [hpow] at h
  exact (Nat.mul_left_cancel hpos h).symm

end SupersingularCurves.Geometry.AbelianVariety
