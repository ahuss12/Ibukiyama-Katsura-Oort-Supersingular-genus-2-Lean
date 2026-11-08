/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import Theorems.Thm_WeierstrassCurve_forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero

/-!
# Geometric supersingularity of elliptic curves

The definition uses the actual point group after base change to an algebraic
closure. Ellipticity is part of the predicate, so a singular Weierstrass
equation cannot qualify. Hasse-invariant vanishing is a proved criterion,
not the definition. No perfectness or finiteness assumption is needed.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.Elliptic

open Polynomial WeierstrassCurve
open scoped Classical

attribute [local instance] WeierstrassCurve.instIsEllipticBaseChange

variable {K : Type*} [Field K]

/-- Ellipticity and trivial geometric p-torsion in characteristic p. -/
def IsSupersingular (p : ℕ) [Fact p.Prime] [CharP K p]
    (E : WeierstrassCurve K) : Prop :=
  E.IsElliptic ∧ ∀ P : (E.baseChange (AlgebraicClosure K)).toAffine.Point,
    p • P = 0 → P = 0

/-- Coefficient extraction commutes with a change of coefficient ring. -/
theorem hasseInvariant_map {R S : Type*} [CommRing R] [CommRing S]
    (p : ℕ) (E : WeierstrassCurve R) (f : R →+* S) :
    (E.map f).hasseInvariant p = f (E.hasseInvariant p) := by
  simp only [WeierstrassCurve.hasseInvariant, ← WeierstrassCurve.Ψ₂Sq_eq,
    WeierstrassCurve.map_Ψ₂Sq, ← Polynomial.map_pow, Polynomial.coeff_map]

theorem hasseInvariant_baseChange (p : ℕ) (E : WeierstrassCurve K)
    (L : Type*) [Field L] [Algebra K L] :
    (E.baseChange L).hasseInvariant p = algebraMap K L (E.hasseInvariant p) :=
  hasseInvariant_map p E (algebraMap K L)

/-- The geometric definition agrees with the Hasse criterion in odd characteristic. -/
theorem isSupersingular_iff_hasseInvariant_eq_zero (p : ℕ) [Fact p.Prime]
    [CharP K p] (hp2 : p ≠ 2) (E : WeierstrassCurve K) [E.IsElliptic] :
    IsSupersingular p E ↔ E.hasseInvariant p = 0 := by
  classical
  rw [IsSupersingular, and_iff_right (inferInstance : E.IsElliptic)]
  rw [WeierstrassCurve.forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero p hp2,
    hasseInvariant_baseChange]
  exact map_eq_zero_iff _ (algebraMap K (AlgebraicClosure K)).injective

/-- Over an algebraically closed field the original point group suffices. -/
theorem isSupersingular_iff_points (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsAlgClosed K] (hp2 : p ≠ 2) (E : WeierstrassCurve K) [E.IsElliptic] :
    IsSupersingular p E ↔ ∀ P : E.toAffine.Point, p • P = 0 → P = 0 := by
  classical
  rw [isSupersingular_iff_hasseInvariant_eq_zero p hp2,
    WeierstrassCurve.forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero p hp2]

/-- The predicate is unchanged by extending the ground field. -/
theorem isSupersingular_baseChange_iff (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp2 : p ≠ 2) (E : WeierstrassCurve K) [E.IsElliptic]
    (L : Type*) [Field L] [Algebra K L] [CharP L p] :
    IsSupersingular p (E.baseChange L) ↔ IsSupersingular p E := by
  rw [isSupersingular_iff_hasseInvariant_eq_zero p hp2,
    isSupersingular_iff_hasseInvariant_eq_zero p hp2, hasseInvariant_baseChange]
  exact map_eq_zero_iff _ (algebraMap K L).injective

end SupersingularCurves.Elliptic
