/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusLineBundle
import SupersingularCurves.Geometry.FrobeniusPicardComparison
import SupersingularCurves.Geometry.FrobeniusDifferentialTwist

/-!
# Actual double Frobenius and tensor powers of line bundles

The two genuine relative Frobenius maps become the square of absolute
Frobenius after projection. Pullback of an invertible sheaf along that square
is its p²-th tensor power, as an actual sheaf isomorphism.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FrobeniusLineBundle
open CategoryTheory MonoidalCategory AlgebraicGeometry

variable {X : Scheme.{u}} (L : X.Modules)

/-- Reassociate the recursively defined actual sheaf tensor powers. -/
def tensorPowerAddIso (m : ℕ) : (n : ℕ) →
    L.tensorPow (m + n) ≅ L.tensorPow m ⊗ L.tensorPow n
  | 0 => (ρ_ (L.tensorPow m)).symm
  | n + 1 => (tensorPowerAddIso m n ⊗ᵢ Iso.refl L) ≪≫
      (α_ (L.tensorPow m) (L.tensorPow n) L)

/-- Iterated tensor powers multiply their actual exponents. -/
def tensorPowerMulIso (m : ℕ) : (n : ℕ) →
    (L.tensorPow m).tensorPow n ≅ L.tensorPow (m * n)
  | 0 => Iso.refl _
  | n + 1 => by
      rw [Nat.mul_succ]
      exact (tensorPowerMulIso m n ⊗ᵢ Iso.refl (L.tensorPow m)) ≪≫
        (tensorPowerAddIso L (m * n) m).symm

variable {K : Type u} [Field K]
variable (c : X ⟶ Spec (CommRingCat.of K))
variable (p : ℕ) [Fact p.Prime] [CharP K p]
variable (hL : Scheme.Modules.IsInvertible L)

/-- Two actual absolute Frobenius pullbacks give the p²-th tensor power. -/
def absoluteSquarePullbackIso :
    (Scheme.Modules.pullback
      (SchemeFrobenius.absolute p c ≫ SchemeFrobenius.absolute p c)).obj L ≅
        L.tensorPow (p ^ 2) :=
  ((Scheme.Modules.pullbackComp _ _).app L).symm ≪≫
    (Scheme.Modules.pullback (SchemeFrobenius.absolute p c)).mapIso
      (pullbackIsoTensorPower p (Fact.out : p.Prime) (SchemeFrobenius.globalChar p c) hL) ≪≫
    pullbackIsoTensorPower p (Fact.out : p.Prime) (SchemeFrobenius.globalChar p c)
      (tensorPower_invertible hL p) ≪≫
    tensorPowerMulIso L p p ≪≫ eqToIso (by rw [pow_two])

end SupersingularCurves.Geometry.FrobeniusLineBundle

namespace SupersingularCurves.Geometry.SchemeFrobenius
open CategoryTheory AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime] {K : Type u} [Field K] [CharP K p]
variable {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of K))

/-- The projection from the actual double Frobenius base change. -/
def doubleProjection : Twist p (toBase p c) ⟶ X :=
  projection p (toBase p c) ≫ projection p c

/-- The two successive actual relative Frobenius morphisms. -/
def doubleRelative : X ⟶ Twist p (toBase p c) :=
  relative p c ≫ relative p (toBase p c)

/-- Absolute Frobenius squared is natural for actual scheme morphisms. -/
theorem absolute_square_natural {Y : Scheme.{u}}
    (d : Y ⟶ Spec (CommRingCat.of K)) (f : X ⟶ Y) :
    (absolute p c ≫ absolute p c) ≫ f =
      f ≫ (absolute p d ≫ absolute p d) := by
  have h := Scheme.frobenius_comp f p 1 (Fact.out : p.Prime)
    (globalChar p c) (globalChar p d)
  change absolute p c ≫ f = f ≫ absolute p d at h
  simp only [Category.assoc]
  rw [h, ← Category.assoc, h, Category.assoc]

/-- Double relative Frobenius followed by the actual double projection is
the square of actual absolute Frobenius. -/
theorem doubleRelative_projection :
    doubleRelative p c ≫ doubleProjection p c = absolute p c ≫ absolute p c := by
  have h := Scheme.frobenius_comp (projection p c) p 1 (Fact.out : p.Prime)
    (globalChar p (toBase p c)) (globalChar p c)
  change absolute p (toBase p c) ≫ projection p c = projection p c ≫ absolute p c at h
  simp only [doubleRelative, doubleProjection, Category.assoc]
  rw [← Category.assoc (relative p (toBase p c)), relative_projection, h,
    ← Category.assoc, relative_projection]

variable [PerfectField K]

instance doubleProjection_isIso : IsIso (doubleProjection p c) := by
  unfold doubleProjection
  infer_instance

/-- Projection followed by double relative Frobenius is absolute Frobenius
squared on the actual twice-twisted scheme. -/
theorem doubleProjection_relative :
    doubleProjection p c ≫ doubleRelative p c =
      absolute p (toBase p (toBase p c)) ≫ absolute p (toBase p (toBase p c)) := by
  apply (cancel_mono (doubleProjection p c)).mp
  rw [Category.assoc, doubleRelative_projection]
  exact (absolute_square_natural p (toBase p (toBase p c)) c
    (doubleProjection p c)).symm

/-- A residual factor of double relative Frobenius satisfies the actual
semilinear square with absolute Frobenius and the original endomorphism. -/
theorem factor_absolute_square
    (e : Twist p (toBase p c) ⟶ X) (m : X ⟶ X)
    (he : doubleRelative p c ≫ e = m) :
    e ≫ (absolute p c ≫ absolute p c) = doubleProjection p c ≫ m := by
  rw [← absolute_square_natural p (toBase p (toBase p c)) c e,
    ← doubleProjection_relative, Category.assoc, he]

end SupersingularCurves.Geometry.SchemeFrobenius
