/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.SymmetricProjectiveBundle
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_FiniteBySections_tensorPow

/-!
# An actual semilinear automorphism and invariant projective bundle

Vanishing of actual Verschiebung cotangent constructs an automorphism of the
underlying scheme lying over the square of field Frobenius. Its composite
with multiplication by p is absolute Frobenius squared, and it preserves an
actual invertible sheaf having a finite projective presentation. These are
inputs to finite-field descent; this file does not assert a descended model.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FrobeniusFiniteFieldDescent
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open NeronModelInfra GoodReductionJacobian SchemeFrobenius PerfectFieldVerschiebung

variable {K : Type u} [Field K] [IsAlgClosed K]
variable (p : ℕ) [Fact p.Prime] [CharP K p]
variable {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of K))

omit [IsAlgClosed K] in
/-- The actual double projection lies over the square of field Frobenius. -/
theorem doubleProjection_over :
    doubleProjection p c ≫ c =
      toBase p (toBase p c) ≫ baseMap p K ≫ baseMap p K := by
  change (pullback.fst (toBase p c) (baseMap p K) ≫
    pullback.fst c (baseMap p K)) ≫ c = _
  rw [Category.assoc, pullback.condition, ← Category.assoc,
    show pullback.fst (toBase p c) (baseMap p K) ≫
        pullback.snd c (baseMap p K) =
        pullback.snd (toBase p c) (baseMap p K) ≫ baseMap p K from
      pullback.condition, Category.assoc]
  rfl

/-- The actual residual isomorphism defines a Frobenius-semilinear scheme
 automorphism after composing its inverse with double projection. -/
def schemeAutomorphism (e : Twist p (toBase p c) ≅ X) : X ≅ X :=
  e.symm ≪≫ asIso (doubleProjection p c)

@[simp]
theorem schemeAutomorphism_hom (e : Twist p (toBase p c) ≅ X) :
    (schemeAutomorphism p c e).hom = e.inv ≫ doubleProjection p c := rfl

/-- This automorphism lies over p²-power Frobenius on the actual base. -/
theorem schemeAutomorphism_over (e : Twist p (toBase p c) ≅ X)
    (he : e.hom ≫ c = toBase p (toBase p c)) :
    (schemeAutomorphism p c e).hom ≫ c = c ≫ baseMap p K ≫ baseMap p K := by
  rw [schemeAutomorphism_hom, Category.assoc, doubleProjection_over, ← he]
  simp only [← Category.assoc, e.inv_hom_id, Category.id_comp]

/-- Conjugating the actual pullback compatibility produces an invariant
sheaf for the genuine semilinear automorphism. -/
def invariantBundleIso (e : Twist p (toBase p c) ≅ X) (M : X.Modules)
    (hM : (Scheme.Modules.pullback e.hom).obj M ≅
      (Scheme.Modules.pullback (doubleProjection p c)).obj M) :
    (Scheme.Modules.pullback (schemeAutomorphism p c e).hom).obj M ≅ M :=
  ((Scheme.Modules.pullbackComp e.inv (doubleProjection p c)).app M).symm ≪≫
    (Scheme.Modules.pullback e.inv).mapIso hM.symm ≪≫
    (Scheme.Modules.pullbackComp e.inv e.hom).app M ≪≫
    (Scheme.Modules.pullbackCongr e.inv_hom_id).app M ≪≫
    (Scheme.Modules.pullbackId X).app M

/-- The semilinear automorphism composed after the original endomorphism is
actual absolute Frobenius squared. -/
theorem endomorphism_comp_schemeAutomorphism
    (e : Twist p (toBase p c) ≅ X) (m : X ⟶ X)
    (he : doubleRelative p c ≫ e.hom = m) :
    m ≫ (schemeAutomorphism p c e).hom = absolute p c ≫ absolute p c := by
  rw [schemeAutomorphism_hom, ← he, Category.assoc, ← Category.assoc e.hom,
    e.hom_inv_id, Category.id_comp, doubleRelative_projection]

end SupersingularCurves.Geometry.FrobeniusFiniteFieldDescent

namespace SupersingularCurves.Geometry.AbelianVariety
open CategoryTheory AlgebraicGeometry
open NeronModelInfra GoodReductionJacobian SchemeFrobenius PerfectFieldVerschiebung
open FrobeniusFiniteFieldDescent

variable {K : Type u} [Field K] [IsAlgClosed K] {g : ℕ}
variable (A : AbelianVariety K g) (p : ℕ) [Fact p.Prime] [CharP K p]

local instance : Smooth A.group.X.hom :=
  SmoothOfRelativeDimension.smooth g A.group.X.hom

/-- Zero actual Verschiebung cotangent supplies a genuine p²-semilinear
scheme automorphism preserving an actual invertible sheaf with a finite
projective presentation. Its p-multiplication composite is absolute
Frobenius squared. -/
theorem exists_frobeniusSquare_automorphism_invariant_bundle
    (hV : GroupScheme.verschiebungCotangent p A.group A.groupScheme_law_commutative = 0) :
    ∃ (τ : A.group.X.left ≅ A.group.X.left) (M : A.group.X.left.Modules),
      τ.hom ≫ A.group.X.hom = A.group.X.hom ≫ baseMap p K ≫ baseMap p K ∧
      (GroupScheme.law A.group).schemeNsmul p ≫ τ.hom =
        absolute p A.group.X.hom ≫ absolute p A.group.X.hom ∧
      Scheme.Modules.IsInvertible M ∧
      M.FiniteBySections A.group.X.hom ∧
      Nonempty ((Scheme.Modules.pullback τ.hom).obj M ≅ M) := by
  obtain ⟨L, e, hL, _, hfinite, he, hover, hcompat⟩ :=
    A.exists_frobenius_factor_iso_symmetric_projective_bundle p hV
  let M := L.tensorPow (p ^ 2)
  have hdouble : doubleRelative p A.group.X.hom ≫ e.hom =
      (GroupScheme.law A.group).schemeNsmul p := by
    rw [doubleRelative, Category.assoc, he, frobenius_verschiebung]
  refine ⟨schemeAutomorphism p A.group.X.hom e, M,
    schemeAutomorphism_over p A.group.X.hom e hover,
    endomorphism_comp_schemeAutomorphism p A.group.X.hom e _ hdouble,
    FrobeniusLineBundle.tensorPower_invertible hL (p ^ 2), ?_,
    ⟨invariantBundleIso p A.group.X.hom e M hcompat.some⟩⟩
  exact hfinite.tensorPow (pow_pos (Fact.out : p.Prime).pos 2)

end SupersingularCurves.Geometry.AbelianVariety
