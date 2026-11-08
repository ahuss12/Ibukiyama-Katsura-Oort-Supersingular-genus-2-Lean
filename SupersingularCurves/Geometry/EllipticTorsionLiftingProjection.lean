/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.EllipticTorsionLiftingCanonical

/-!
# The Hopf map of actual torsion projection

Multiplication between actual torsion levels induces a bialgebra map via its
natural group-valued functor on all test algebras. Its spectrum is identified
with the previously constructed scheme projection.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.TorsionLevels.Presentation
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian

variable {K : Type u} [Field K] [IsAlgClosed K] {g n m : ℕ} {A : AbelianVariety K g}
  (H : Presentation A (n * m)) (H' : Presentation A n)

local instance : Smooth A.group.X.hom :=
  SmoothOfRelativeDimension.smooth g A.group.X.hom

private theorem nsmul_pow {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (r : ℕ) (P : SchemeHomOver t A.group.X.hom) :
    letI := (GroupScheme.law A.group).pointGroup t
    (GroupScheme.law A.group).nsmul t r P = P ^ r := by
  letI := (GroupScheme.law A.group).pointGroup t
  induction r with
  | zero => rfl
  | succ r ih => rw [RelativeGroupLaw.nsmul_succ, pow_succ, ih]; rfl

private theorem nsmul_mem (T : Type u) [CommRing T] [Algebra K T]
    (x : WithConv (H.Coord →ₐ[K] T)) :
    (GroupScheme.law A.group).nsmul _ m (H.points T x).val ∈
      (GroupScheme.law A.group).torsionSubset
        (Spec.map (CommRingCat.ofHom (algebraMap K T))) n := by
  letI := (GroupScheme.law A.group).pointGroup
    (Spec.map (CommRingCat.ofHom (algebraMap K T)))
  have hx := (H.points T x).property
  change (GroupScheme.law A.group).nsmul _ (n * m) (H.points T x).val = _ at hx
  change (GroupScheme.law A.group).nsmul _ n
    ((GroupScheme.law A.group).nsmul _ m (H.points T x).val) = _
  rw [nsmul_pow] at hx
  rw [nsmul_pow, nsmul_pow, ← pow_mul, Nat.mul_comm m n]
  exact hx

/-- The actual multiplication map on all torsion points. -/
def multiplicationPoints (T : Type u) [CommRing T] [Algebra K T]
    (x : WithConv (H.Coord →ₐ[K] T)) : WithConv (H'.Coord →ₐ[K] T) :=
  (H'.points T).symm ⟨_, nsmul_mem H T x⟩

theorem multiplicationPoints_comparison (T : Type u) [CommRing T] [Algebra K T]
    (x : WithConv (H.Coord →ₐ[K] T)) :
    ((H'.points T (multiplicationPoints H H' T x)).val : SchemeHomOver _ A.group.X.hom) =
      (GroupScheme.law A.group).nsmul _ m (H.points T x).val :=
  congrArg Subtype.val ((H'.points T).apply_symm_apply _)

theorem multiplicationPoints_natural
    (T T' : Type u) [CommRing T] [Algebra K T] [CommRing T'] [Algebra K T']
    (a : T →ₐ[K] T') (x : WithConv (H.Coord →ₐ[K] T)) :
    (multiplicationPoints H H' T' (.toConv (a.comp x.ofConv))).ofConv =
      a.comp (multiplicationPoints H H' T x).ofConv := by
  have hh : multiplicationPoints H H' T' (.toConv (a.comp x.ofConv)) =
      .toConv (a.comp (multiplicationPoints H H' T x).ofConv) := by
    apply (H'.points T').injective
    apply Subtype.ext
    apply Subtype.ext
    rw [H'.points_natural, multiplicationPoints_comparison,
      multiplicationPoints_comparison, SchemeFrobenius.nsmul_point,
      SchemeFrobenius.nsmul_point, H.points_natural, Category.assoc]
  exact congrArg WithConv.ofConv hh

theorem multiplicationPoints_mul (T : Type u) [CommRing T] [Algebra K T]
    (x y : WithConv (H.Coord →ₐ[K] T)) :
    multiplicationPoints H H' T (x * y) =
      multiplicationPoints H H' T x * multiplicationPoints H H' T y := by
  apply (H'.points T).injective
  apply Subtype.ext
  rw [H'.points_mul, multiplicationPoints_comparison, multiplicationPoints_comparison,
    multiplicationPoints_comparison, H.points_mul,
    PerfectFieldVerschiebung.nsmul_mul A.group.X.hom (GroupScheme.law A.group)
      A.groupScheme_law_commutative]

theorem multiplicationPoints_one (T : Type u) [CommRing T] [Algebra K T] :
    multiplicationPoints H H' T 1 = 1 := by
  apply (H'.points T).injective
  apply Subtype.ext
  rw [multiplicationPoints_comparison, points_one, points_one, RelativeGroupLaw.nsmul_unit]

/-- The actual projection induces a finite Hopf algebra map. -/
theorem exists_multiplicationMap :
    ∃ q : H'.Coord →ₐc[K] H.Coord,
      ∀ (T : Type u) [CommRing T] [Algebra K T] (x : WithConv (H.Coord →ₐ[K] T)),
        (multiplicationPoints H H' T x).ofConv = x.ofConv.comp (q : H'.Coord →ₐ[K] H.Coord) :=
  BialgHom.exists_comp_eq_of_natural_of_map_mul (multiplicationPoints H H')
    (multiplicationPoints_natural H H') (multiplicationPoints_mul H H')
    (multiplicationPoints_one H H')

def multiplicationMap : H'.Coord →ₐc[K] H.Coord := Classical.choose (exists_multiplicationMap H H')

theorem multiplicationMap_points (T : Type u) [CommRing T] [Algebra K T]
    (x : WithConv (H.Coord →ₐ[K] T)) :
    ((H'.points T (.toConv (x.ofConv.comp
      (multiplicationMap H H' : H'.Coord →ₐ[K] H.Coord)))).val : SchemeHomOver _ A.group.X.hom) =
        (GroupScheme.law A.group).nsmul _ m (H.points T x).val := by
  have he := Classical.choose_spec (exists_multiplicationMap H H') T x
  rw [multiplicationMap, ← he]
  exact multiplicationPoints_comparison H H' T x

/-- The bialgebra map is the already constructed actual scheme projection. -/
@[reassoc]
theorem multiplicationMap_spec :
    Spec.map (CommRingCat.ofHom (multiplicationMap H H').toAlgHom.toRingHom) ≫ H'.specIso.hom =
      H.specIso.hom ≫ multiplication A n m := by
  apply (cancel_mono (inclusion A n)).mp
  have h := congrArg Subtype.val
    (multiplicationMap_points H H' H.Coord (.toConv (AlgHom.id K H.Coord)))
  rw [H'.points_scheme, SchemeFrobenius.nsmul_point, H.points_scheme] at h
  have hid : Spec.map (CommRingCat.ofHom (AlgHom.id K H.Coord).toRingHom) = 𝟙 _ := by
    change Spec.map (𝟙 (CommRingCat.of H.Coord)) = _
    exact Spec.map_id _
  simpa only [WithConv.ofConv_toConv, AlgHom.id_comp, hid, Category.id_comp,
    Category.assoc, multiplication_inclusion] using h

end SupersingularCurves.Geometry.TorsionLevels.Presentation
