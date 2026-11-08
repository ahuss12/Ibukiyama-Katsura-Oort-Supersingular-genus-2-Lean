/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.PRankZeroVerschiebungKernel
import SupersingularCurves.Geometry.PointedCotangentFibre

/-!
# A nontrivial finite infinitesimal subgroup at p-rank zero

The simultaneous kernel of actual Frobenius and Verschiebung has the same
cotangent space as the actual Verschiebung kernel. This is proved by lifting
square-zero points across the actual Frobenius fibre. At p-rank zero in positive
dimension that cotangent space is nonzero, so the simultaneous kernel is a
genuine nontrivial finite flat subgroup.

The order-p calculation in dimension two and superspeciality of the quotient
are not conclusions of this file.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian SchemeFrobenius PerfectFieldVerschiebung

variable {K : Type u} [Field K]
variable (p : ℕ) [Fact p.Prime] [CharP K p] [IsAlgClosed K]
variable {g : ℕ} (A : AbelianVariety K g)

theorem vInclusion_frobenius_over :
    (vInclusion p A ≫ F p A) ≫ SchemeFrobenius.toBase p (base p A) = vToBase p A := by
  rw [Category.assoc, relative_toBase, vInclusion_over]

theorem vIdentityPoint_frobenius :
    (vIdentityPoint p A).1 ≫ (vInclusion p A ≫ F p A) = twiceTwistZero p A := by
  rw [← Category.assoc, vIdentityPoint_inclusion]
  exact congrArg Subtype.val (relative_one p (base p A) (law p A) (𝟙 _))

/-- The actual restriction of Frobenius to the actual V-kernel has zero
cotangent differential. -/
theorem vKernel_frobenius_differential_zero :
    PointedCotangent.differential (vToBase p A) (vIdentityPoint p A)
      (vInclusion p A ≫ F p A) (vInclusion_frobenius_over p A)
      (vIdentityPoint_frobenius p A) = 0 := by
  let s := (law p A).one (𝟙 (Spec (CommRingCat.of K)))
  let z := (twistLaw p (base p A) (law p A)).one (𝟙 (Spec (CommRingCat.of K)))
  have hsz : s.1 ≫ F p A = z.1 :=
    congrArg Subtype.val (relative_one p (base p A) (law p A) (𝟙 _))
  have hz : twistedSection p (base p A) s = z :=
    Subtype.ext ((section_relative p (base p A) s).symm.trans hsz)
  have hF : PointedCotangent.differential (base p A) s (F p A)
      (relative_toBase p (base p A)) hsz = 0 :=
    (PointedCotangent.differential_eq_zero_iff_of_points_eq rfl hz (F p A)
      (relative_toBase p (base p A)) (section_relative p (base p A) s) hsz).mp
      (relative_differential_eq_zero p (base p A) s)
  rw [PointedCotangent.differential_comp (vToBase p A) (vIdentityPoint p A)
    (vInclusion p A) (vInclusion_over p A) (vIdentityPoint_inclusion p A)
    (F p A) (relative_toBase p (base p A)) hsz, hF, LinearMap.comp_zero]

/-- The same actual subgroup, with its pullback structure morphism. -/
abbrev fibreToBase : scheme p A ⟶ Spec (CommRingCat.of K) :=
  pullback.snd (vInclusion p A ≫ F p A) (twiceTwistZero p A)

/-- The identity section supplied by the defining pullback. -/
def fibreIdentityPoint : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (fibreToBase p A) :=
  PointedCotangent.Fibre.point (vToBase p A) (vIdentityPoint p A)
    (vInclusion p A ≫ F p A) (vIdentityPoint_frobenius p A)

/-- The subgroup's actual cotangent space is isomorphic to that of ker V. -/
theorem cotangent_bijective :
    Function.Bijective (PointedCotangent.differential (fibreToBase p A)
      (fibreIdentityPoint p A)
      (pullback.fst (vInclusion p A ≫ F p A) (twiceTwistZero p A))
      (PointedCotangent.Fibre.inclusion_over (vToBase p A)
        (vInclusion p A ≫ F p A) (vInclusion_frobenius_over p A))
      (PointedCotangent.Fibre.point_inclusion (vToBase p A) (vIdentityPoint p A)
        (vInclusion p A ≫ F p A) (vIdentityPoint_frobenius p A))) :=
  PointedCotangent.Fibre.differential_bijective_of_zero (vToBase p A)
    (vIdentityPoint p A) (vInclusion p A ≫ F p A)
    (vInclusion_frobenius_over p A) (vIdentityPoint_frobenius p A)
    (vKernel_frobenius_differential_zero p A)

/-- Positive dimension and p-rank zero force this actual finite subgroup
to have nonzero cotangent space. It cannot be the trivial subgroup scheme. -/
theorem cotangent_not_subsingleton (hA : A.HasPRankOver p 0) (hg : g ≠ 0) :
    ¬ Subsingleton (PointedCotangent.Cotangent (fibreToBase p A) (fibreIdentityPoint p A)) := by
  intro hcot
  let := hcot
  apply vKernel_cotangent_not_subsingleton p A hA hg
  exact Function.Injective.subsingleton (cotangent_bijective p A).1

end SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup
