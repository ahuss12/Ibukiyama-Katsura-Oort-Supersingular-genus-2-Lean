/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup
import SupersingularCurves.Geometry.JacobianPoints
import SupersingularCurves.Geometry.FiniteCotangentPoint

/-!
# The infinitesimal Verschiebung kernel at p-rank zero

The independently defined p-rank-zero hypothesis forces the actual finite
Verschiebung fibre to have one geometric point. Its scheme degree remains
`p^g`. In positive dimension its local cotangent space therefore cannot vanish.
This is a statement about the actual finite kernel, not a replacement
definition of supersingularity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian SchemeFrobenius PerfectFieldVerschiebung
open scoped CategoryTheory.MonObj

variable {K : Type u} [Field K]
variable (p : ℕ) [Fact p.Prime] [CharP K p] [IsAlgClosed K]
variable {g : ℕ} (A : AbelianVariety K g)

/-- The genuine identity point of the actual Verschiebung fibre. -/
def vIdentityPoint : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (vToBase p A) :=
  ⟨pullback.lift (twistZero p A) (𝟙 _)
    (by simpa only [Category.id_comp] using
      (verschiebung_zero p A.group.X.hom (GroupScheme.law A.group)
        A.groupScheme_law_commutative)), pullback.lift_snd _ _ _⟩

theorem vIdentityPoint_inclusion :
    (vIdentityPoint p A).1 ≫ vInclusion p A = twistZero p A :=
  pullback.lift_fst _ _ _

/-- Actual p-rank zero implies the rational Verschiebung kernel is trivial
in every dimension, by the Frobenius point bijection. -/
theorem vPoint_kernel_trivial (hA : A.HasPRankOver p 0)
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (base p A))
    (hx : verschiebungPoint p A.group.X.hom (GroupScheme.law A.group)
      A.groupScheme_law_commutative x = (GroupScheme.law A.group).one (𝟙 _)) :
    x = (law p A).one (𝟙 _) := by
  apply (verschiebungPoint_kernel_trivial_iff p A.group.X.hom
    (GroupScheme.law A.group) A.groupScheme_law_commutative).mpr ?_ x hx
  intro y hy
  let P : A.Points := schemeHomOverToOverHom y
  have hP : P ^ p = 1 := by
    apply Over.OverMorphism.ext
    have ht := congrArg Subtype.val (GroupScheme.nsmul_eq_pow A.group (𝟙 _) p P)
    simp only [P, overHomToSchemeHomOver_schemeHomOverToOverHom] at ht
    change ((GroupScheme.law A.group).nsmul (𝟙 _) p y).1 = (P ^ p).left at ht
    rw [← ht, hy]
    rfl
  have hz := congrArg overHomToSchemeHomOver
    ((AbelianVariety.hasPRankOver_zero_iff A p).mp hA P hP)
  apply Subtype.ext
  exact congrArg Subtype.val hz

/-- The entire finite Verschiebung fibre has a unique rational point. -/
theorem vKernel_unique_point (hA : A.HasPRankOver p 0)
    (q : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (vToBase p A)) :
    q = vIdentityPoint p A := by
  let x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (base p A) :=
    ⟨q.1 ≫ vInclusion p A, by rw [Category.assoc, vInclusion_over, q.2]⟩
  have hx : x.1 ≫ V p A = zero A := by
    change (q.1 ≫ pullback.fst _ _) ≫ V p A = _
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (q.1 ≫ vToBase p A) ≫ zero A = _
    rw [q.2, Category.id_comp]
  have hz := vPoint_kernel_trivial p A hA x (Subtype.ext hx)
  apply Subtype.ext
  apply pullback.hom_ext
  · exact (congrArg Subtype.val hz).trans (vIdentityPoint_inclusion p A).symm
  · exact q.2.trans (vIdentityPoint p A).2.symm

/-- The actual Verschiebung kernel is supported at its identity at p-rank zero. -/
theorem vKernel_subsingleton (hA : A.HasPRankOver p 0) : Subsingleton (vKernel p A) :=
  FiniteGeometricPoints.subsingleton_of_unique_point (vToBase p A)
    (vIdentityPoint p A) (vKernel_unique_point p A hA)

/-- Its finite scheme length is still `p^g`; trivial geometric points do not
discard the infinitesimal kernel. -/
theorem vKernel_finrank :
    (vToBase p A).finrank (IsLocalRing.closedPoint K) = p ^ g := by
  let : IsFinite (V p A) := A.verschiebung_isFinite p
  let : Flat (V p A) := A.verschiebung_flat p
  change (pullback.snd (V p A) (zero A)).finrank _ = _
  rw [Scheme.Hom.finrank_pullback_snd]
  exact A.verschiebung_finrank p (zero A (IsLocalRing.closedPoint K))

/-- Positive-dimensional p-rank-zero abelian varieties have a nonzero
actual cotangent space in their Verschiebung kernel. -/
theorem vKernel_cotangent_not_subsingleton (hA : A.HasPRankOver p 0) (hg : g ≠ 0) :
    ¬ Subsingleton (PointedCotangent.Cotangent (vToBase p A) (vIdentityPoint p A)) := by
  intro hcot
  let : IsIso (vToBase p A) :=
    PointedCotangent.isIso_of_unique_point_of_cotangent_subsingleton
      (vToBase p A) (vIdentityPoint p A) (vKernel_unique_point p A hA) hcot
  have hone := congrFun (Scheme.Hom.finrank_eq_one_of_isIso (vToBase p A))
    (IsLocalRing.closedPoint K)
  have hp : p ^ g = 1 := (vKernel_finrank p A).symm.trans hone
  have hlt : 1 < p ^ g := one_lt_pow₀ (Fact.out : p.Prime).one_lt hg
  exact (ne_of_gt hlt) hp

end SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup
