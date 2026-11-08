/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.EllipticVerschiebungKernel
import SupersingularCurves.Geometry.PointedCotangentKernel
import SupersingularCurves.Geometry.PointedCotangentDimension

/-!
# The actual elliptic Verschiebung kernel fibre

The kernel is the scheme-theoretic fibre over the genuine identity section.
Supersingularity implies that it has a unique rational point. A nonzero
Verschiebung cotangent map would force this fibre's cotangent space to vanish,
using the actual smooth relative dimension one and its closed immersion into
the Frobenius twist.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.AbelianVariety
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open SchemeFrobenius PerfectFieldVerschiebung

variable (p : ℕ) [Fact p.Prime]
variable {K : Type u} [Field K] [CharP K p] [IsAlgClosed K]
variable (E : AbelianVariety K 1)

/-- The actual Verschiebung morphism of the elliptic abelian variety. -/
abbrev ellipticVerschiebung : Twist p E.group.X.hom ⟶ E.group.X.left :=
  verschiebung p E.group.X.hom (GroupScheme.law E.group)
    (GroupScheme.law_commutative E.group)

/-- The scheme-theoretic fibre of Verschiebung over the actual identity. -/
abbrev verschiebungKernelScheme : Scheme.{u} :=
  pullback (ellipticVerschiebung p E) (GroupScheme.zero E.group).1

def verschiebungKernelToBase : verschiebungKernelScheme p E ⟶ Spec (CommRingCat.of K) :=
  pullback.snd (ellipticVerschiebung p E) (GroupScheme.zero E.group).1

def verschiebungKernelInclusion : verschiebungKernelScheme p E ⟶ Twist p E.group.X.hom :=
  pullback.fst (ellipticVerschiebung p E) (GroupScheme.zero E.group).1

theorem verschiebungKernelInclusion_over :
    verschiebungKernelInclusion p E ≫ toBase p E.group.X.hom =
      verschiebungKernelToBase p E := by
  rw [← verschiebung_over p E.group.X.hom (GroupScheme.law E.group)
    (GroupScheme.law_commutative E.group), ← Category.assoc]
  change (pullback.fst _ _ ≫ ellipticVerschiebung p E) ≫ E.group.X.hom = _
  rw [pullback.condition, Category.assoc, (GroupScheme.zero E.group).2, Category.comp_id]
  rfl

/-- The identity section belongs to the actual Verschiebung fibre. -/
def verschiebungKernelZero :
    SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (verschiebungKernelToBase p E) :=
  ⟨pullback.lift (GroupScheme.twistZero p E.group).1 (𝟙 _)
    (by
      simpa only [Category.id_comp, GroupScheme.twistZero, ellipticVerschiebung,
        GroupScheme.zero] using
        (verschiebung_zero p E.group.X.hom (GroupScheme.law E.group)
          (GroupScheme.law_commutative E.group))),
    pullback.lift_snd _ _ _⟩

theorem verschiebungKernelZero_inclusion :
    (verschiebungKernelZero p E).1 ≫ verschiebungKernelInclusion p E =
      (GroupScheme.twistZero p E.group).1 :=
  pullback.lift_fst _ _ _

instance verschiebungKernelInclusion_mono : Mono (verschiebungKernelInclusion p E) := by
  let : IsClosedImmersion (GroupScheme.zero E.group).1 :=
    isClosedImmersion_of_comp_eq_id E.group.X.hom (GroupScheme.zero E.group).1
      (GroupScheme.zero E.group).2
  change Mono (pullback.fst _ _)
  infer_instance

/-- The unique rational point is proved using the original independent
geometric p-torsion definition and the actual pullback universal property. -/
theorem IsSupersingularElliptic.verschiebungKernel_unique_point
    (hE : E.IsSupersingularElliptic p)
    (q : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (verschiebungKernelToBase p E)) :
    q = verschiebungKernelZero p E := by
  let x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (toBase p E.group.X.hom) :=
    ⟨q.1 ≫ verschiebungKernelInclusion p E, by
      rw [Category.assoc, verschiebungKernelInclusion_over, q.2]⟩
  have hx : x.1 ≫ ellipticVerschiebung p E = (GroupScheme.zero E.group).1 := by
    change (q.1 ≫ pullback.fst _ _) ≫ ellipticVerschiebung p E = _
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (q.1 ≫ verschiebungKernelToBase p E) ≫ (GroupScheme.zero E.group).1 = _
    rw [q.2, Category.id_comp]
  have hz := hE.verschiebung_kernel_trivial p x hx
  apply Subtype.ext
  apply pullback.hom_ext
  · exact (congrArg Subtype.val hz).trans (verschiebungKernelZero_inclusion p E).symm
  · exact q.2.trans (verschiebungKernelZero p E).2.symm

/-- A nonzero elliptic Verschiebung differential would give a zero
cotangent space for its genuine kernel fibre. -/
theorem verschiebungKernel_cotangent_subsingleton_of_nonzero
    (hV : GroupScheme.verschiebungCotangent p E.group
      (GroupScheme.law_commutative E.group) ≠ 0) :
    Subsingleton (PointedCotangent.Cotangent (verschiebungKernelToBase p E)
      (verschiebungKernelZero p E)) := by
  let : SmoothOfRelativeDimension 1 (toBase p E.group.X.hom) := by
    change SmoothOfRelativeDimension 1 (pullback.snd E.group.X.hom (baseMap p K))
    infer_instance
  have hdim := PointedCotangent.finrank_eq_relativeDimension
    (toBase p E.group.X.hom) (GroupScheme.twistZero p E.group) 1
  have hsurj := surjective_of_nonzero_of_finrank_eq_one hdim hV
  exact PointedCotangent.cotangent_subsingleton_of_mono_comp_eq_constant
    (verschiebungKernelToBase p E) (verschiebungKernelZero p E)
    (verschiebungKernelInclusion p E) (verschiebungKernelInclusion_over p E)
    (verschiebungKernelZero_inclusion p E) (ellipticVerschiebung p E)
    (verschiebung_over p E.group.X.hom (GroupScheme.law E.group)
      (GroupScheme.law_commutative E.group))
    (verschiebung_zero p E.group.X.hom (GroupScheme.law E.group)
      (GroupScheme.law_commutative E.group))
    pullback.condition hsurj

end SupersingularCurves.Geometry.AbelianVariety
