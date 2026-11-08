/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.VerschiebungFrobeniusCriterion
import SupersingularCurves.Geometry.PRankZeroVerschiebungKernel

/-!
# The actual Frobenius and Verschiebung kernels when dV vanishes

Vanishing of the actual Verschiebung cotangent gives a residual Frobenius
factor that is an actual isomorphism. Therefore its actual Frobenius and
Verschiebung kernels coincide, on every test scheme. The previously constructed
simultaneous kernel is isomorphic to the actual Verschiebung fibre, and has
finite scheme rank p^g. These statements do not construct an elliptic factor
or assert an elliptic-product classification.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian SchemeFrobenius PerfectFieldVerschiebung

variable {K : Type u} [Field K] [IsAlgClosed K]
variable (p : ℕ) [Fact p.Prime] [CharP K p]
variable {g : ℕ} (A : AbelianVariety K g)
variable (hV : GroupScheme.verschiebungCotangent p A.group A.groupScheme_law_commutative = 0)

include hV

/-- Frobenius and Verschiebung have the same actual kernel condition on
every test scheme, including nonreduced schemes. -/
theorem frobenius_eq_zero_iff_verschiebung_eq_zero
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x : SchemeHomOver t (base p A)) :
    x.1 ≫ F p A = t ≫ twiceTwistZero p A ↔
      x.1 ≫ V p A = t ≫ zero A := by
  obtain ⟨e, he, _⟩ :=
    A.exists_frobenius_factor_iso_of_verschiebungCotangent_eq_zero p hV
  change F p A ≫ e.hom = V p A at he
  have hF0 : twistZero p A ≫ F p A = twiceTwistZero p A :=
    congrArg Subtype.val (relative_one p (base p A) (law p A) (𝟙 _))
  have he0 : twiceTwistZero p A ≫ e.hom = zero A := by
    rw [← hF0, Category.assoc, he]
    exact verschiebung_zero p A.group.X.hom (GroupScheme.law A.group)
      A.groupScheme_law_commutative
  constructor
  · intro hx
    rw [← he, ← Category.assoc, hx, Category.assoc, he0]
  · intro hx
    apply (cancel_mono e.hom).mp
    rw [Category.assoc, he, hx, Category.assoc, he0]

/-- Actual Frobenius is the constant identity morphism on the actual
Verschiebung fibre when dV vanishes. -/
theorem vInclusion_frobenius_of_verschiebungCotangent_eq_zero :
    vInclusion p A ≫ F p A = vToBase p A ≫ twiceTwistZero p A := by
  let x : SchemeHomOver (vToBase p A) (base p A) :=
    ⟨vInclusion p A, vInclusion_over p A⟩
  exact (frobenius_eq_zero_iff_verschiebung_eq_zero p A hV (vToBase p A) x).mpr
    pullback.condition

/-- The simultaneous actual kernel is precisely the actual V-kernel,
as witnessed by an isomorphism whose forward map is the original inclusion. -/
def simultaneousKernelIsoVKernel : scheme p A ≅ vKernel p A where
  hom := pullback.fst (vInclusion p A ≫ F p A) (twiceTwistZero p A)
  inv := pullback.lift (𝟙 _) (vToBase p A)
    (by simpa only [Category.id_comp] using
      vInclusion_frobenius_of_verschiebungCotangent_eq_zero p A hV)
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp]
    · simp only [Category.assoc, pullback.lift_snd, Category.id_comp]
      rw [← vInclusion_over, ← Category.assoc]
      exact structure_eq_snd p A
  inv_hom_id := pullback.lift_fst _ _ _

/-- The isomorphism preserves the ambient closed-subscheme inclusion. -/
@[simp] theorem simultaneousKernelIsoVKernel_hom_inclusion :
    (simultaneousKernelIsoVKernel p A hV).hom ≫ vInclusion p A = inclusion p A := rfl

/-- The isomorphism preserves the actual structure morphism over K. -/
@[simp] theorem simultaneousKernelIsoVKernel_hom_toBase :
    (simultaneousKernelIsoVKernel p A hV).hom ≫ vToBase p A = toBase p A := by
  rw [← vInclusion_over, ← Category.assoc]
  rfl

/-- The actual finite simultaneous kernel has scheme rank p^g when the
actual Verschiebung cotangent vanishes. -/
theorem simultaneousKernel_finrank_of_verschiebungCotangent_eq_zero :
    (toBase p A).finrank (IsLocalRing.closedPoint K) = p ^ g := by
  rw [← simultaneousKernelIsoVKernel_hom_toBase p A hV,
    Scheme.Hom.finrank_comp_left_of_isIso]
  exact vKernel_finrank p A

end SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup
