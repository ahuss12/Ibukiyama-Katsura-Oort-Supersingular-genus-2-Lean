/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.EllipticTorsionLiftingResidual
import SupersingularCurves.Geometry.EllipticTorsionLiftingHeightOne

/-! # Semilinear automorphisms on the actual elliptic Frobenius kernel -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.EllipticTorsionRealization
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open SchemeFrobenius
variable {K : Type u} [Field K] [IsAlgClosed K]
  (p : ℕ) [Fact p.Prime] [CharP K p] (E : AbelianVariety K 1)

theorem twistZero_projection :
    (GroupScheme.twistZero p E.group).1 ≫ projection p E.group.X.hom =
      baseMap p K ≫ (GroupScheme.zero E.group).1 := by
  rw [← GroupScheme.relative_zero, Category.assoc, relative_projection,
    ← baseMap_eq_absolute p]
  exact (Scheme.frobenius_comp (GroupScheme.zero E.group).1 p 1
    (Fact.out : p.Prime) (Scheme.natCast_eq_zero_ΓSpec (CharP.cast_eq_zero K p))
    (globalChar p E.group.X.hom)).symm

@[reassoc]
theorem frobeniusKernelInclusion_absolute :
    frobeniusKernelInclusion p E ≫ absolute p E.group.X.hom =
      frobeniusKernelBase p E ≫ baseMap p K ≫ (GroupScheme.zero E.group).1 := by
  rw [← relative_projection p E.group.X.hom, ← Category.assoc]
  change (pullback.fst _ _ ≫ relative p E.group.X.hom) ≫ _ = _
  rw [pullback.condition, Category.assoc, twistZero_projection]

variable {E}

/-- Any actual semilinear pointed morphism preserves the actual Frobenius
kernel. The scalar map is allowed to be an arbitrary field-scheme morphism. -/
def semilinearRestriction (f : E.group.X.left ⟶ E.group.X.left)
    (β : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K))
    (hf : f ≫ E.group.X.hom = E.group.X.hom ≫ β)
    (hzero : (GroupScheme.zero E.group).1 ≫ f = β ≫ (GroupScheme.zero E.group).1) :
    frobeniusKernel p E ⟶ frobeniusKernel p E :=
  pullback.lift (frobeniusKernelInclusion p E ≫ f) (frobeniusKernelBase p E ≫ β) (by
    apply (cancel_mono (projection p E.group.X.hom)).mp
    simp only [Category.assoc, relative_projection, twistZero_projection]
    have hn := Scheme.frobenius_comp f p 1 (Fact.out : p.Prime)
      (globalChar p E.group.X.hom) (globalChar p E.group.X.hom)
    change absolute p E.group.X.hom ≫ f = f ≫ absolute p E.group.X.hom at hn
    rw [← hn, ← Category.assoc, frobeniusKernelInclusion_absolute, Category.assoc,
      Category.assoc, hzero]
    have hβ := Scheme.frobenius_comp β p 1 (Fact.out : p.Prime)
      (Scheme.natCast_eq_zero_ΓSpec (CharP.cast_eq_zero K p))
      (Scheme.natCast_eq_zero_ΓSpec (CharP.cast_eq_zero K p))
    rw [baseMap_eq_absolute] at hβ
    change baseMap p K ≫ β = β ≫ baseMap p K at hβ
    rw [← Category.assoc (baseMap p K), hβ, Category.assoc])

@[reassoc]
theorem semilinearRestriction_inclusion (f : E.group.X.left ⟶ E.group.X.left)
    (β : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K))
    (hf : f ≫ E.group.X.hom = E.group.X.hom ≫ β)
    (hzero : (GroupScheme.zero E.group).1 ≫ f = β ≫ (GroupScheme.zero E.group).1) :
    semilinearRestriction p f β hf hzero ≫ frobeniusKernelInclusion p E =
      frobeniusKernelInclusion p E ≫ f := pullback.lift_fst _ _ _

@[reassoc]
theorem semilinearRestriction_over (f : E.group.X.left ⟶ E.group.X.left)
    (β : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K))
    (hf : f ≫ E.group.X.hom = E.group.X.hom ≫ β)
    (hzero : (GroupScheme.zero E.group).1 ≫ f = β ≫ (GroupScheme.zero E.group).1) :
    semilinearRestriction p f β hf hzero ≫ frobeniusKernelBase p E =
      frobeniusKernelBase p E ≫ β := pullback.lift_snd _ _ _

@[reassoc]
theorem semilinearRestriction_zero (f : E.group.X.left ⟶ E.group.X.left)
    (β : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K))
    (hf : f ≫ E.group.X.hom = E.group.X.hom ≫ β)
    (hzero : (GroupScheme.zero E.group).1 ≫ f = β ≫ (GroupScheme.zero E.group).1) :
    (frobeniusKernelZero p E).1 ≫ semilinearRestriction p f β hf hzero =
      β ≫ (frobeniusKernelZero p E).1 := by
  apply (cancel_mono (frobeniusKernelInclusion p E)).mp
  simp only [Category.assoc, semilinearRestriction_inclusion,
    frobeniusKernelZero_inclusion_assoc, frobeniusKernelZero_inclusion, hzero]

/-- An actual semilinear pointed automorphism restricts to an actual
automorphism of the entire nonreduced Frobenius kernel. -/
def semilinearKernelIso (e : E.group.X.left ≅ E.group.X.left)
    (β : Spec (CommRingCat.of K) ≅ Spec (CommRingCat.of K))
    (he : e.hom ≫ E.group.X.hom = E.group.X.hom ≫ β.hom)
    (hzero : (GroupScheme.zero E.group).1 ≫ e.hom = β.hom ≫ (GroupScheme.zero E.group).1) :
    frobeniusKernel p E ≅ frobeniusKernel p E := by
  have hi : e.inv ≫ E.group.X.hom = E.group.X.hom ≫ β.inv := by
    apply (cancel_epi e.hom).mp
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, ← Category.assoc,
      he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hzi : (GroupScheme.zero E.group).1 ≫ e.inv = β.inv ≫ (GroupScheme.zero E.group).1 := by
    apply (cancel_epi β.hom).mp
    rw [← Category.assoc, ← hzero, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.hom_inv_id_assoc]
  refine ⟨semilinearRestriction p e.hom β.hom he hzero,
    semilinearRestriction p e.inv β.inv hi hzi, ?_, ?_⟩
  · apply (cancel_mono (frobeniusKernelInclusion p E)).mp
    simp only [Category.assoc, semilinearRestriction_inclusion,
      semilinearRestriction_inclusion_assoc, Iso.hom_inv_id, Category.comp_id,
      Category.id_comp]
  · apply (cancel_mono (frobeniusKernelInclusion p E)).mp
    simp only [Category.assoc, semilinearRestriction_inclusion,
      semilinearRestriction_inclusion_assoc, Iso.inv_hom_id, Category.comp_id,
      Category.id_comp]

variable (E)
variable (hV : GroupScheme.verschiebungCotangent p E.group E.groupScheme_law_commutative = 0)

/-- The residual automorphism constructed from actual dV=0 acts on the
actual elliptic Frobenius kernel; no local automorphism is supplied. -/
def residualKernelIso : frobeniusKernel p E ≅ frobeniusKernel p E :=
  semilinearKernelIso p (TorsionLevels.residualAbsoluteIso E p hV)
    ((asIso (baseMap p K)).symm ≪≫ (asIso (baseMap p K)).symm)
    (TorsionLevels.residualAbsoluteIso_over E p hV)
    (TorsionLevels.residualAbsoluteIso_zero E p hV)

@[reassoc]
theorem residualKernelIso_inclusion :
    (residualKernelIso p E hV).hom ≫ frobeniusKernelInclusion p E =
      frobeniusKernelInclusion p E ≫ (TorsionLevels.residualAbsoluteIso E p hV).hom :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem residualKernelIso_over :
    (residualKernelIso p E hV).hom ≫ frobeniusKernelBase p E =
      frobeniusKernelBase p E ≫ inv (baseMap p K) ≫ inv (baseMap p K) :=
  pullback.lift_snd _ _ _

@[reassoc]
theorem residualKernelIso_zero :
    (frobeniusKernelZero p E).1 ≫ (residualKernelIso p E hV).hom =
      inv (baseMap p K) ≫ inv (baseMap p K) ≫ (frobeniusKernelZero p E).1 := by
  apply (cancel_mono (frobeniusKernelInclusion p E)).mp
  rw [Category.assoc, residualKernelIso_inclusion,
    ← Category.assoc, frobeniusKernelZero_inclusion,
    TorsionLevels.residualAbsoluteIso_zero]
  simp only [Category.assoc, frobeniusKernelZero_inclusion]

end SupersingularCurves.Geometry.EllipticTorsionRealization
