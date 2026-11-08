/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.EllipticTorsionLiftingResidualKernel

/-! # The actual finite-flat Frobenius projection E[p]→ker(F) when dV=0 -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.EllipticTorsionRealization
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SchemeFrobenius TorsionLevels
open AbelianVariety
variable {K : Type u} [Field K] [IsAlgClosed K]
  (p : ℕ) [Fact p.Prime] [CharP K p] (E : AbelianVariety K 1)
  (hV : GroupScheme.verschiebungCotangent p E.group E.groupScheme_law_commutative = 0)

theorem projection_absolute_residual :
    projection p E.group.X.hom ≫ absolute p E.group.X.hom ≫
      (residualAbsoluteIso E p hV).hom = ellipticVerschiebung p E := by
  rw [← ambientVerschiebung_eq_absolute_residual E p hV]
  exact IsIso.hom_inv_id_assoc (projection p E.group.X.hom) _

/-- The actual twist projection sends the actual V-kernel to the actual
F-kernel, with its genuine Frobenius field map. -/
def vKernelToFKernel : verschiebungKernelScheme p E ⟶ frobeniusKernel p E :=
  pullback.lift (verschiebungKernelInclusion p E ≫ projection p E.group.X.hom)
    (verschiebungKernelToBase p E ≫ baseMap p K) (by
      apply (cancel_mono (projection p E.group.X.hom)).mp
      simp only [Category.assoc, relative_projection, twistZero_projection]
      apply (cancel_mono (residualAbsoluteIso E p hV).hom).mp
      simp only [Category.assoc]
      rw [projection_absolute_residual]
      change (pullback.fst _ _ ≫ ellipticVerschiebung p E) = _
      rw [pullback.condition]
      simp only [Category.assoc, residualAbsoluteIso_zero, IsIso.hom_inv_id_assoc]
      rfl)

/-- Inverse twist projection gives the inverse map on the actual kernels. -/
def fKernelToVKernel : frobeniusKernel p E ⟶ verschiebungKernelScheme p E :=
  pullback.lift (frobeniusKernelInclusion p E ≫ inv (projection p E.group.X.hom))
    (frobeniusKernelBase p E ≫ inv (baseMap p K)) (by
      rw [Category.assoc]
      change frobeniusKernelInclusion p E ≫ ambientVerschiebung E p = _
      rw [ambientVerschiebung_eq_absolute_residual E p hV, ← Category.assoc,
        frobeniusKernelInclusion_absolute]
      simp only [Category.assoc, residualAbsoluteIso_zero, IsIso.hom_inv_id_assoc])

@[reassoc]
theorem vKernelToFKernel_inclusion :
    vKernelToFKernel p E hV ≫ frobeniusKernelInclusion p E =
      verschiebungKernelInclusion p E ≫ projection p E.group.X.hom := pullback.lift_fst _ _ _

@[reassoc]
theorem fKernelToVKernel_inclusion :
    fKernelToVKernel p E hV ≫ verschiebungKernelInclusion p E =
      frobeniusKernelInclusion p E ≫ inv (projection p E.group.X.hom) := pullback.lift_fst _ _ _

/-- The two actual scheme kernels are isomorphic, retaining the field twist. -/
def vKernelIsoFKernel : verschiebungKernelScheme p E ≅ frobeniusKernel p E where
  hom := vKernelToFKernel p E hV
  inv := fKernelToVKernel p E hV
  hom_inv_id := by
    apply (cancel_mono (verschiebungKernelInclusion p E)).mp
    simp only [Category.assoc, fKernelToVKernel_inclusion,
      vKernelToFKernel_inclusion_assoc, IsIso.hom_inv_id, Category.comp_id,
      Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (frobeniusKernelInclusion p E)).mp
    simp only [Category.assoc, vKernelToFKernel_inclusion,
      fKernelToVKernel_inclusion_assoc, IsIso.inv_hom_id, Category.comp_id,
      Category.id_comp]

/-- The actual Frobenius projection, constructed from the already proved
finite-flat projection to ker(V) and the actual kernel isomorphism. -/
def absoluteProjection : torsion p E ⟶ frobeniusKernel p E :=
  frobeniusOnTorsion p E ≫ (vKernelIsoFKernel p E hV).hom

instance absoluteProjection_isFinite : IsFinite (absoluteProjection p E hV) := by
  unfold absoluteProjection
  infer_instance

instance absoluteProjection_flat : Flat (absoluteProjection p E hV) := by
  unfold absoluteProjection
  infer_instance

instance absoluteProjection_surjective : Surjective (absoluteProjection p E hV) := by
  unfold absoluteProjection
  infer_instance

@[reassoc]
theorem absoluteProjection_inclusion :
    absoluteProjection p E hV ≫ frobeniusKernelInclusion p E =
      torsionInclusion p E ≫ absolute p E.group.X.hom := by
  change (frobeniusOnTorsion p E ≫ vKernelToFKernel p E hV) ≫ _ = _
  rw [Category.assoc, vKernelToFKernel_inclusion, ← Category.assoc,
    frobeniusOnTorsion_inclusion, Category.assoc, relative_projection]

/-- The actual projection followed by ker(F)→E[p] is absolute Frobenius of
the entire p-torsion scheme, including its nonreduced structure. -/
@[reassoc]
theorem absoluteProjection_toTorsion :
    absoluteProjection p E hV ≫ frobeniusKernelToTorsion p E =
      absolute p (torsionBase p E) := by
  apply (cancel_mono (torsionInclusion p E)).mp
  rw [Category.assoc, frobeniusKernelToTorsion_inclusion, absoluteProjection_inclusion]
  exact (Scheme.frobenius_comp (torsionInclusion p E) p 1 (Fact.out : p.Prime)
    (globalChar p (torsionBase p E)) (globalChar p E.group.X.hom)).symm

/-- The projection followed by the actual residual ker(F) automorphism
recovers actual ambient Verschiebung restricted to E[p]. -/
@[reassoc]
theorem absoluteProjection_residual_toTorsion :
    absoluteProjection p E hV ≫ (residualKernelIso p E hV).hom ≫
      frobeniusKernelToTorsion p E = ambientOnLevel E p p := by
  apply (cancel_mono (torsionInclusion p E)).mp
  simp only [Category.assoc, frobeniusKernelToTorsion_inclusion,
    residualKernelIso_inclusion, absoluteProjection_inclusion_assoc]
  rw [← ambientVerschiebung_eq_absolute_residual E p hV]
  exact (ambientOnLevel_inclusion E p p).symm

end SupersingularCurves.Geometry.EllipticTorsionRealization
