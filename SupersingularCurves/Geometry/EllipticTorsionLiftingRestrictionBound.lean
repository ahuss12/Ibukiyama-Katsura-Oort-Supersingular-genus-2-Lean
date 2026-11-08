/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.EllipticTorsionLiftingFrobeniusProjection
import SupersingularCurves.Geometry.EllipticTorsionLiftingResidualCoordinates
import SupersingularCurves.Geometry.EllipticTorsionLiftingNaturality

/-! # The actual restriction image on the Frobenius kernel lies in F_{p²} -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.EllipticTorsionRealization
open CategoryTheory AlgebraicGeometry SchemeFrobenius TorsionLevels
variable {K : Type u} [Field K] [IsAlgClosed K]
  (p : ℕ) [Fact p.Prime] [CharP K p] (E : AbelianVariety K 1)
  (hV : GroupScheme.verschiebungCotangent p E.group E.groupScheme_law_commutative = 0)

instance frobeniusKernelToTorsion_mono : Mono (frobeniusKernelToTorsion p E) :=
  mono_of_mono_fac (frobeniusKernelToTorsion_inclusion p E)

/-- An actual torsion morphism and its actual kernel restriction commute
with the constructed finite-flat Frobenius projection. -/
theorem absoluteProjection_naturality
    (f : torsion p E ⟶ torsion p E)
    (r : frobeniusKernel p E ⟶ frobeniusKernel p E)
    (hr : r ≫ frobeniusKernelToTorsion p E = frobeniusKernelToTorsion p E ≫ f) :
    f ≫ absoluteProjection p E hV = absoluteProjection p E hV ≫ r := by
  apply (cancel_mono (frobeniusKernelToTorsion p E)).mp
  simp only [Category.assoc, absoluteProjection_toTorsion, hr]
  rw [← Category.assoc, absoluteProjection_toTorsion]
  exact (Scheme.frobenius_comp f p 1 (Fact.out : p.Prime)
    (globalChar p (torsionBase p E)) (globalChar p (torsionBase p E))).symm

/-- Actual finite-flat cancellation proves commutation with the residual
kernel automorphism. Only the actual restriction and V-naturality squares
are supplied. No commutation with the residual automorphism is assumed. -/
theorem restriction_residual_commute
    (f : torsion p E ⟶ torsion p E)
    (r : frobeniusKernel p E ⟶ frobeniusKernel p E)
    (hr : r ≫ frobeniusKernelToTorsion p E = frobeniusKernelToTorsion p E ≫ f)
    (hv : f ≫ ambientOnLevel E p p = ambientOnLevel E p p ≫ f) :
    r ≫ (residualKernelIso p E hV).hom = (residualKernelIso p E hV).hom ≫ r := by
  have hq := absoluteProjection_naturality p E hV f r hr
  apply (cancel_epi (absoluteProjection p E hV)).mp
  apply (cancel_mono (frobeniusKernelToTorsion p E)).mp
  simp only [Category.assoc]
  calc
    absoluteProjection p E hV ≫ r ≫ (residualKernelIso p E hV).hom ≫
        frobeniusKernelToTorsion p E =
      f ≫ absoluteProjection p E hV ≫ (residualKernelIso p E hV).hom ≫
        frobeniusKernelToTorsion p E := by
          simpa only [Category.assoc] using congrArg
            (fun z => z ≫ (residualKernelIso p E hV).hom ≫ frobeniusKernelToTorsion p E)
            hq.symm
    _ = f ≫ ambientOnLevel E p p := by rw [absoluteProjection_residual_toTorsion]
    _ = ambientOnLevel E p p ≫ f := hv
    _ = absoluteProjection p E hV ≫ (residualKernelIso p E hV).hom ≫
        frobeniusKernelToTorsion p E ≫ f := by
          rw [← absoluteProjection_residual_toTorsion p E hV]
          simp only [Category.assoc]
    _ = absoluteProjection p E hV ≫ (residualKernelIso p E hV).hom ≫ r ≫
        frobeniusKernelToTorsion p E := by rw [hr]

namespace FrobeniusKernelHopf
variable (HF : FrobeniusKernelHopf p E)

include hV in
/-- The scalar of an actual Frobenius-kernel Hopf endomorphism extending
to a Hopf endomorphism of actual E[p] belongs to F_{p²}. The V-naturality
and residual-commutation assertions are proved from the actual finite
torsion map, rather than included among the hypotheses. -/
theorem cotangentScalar_pow_sq_of_torsion_extension
    (HT : TorsionLevels.Presentation E p)
    (φ : HF.Coord →ₐc[K] HF.Coord) (ψ : HT.Coord →ₐc[K] HT.Coord)
    (hr : HF.endScheme φ ≫ frobeniusKernelToTorsion p E =
      frobeniusKernelToTorsion p E ≫ TorsionLevels.Presentation.schemeMap HT HT ψ) :
    HF.cotangentScalar φ ^ (p ^ 2) = HF.cotangentScalar φ := by
  apply HF.cotangentScalar_pow_sq_of_residual_commute hV φ
  exact restriction_residual_commute p E hV
    (TorsionLevels.Presentation.schemeMap HT HT ψ) (HF.endScheme φ) hr
    (TorsionLevels.Presentation.ambient_naturality p HT HT ψ)

include hV in
/-- Version choosing the independently constructed presentation of the
actual p-torsion scheme internally. -/
theorem cotangentScalar_pow_sq_of_constructed_torsion_extension
    (φ : HF.Coord →ₐc[K] HF.Coord)
    (ψ : (TorsionLevels.presentation E p (Fact.out : p.Prime).ne_zero).Coord →ₐc[K]
      (TorsionLevels.presentation E p (Fact.out : p.Prime).ne_zero).Coord)
    (hr : HF.endScheme φ ≫ frobeniusKernelToTorsion p E =
      frobeniusKernelToTorsion p E ≫ TorsionLevels.Presentation.schemeMap
        (TorsionLevels.presentation E p (Fact.out : p.Prime).ne_zero)
        (TorsionLevels.presentation E p (Fact.out : p.Prime).ne_zero) ψ) :
    HF.cotangentScalar φ ^ (p ^ 2) = HF.cotangentScalar φ :=
  HF.cotangentScalar_pow_sq_of_torsion_extension p E hV _ φ ψ hr

end FrobeniusKernelHopf
end SupersingularCurves.Geometry.EllipticTorsionRealization
