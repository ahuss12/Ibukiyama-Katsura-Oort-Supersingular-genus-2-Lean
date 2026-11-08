/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusLineBundle
import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensorPow_iso
import Theorems.Thm_AlgebraicGeometry_Polarisation_mem_kernelPts_iff_nonempty_pullback_translate_iso
import Theorems.Thm_AlgebraicGeometry_Polarisation_kernelPts_tensor_eq_of_inPicZero

/-! # Finite translation kernel of a genuine polarization root modulo Pic0 -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SupersingularCurves.Geometry.PolarisationRootNumerics
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open GoodReductionJacobian NeronModelInfra AlgebraicGeometry.Polarisation

variable (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}}
  (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)

/-- Isomorphic line bundles have the same actual translation stabilizer. -/
theorem kernelPts_eq_of_iso (M N : A.Modules) (e : M ≅ N) :
    kernelPts f L M = kernelPts f L N := by
  ext x
  rw [mem_kernelPts_iff_nonempty_pullback_translate_iso,
    mem_kernelPts_iff_nonempty_pullback_translate_iso]
  constructor
  · rintro ⟨h⟩
    exact ⟨(Scheme.Modules.pullback (L.translate x)).mapIso e.symm ≪≫ h ≪≫ e⟩
  · rintro ⟨h⟩
    exact ⟨(Scheme.Modules.pullback (L.translate x)).mapIso e ≪≫ h ≪≫ e.symm⟩

/-- Translation invariance of a line bundle implies invariance of every power.
The pullback/tensor argument is also used in the pinned FLT finite-by-sections proof. -/
theorem kernelPts_subset_tensorPow (R : A.Modules) (n : ℕ) :
    kernelPts f L R ⊆ kernelPts f L (R.tensorPow n) := by
  intro x hx
  obtain ⟨e⟩ := (mem_kernelPts_iff_nonempty_pullback_translate_iso k f L R x).mp hx
  obtain ⟨p⟩ := Scheme.Modules.nonempty_pullback_tensorPow_iso (L.translate x) R n
  exact (mem_kernelPts_iff_nonempty_pullback_translate_iso k f L (R.tensorPow n) x).mpr
    ⟨p ≪≫ Scheme.Modules.tensorPowMapIso e n⟩

/-- Finite kernel descends to a genuine root, including its Pic0 error. -/
theorem finite_kernelPts_of_root (M R P : A.Modules)
    (hR : Scheme.Modules.IsInvertible R) (hP : InPicZero f L P)
    (n : ℕ) (e : M ≅ R.tensorPow n ⊗ P) (hM : (kernelPts f L M).Finite) :
    (kernelPts f L R).Finite := by
  have hpow : (kernelPts f L (R.tensorPow n)).Finite := by
    rw [← kernelPts_tensor_eq_of_inPicZero k f L (R.tensorPow n)
      (FrobeniusLineBundle.tensorPower_invertible hR n) P hP]
    rw [← kernelPts_eq_of_iso k f L M _ e]
    exact hM
  exact hpow.subset (kernelPts_subset_tensorPow k f L R n)


end SupersingularCurves.Geometry.PolarisationRootNumerics
