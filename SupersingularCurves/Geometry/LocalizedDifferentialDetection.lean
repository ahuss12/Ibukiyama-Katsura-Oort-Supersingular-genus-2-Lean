/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Detecting differentials using localized scalar-valued duals

A scalar-valued dual of the differential module extends across a formally
étale algebra map, using the canonical base-change isomorphism for Kähler
differentials. Thus vanishing modulo an ideal after this base change forces
every dual value to belong to the contracted ideal. The maximal-ideal form
applies in particular to localizations at points of a smooth scheme.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.Geometry.LocalizedDifferentialDetection

open KaehlerDifferential

variable (K A S : Type*) [CommRing K] [CommRing A] [CommRing S]
  [Algebra K A] [Algebra K S] [Algebra A S] [IsScalarTower K A S]
  [Algebra.FormallyEtale A S]

/-- Extend a scalar-valued differential dual across a formally étale
algebra map by the canonical differential base-change isomorphism. -/
def extendDual (l : Ω[A⁄K] →ₗ[A] A) : Ω[S⁄K] →ₗ[S] S :=
  (TensorProduct.AlgebraTensorModule.rid A S S).toLinearMap ∘ₗ
    l.baseChange S ∘ₗ (tensorKaehlerEquivOfFormallyEtale K A S).symm.toLinearMap

/-- The extended dual has the required value on differentials from the
original algebra. -/
theorem extendDual_D (l : Ω[A⁄K] →ₗ[A] A) (a : A) :
    extendDual K A S l (D K S (algebraMap A S a)) = algebraMap A S (l (D K A a)) := by
  simp [extendDual, tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    Algebra.smul_def]

/-- If the pulled-back differential belongs to an ideal times the
differential module, every original dual value lies in its contraction. -/
theorem dual_D_mem_under_of_D_mem_smul (I : Ideal S) (a : A)
    (h : D K S (algebraMap A S a) ∈ I • (⊤ : Submodule S Ω[S⁄K]))
    (l : Ω[A⁄K] →ₗ[A] A) : l (D K A a) ∈ I.under A := by
  have hl := Submodule.smul_top_le_comap_smul_top I (extendDual K A S l) h
  simpa only [Submodule.mem_comap, extendDual_D, smul_eq_mul, Ideal.mul_top,
    Ideal.mem_under] using hl

/-- Specialization to the closed-point ideal of a local algebra. -/
theorem dual_D_mem_under_maximalIdeal [IsLocalRing S] (a : A)
    (h : D K S (algebraMap A S a) ∈
      IsLocalRing.maximalIdeal S • (⊤ : Submodule S Ω[S⁄K]))
    (l : Ω[A⁄K] →ₗ[A] A) :
    l (D K A a) ∈ (IsLocalRing.maximalIdeal S).under A :=
  dual_D_mem_under_of_D_mem_smul K A S (IsLocalRing.maximalIdeal S) a h l

/-- A named prime or maximal ideal may be supplied through the usual
localization contraction equality. -/
theorem dual_D_mem_of_D_mem_maximalIdeal_smul [IsLocalRing S]
    (P : Ideal A) (hP : (IsLocalRing.maximalIdeal S).under A = P) (a : A)
    (h : D K S (algebraMap A S a) ∈
      IsLocalRing.maximalIdeal S • (⊤ : Submodule S Ω[S⁄K]))
    (l : Ω[A⁄K] →ₗ[A] A) : l (D K A a) ∈ P := by
  rw [← hP]
  exact dual_D_mem_under_maximalIdeal K A S a h l

end SupersingularCurves.Geometry.LocalizedDifferentialDetection
