/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Jacobson.Ring

/-!
# Detection of projective-module sections on closed fibres

Over a reduced Jacobson ring, an element of a projective module is zero if
its image in every maximal-ideal fibre is zero. Projectivity embeds the module
into a free module. Every coordinate then belongs to every maximal ideal,
and hence to the zero Jacobson radical. No finite-generation assumption on
the module is required.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.Geometry.ReducedModuleDetection

open scoped TensorProduct

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-- The tensor description of vanishing in a maximal-ideal fibre agrees
with membership in the ideal times the module. The statement holds for
every ideal, without a maximality assumption. -/
theorem one_tmul_eq_zero_iff_mem_smul (I : Ideal A) (m : M) :
    (1 : A ⧸ I) ⊗ₜ[A] m = 0 ↔ m ∈ I • (⊤ : Submodule A M) := by
  rw [← (TensorProduct.quotTensorEquivQuotSMul M I).map_eq_zero_iff]
  simp only [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul,
    Submodule.Quotient.mk_eq_zero]

/-- In a reduced Jacobson ring, scalar membership in every maximal ideal
implies vanishing. -/
theorem eq_zero_of_mem_maximal [IsReduced A] [IsJacobsonRing A] (a : A)
    (h : ∀ I : Ideal A, I.IsMaximal → a ∈ I) : a = 0 := by
  have ha : a ∈ (⊥ : Ideal A).jacobson := by
    apply Ideal.mem_sInf.mpr
    intro I hI
    exact h I hI.2
  rw [IsJacobsonRing.out' _ Ideal.isRadical_bot] at ha
  exact ha

/-- Scalar-valued linear functionals followed by reduction at maximal
ideals detect a section of a projective module. -/
theorem eq_zero_of_forall_dual_mem_maximal [IsReduced A] [IsJacobsonRing A]
    [Module.Projective A M] (m : M)
    (h : ∀ I : Ideal A, I.IsMaximal → ∀ l : M →ₗ[A] A, l m ∈ I) : m = 0 := by
  obtain ⟨s, hs⟩ := Module.Projective.out (R := A) (P := M)
  apply hs.injective
  rw [map_zero]
  ext j
  apply eq_zero_of_mem_maximal
  intro I hI
  exact h I hI ((Finsupp.lapply j).comp s)

/-- A projective module over a reduced Jacobson ring has no nonzero
section contained in every maximal ideal times the module. -/
theorem eq_zero_of_mem_maximal_smul [IsReduced A] [IsJacobsonRing A]
    [Module.Projective A M] (m : M)
    (h : ∀ I : Ideal A, I.IsMaximal → m ∈ I • (⊤ : Submodule A M)) : m = 0 := by
  apply eq_zero_of_forall_dual_mem_maximal (A := A) m
  intro I hI l
  have hm := Submodule.smul_top_le_comap_smul_top I l (h I hI)
  simpa using hm

/-- Closed fibres detect sections of a projective module over a reduced
Jacobson ring. This uses the actual residue-field tensor product. -/
theorem eq_zero_of_maximal_fibre_zero [IsReduced A] [IsJacobsonRing A]
    [Module.Projective A M] (m : M)
    (h : ∀ I : Ideal A, I.IsMaximal → (1 : A ⧸ I) ⊗ₜ[A] m = 0) : m = 0 := by
  apply eq_zero_of_mem_maximal_smul (A := A) m
  intro I hI
  exact (one_tmul_eq_zero_iff_mem_smul I m).mp (h I hI)

end SupersingularCurves.Geometry.ReducedModuleDetection
