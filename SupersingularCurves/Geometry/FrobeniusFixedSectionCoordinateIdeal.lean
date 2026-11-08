/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusInvariantIdeal
import Mathlib.RingTheory.GradedAlgebra.RingHom

/-! # Descent of the actual homogeneous relations among fixed sections -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
namespace SupersingularCurves.Geometry.FrobeniusDescent
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K] {R : Type u} [CommRing R] [Algebra K R]
variable {σ : Type v} (r : σ → R)
variable (𝓡 : ℕ → Submodule K R) [GradedAlgebra 𝓡]
variable (hr : ∀ i, r i ∈ 𝓡 1)

include hr in
/-- Polynomial evaluation at actual degree-one sections preserves degree. -/
theorem fixedSection_aeval_mem {n : ℕ} {F : MvPolynomial σ K}
    (hF : F.IsHomogeneous n) : aeval r F ∈ 𝓡 n := by
  classical
  rw [F.as_sum, map_sum]
  apply Submodule.sum_mem
  intro d hd
  rw [aeval_monomial, ← Algebra.smul_def]
  apply Submodule.smul_mem
  rw [hF.degree_eq_sum_deg_support hd]
  apply SetLike.prod_mem_graded
  intro i hi
  simpa only [smul_eq_mul, mul_one] using SetLike.pow_mem_graded (d i) (hr i)

/-- The canonical coordinate homomorphism into the actual section ring. -/
def fixedSectionGradedEvaluation : homogeneousSubmodule σ K →+*ᵍ 𝓡 where
  __ := (aeval r).toRingHom
  map_mem := fun h => fixedSection_aeval_mem r 𝓡 hr ((mem_homogeneousSubmodule _ _).mp h)

/-- The ideal is the literal kernel of evaluating polynomials in the sections. -/
abbrev fixedSectionRelationIdeal : Ideal (MvPolynomial σ K) := RingHom.ker (aeval r).toRingHom

include hr in
/-- The actual relation ideal is homogeneous. -/
theorem fixedSectionRelationIdeal_homogeneous (F : MvPolynomial σ K)
    (hF : F ∈ fixedSectionRelationIdeal r) (n : ℕ) :
    homogeneousComponent n F ∈ fixedSectionRelationIdeal r := by
  change aeval r (homogeneousComponent n F) = 0
  change aeval r F = 0 at hF
  have h := (fixedSectionGradedEvaluation r 𝓡 hr).map_directSumDecompose (x := F) (i := n)
  rw [show (DirectSum.decompose (homogeneousSubmodule σ K) F n : MvPolynomial σ K) =
      homogeneousComponent n F from MvPolynomial.decomposition.decompose'_apply F n] at h
  change aeval r (homogeneousComponent n F) = (DirectSum.decompose 𝓡 (aeval r F) n : R) at h
  rw [h, hF, DirectSum.decompose_zero]
  rfl

variable (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)
variable (θ : R →+* R) (hθ : ∀ (c : K) (x : R), θ (c • x) = c ^ (p ^ s) • θ x)
variable (hfixed : ∀ i, θ (r i) = r i)

include hθ hfixed in
/-- Evaluation intertwines coefficient Frobenius with the actual section action. -/
theorem fixedSection_aeval_coefficientFrobenius (F : MvPolynomial σ K) :
    aeval r (coefficientFrobenius p s F) = θ (aeval r F) := by
  have h : (aeval (R := K) r).toRingHom.comp (coefficientFrobenius p s) =
      θ.comp (aeval (R := K) r).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change aeval r (MvPolynomial.map (iterateFrobenius K p s) (C a)) = θ (aeval r (C a))
      rw [MvPolynomial.map_C, aeval_C, aeval_C]
      change algebraMap K R (a ^ p ^ s) = θ (algebraMap K R a)
      have h := hθ a 1
      simpa only [Algebra.smul_def, mul_one, map_one] using h.symm
    · intro i
      change aeval r (MvPolynomial.map (iterateFrobenius K p s) (X i)) = θ (aeval r (X i))
      rw [MvPolynomial.map_X, aeval_X, hfixed]
  exact DFunLike.congr_fun h F

include hθ hfixed in
/-- Frobenius stability follows from the actual fixed sections, rather than
being supplied for their ideal of relations. -/
theorem fixedSectionRelationIdeal_stable (F : MvPolynomial σ K)
    (hF : F ∈ fixedSectionRelationIdeal r) :
    coefficientFrobenius p s F ∈ fixedSectionRelationIdeal r := by
  change aeval r (coefficientFrobenius p s F) = 0
  rw [fixedSection_aeval_coefficientFrobenius r p s θ hθ hfixed]
  exact (congrArg θ hF).trans θ.map_zero

variable [IsAlgClosed K] [Finite σ]
include hθ hfixed in
/-- The actual homogeneous coordinate relation ideal descends exactly to the
finite Frobenius-fixed coefficient field. -/
theorem fixedSectionRelationIdeal_descends (hs : s ≠ 0) :
    Ideal.map (MvPolynomial.map (fixedField K p s).subtype)
      (Ideal.comap (MvPolynomial.map (fixedField K p s).subtype)
        (fixedSectionRelationIdeal r)) = fixedSectionRelationIdeal r :=
  ideal_map_comap_eq p s hs (fixedSectionRelationIdeal r)
    (fixedSectionRelationIdeal_stable r p s θ hθ hfixed)

end SupersingularCurves.Geometry.FrobeniusDescent
