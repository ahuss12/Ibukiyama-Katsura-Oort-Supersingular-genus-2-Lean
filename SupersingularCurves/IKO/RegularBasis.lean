/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.IKO.RegularCoordinates
import SupersingularCurves.Hyperelliptic.Genus

/-!
# Full regular-differential bases for the two IKO families

Over an algebraically closed field of odd characteristic, the constructed
fields have genus two and their entire regular-differential spaces have
dimension two. Thus the previously constructed coordinate maps are bijective.
The final Cartier criteria quantify over every regular differential.
No Jacobian or supersingularity equivalence is assumed or asserted here.
-/
set_option autoImplicit false
noncomputable section
namespace SupersingularCurves.IKO
open AlgebraicCurve KaehlerDifferential Polynomial
open SupersingularCurves.Differentials SupersingularCurves.Hyperelliptic
variable {K : Type*} [Field K]

theorem natDegree_familyA (t : K) : (familyA t).natDegree = 6 := by
  unfold familyA
  compute_degree <;> norm_num

theorem natDegree_familyB (t : K) : (familyB t).natDegree = 5 := by
  unfold familyB
  compute_degree <;> norm_num

variable [IsAlgClosed K] [NeZero (2 : K)]

theorem familyA_genus (t : K) (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    genusFF K (familyAModel t h3 ht1).FunctionField = 2 :=
  (familyAModel t h3 ht1).genus_eq_two (familyA_separable t h3 ht0 ht1)
    (Or.inr (natDegree_familyA t))

theorem familyB_genus (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    genusFF K (familyBModel t ht0).FunctionField = 2 :=
  (familyBModel t ht0).genus_eq_two (familyB_separable t (NeZero.ne _) ht0 ht1)
    (Or.inl (natDegree_familyB t))

theorem familyA_regular_dimension (t : K) (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    Module.Finite K (regularDifferentials K (familyAModel t h3 ht1).FunctionField) ∧
      Module.finrank K (regularDifferentials K (familyAModel t h3 ht1).FunctionField) = 2 :=
  (familyAModel t h3 ht1).finite_and_finrank_regularDifferentials
    (familyA_separable t h3 ht0 ht1) (Or.inr (natDegree_familyA t))

theorem familyB_regular_dimension (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    Module.Finite K (regularDifferentials K (familyBModel t ht0).FunctionField) ∧
      Module.finrank K (regularDifferentials K (familyBModel t ht0).FunctionField) = 2 :=
  (familyBModel t ht0).finite_and_finrank_regularDifferentials
    (familyB_separable t (NeZero.ne _) ht0 ht1) (Or.inl (natDegree_familyB t))

/-- Every regular differential has the displayed two coordinates. -/
theorem familyARegularCoordinates_bijective
    (t : K) (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    Function.Bijective (familyARegularCoordinates t h3 ht0 ht1) := by
  have hd := familyA_regular_dimension t h3 ht0 ht1
  letI := hd.1
  refine ⟨familyARegularCoordinates_injective t h3 ht0 ht1, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := familyARegularCoordinates t h3 ht0 ht1) (by simpa using hd.2.symm)).mp
  exact familyARegularCoordinates_injective t h3 ht0 ht1

theorem familyBRegularCoordinates_bijective (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    Function.Bijective (familyBRegularCoordinates t (NeZero.ne _) ht0 ht1) := by
  have hd := familyB_regular_dimension t ht0 ht1
  letI := hd.1
  refine ⟨familyBRegularCoordinates_injective t ht0 ht1, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := familyBRegularCoordinates t (NeZero.ne _) ht0 ht1) (by simpa using hd.2.symm)).mp
  exact familyBRegularCoordinates_injective t ht0 ht1

def familyARegularEquiv (t : K) (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (Fin 2 → K) ≃ₗ[K] regularDifferentials K (familyAModel t h3 ht1).FunctionField :=
  LinearEquiv.ofBijective (familyARegularCoordinates t h3 ht0 ht1)
    (familyARegularCoordinates_bijective t h3 ht0 ht1)

def familyBRegularEquiv (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (Fin 2 → K) ≃ₗ[K] regularDifferentials K (familyBModel t ht0).FunctionField :=
  LinearEquiv.ofBijective (familyBRegularCoordinates t (NeZero.ne _) ht0 ht1)
    (familyBRegularCoordinates_bijective t ht0 ht1)

def familyARegularBasis (t : K) (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    Module.Basis (Fin 2) K (regularDifferentials K (familyAModel t h3 ht1).FunctionField) :=
  (Pi.basisFun K (Fin 2)).map (familyARegularEquiv t h3 ht0 ht1)

def familyBRegularBasis (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    Module.Basis (Fin 2) K (regularDifferentials K (familyBModel t ht0).FunctionField) :=
  (Pi.basisFun K (Fin 2)).map (familyBRegularEquiv t ht0 ht1)

theorem familyARegularBasis_zero (t : K) (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    ((familyARegularBasis t h3 ht0 ht1) 0 :
      Ω[(familyAModel t h3 ht1).FunctionField⁄K]) =
        (familyAModel t h3 ht1).y⁻¹ • D K _ (familyAModel t h3 ht1).x := by
  simp [familyARegularBasis, familyARegularEquiv, familyARegularCoordinates,
    regularDifferentialCombination, differentialCombination, Pi.basisFun_apply]

theorem familyARegularBasis_one (t : K) (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    ((familyARegularBasis t h3 ht0 ht1) 1 :
      Ω[(familyAModel t h3 ht1).FunctionField⁄K]) =
        (familyAModel t h3 ht1).x •
          ((familyAModel t h3 ht1).y⁻¹ • D K _ (familyAModel t h3 ht1).x) := by
  simp [familyARegularBasis, familyARegularEquiv, familyARegularCoordinates,
    regularDifferentialCombination, differentialCombination, Pi.basisFun_apply]

theorem familyBRegularBasis_zero (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    ((familyBRegularBasis t ht0 ht1) 0 : Ω[(familyBModel t ht0).FunctionField⁄K]) =
      (familyBModel t ht0).y⁻¹ • D K _ (familyBModel t ht0).x := by
  simp [familyBRegularBasis, familyBRegularEquiv, familyBRegularCoordinates,
    regularDifferentialCombination, differentialCombination, Pi.basisFun_apply]

theorem familyBRegularBasis_one (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    ((familyBRegularBasis t ht0 ht1) 1 : Ω[(familyBModel t ht0).FunctionField⁄K]) =
      (familyBModel t ht0).x • ((familyBModel t ht0).y⁻¹ • D K _ (familyBModel t ht0).x) := by
  simp [familyBRegularBasis, familyBRegularEquiv, familyBRegularCoordinates,
    regularDifferentialCombination, differentialCombination, Pi.basisFun_apply]

/-- Matrix coordinates of Cartier for an arbitrary regular differential. -/
theorem familyA_regularCartier_coordinates
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp5 : 5 ≤ p)
    (t : K) (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (ω : regularDifferentials K (familyAModel t h3 ht1).FunctionField) :
    (familyARegularEquiv t h3 ht0 ht1).symm
        (regularCartier p (familyAModel t h3 ht1).x ω) =
      semilinearAction (frobeniusEquiv K p) (coefficientMatrix p (familyA t))
        ((familyARegularEquiv t h3 ht0 ht1).symm ω) := by
  apply (familyARegularEquiv t h3 ht0 ht1).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (congrArg (regularCartier p (familyAModel t h3 ht1).x)
    ((familyARegularEquiv t h3 ht0 ht1).apply_symm_apply ω).symm).trans
      (familyA_regularCartier_action p hp5 t h3 ht0 ht1 _)

theorem familyB_regularCartier_coordinates
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp3 : 3 ≤ p)
    (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (ω : regularDifferentials K (familyBModel t ht0).FunctionField) :
    (familyBRegularEquiv t ht0 ht1).symm
        (regularCartier p (familyBModel t ht0).x ω) =
      semilinearAction (frobeniusEquiv K p) (coefficientMatrix p (familyB t))
        ((familyBRegularEquiv t ht0 ht1).symm ω) := by
  apply (familyBRegularEquiv t ht0 ht1).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (congrArg (regularCartier p (familyBModel t ht0).x)
    ((familyBRegularEquiv t ht0 ht1).apply_symm_apply ω).symm).trans
      (familyB_regularCartier_action p hp3 t (NeZero.ne _) ht0 ht1 _)

/-- The criterion now quantifies over the entire regular-differential space. -/
theorem familyA_all_regularCartier_zero_iff
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp5 : 5 ≤ p)
    (t : K) (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (∀ ω : regularDifferentials K (familyAModel t h3 ht1).FunctionField,
      regularCartier p (familyAModel t h3 ht1).x ω = 0) ↔ (gPolynomial p).eval t = 0 := by
  rw [← familyA_regularCartier_zero_iff p hp5 t h3 ht0 ht1]
  constructor
  · intro h v; exact h _
  · intro h ω
    obtain ⟨v, rfl⟩ := (familyARegularCoordinates_bijective t h3 ht0 ht1).2 ω
    exact h v

theorem familyB_all_regularCartier_zero_iff
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp3 : 3 ≤ p)
    (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (∀ ω : regularDifferentials K (familyBModel t ht0).FunctionField,
      regularCartier p (familyBModel t ht0).x ω = 0) ↔ (hPolynomial p).eval t = 0 := by
  rw [← familyB_regularCartier_zero_iff p hp3 t ht0 ht1]
  constructor
  · intro h v; exact h _
  · intro h ω
    obtain ⟨v, rfl⟩ := (familyBRegularCoordinates_bijective t ht0 ht1).2 ω
    exact h v

theorem familyA_all_regularCartier_square_zero_iff
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp5 : 5 ≤ p)
    (t : K) (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (∀ ω : regularDifferentials K (familyAModel t h3 ht1).FunctionField,
      regularCartier p (familyAModel t h3 ht1).x
        (regularCartier p (familyAModel t h3 ht1).x ω) = 0) ↔ (gPolynomial p).eval t = 0 := by
  rw [← familyA_regularCartier_square_zero_iff p hp5 t h3 ht0 ht1]
  constructor
  · intro h v; exact h _
  · intro h ω
    obtain ⟨v, rfl⟩ := (familyARegularCoordinates_bijective t h3 ht0 ht1).2 ω
    exact h v

theorem familyB_all_regularCartier_square_zero_iff
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp3 : 3 ≤ p)
    (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (∀ ω : regularDifferentials K (familyBModel t ht0).FunctionField,
      regularCartier p (familyBModel t ht0).x
        (regularCartier p (familyBModel t ht0).x ω) = 0) ↔ (hPolynomial p).eval t = 0 := by
  rw [← familyB_regularCartier_square_zero_iff p hp3 t ht0 ht1]
  constructor
  · intro h v; exact h _
  · intro h ω
    obtain ⟨v, rfl⟩ := (familyBRegularCoordinates_bijective t ht0 ht1).2 ω
    exact h v

end SupersingularCurves.IKO
