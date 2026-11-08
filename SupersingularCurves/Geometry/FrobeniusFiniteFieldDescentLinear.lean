/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import Theorems.Thm_Submodule_span_fixedPoints_eq_top_of_frobenius_semilinear_injective

/-!
# Fixed coordinates for Frobenius-semilinear maps

An injective Frobenius-semilinear endomorphism of a finite-dimensional vector
space over an algebraically closed field admits a basis of fixed vectors.
In these coordinates the endomorphism is precisely coordinatewise Frobenius.
These statements apply to the action on sections of a Frobenius-invariant
line bundle, without a finite-order assumption on that action.
-/

set_option autoImplicit false
noncomputable section
universe u v w

namespace SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentLinear

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

/-- Coordinates in any fixed basis transform by the same Frobenius power. -/
theorem repr_apply_eq_pow {ι : Type w} [Fintype ι]
    (p s : ℕ) (θ : V →+ V)
    (hθ : ∀ (c : K) (v : V), θ (c • v) = c ^ p ^ s • θ v)
    (b : Module.Basis ι K V) (hb : ∀ i, θ (b i) = b i) (v : V) (i : ι) :
    b.repr (θ v) i = (b.repr v i) ^ p ^ s := by
  have heq : θ v = ∑ j, ((b.repr v j) ^ p ^ s) • b j := by
    conv_lhs => rw [← b.sum_repr v]
    simp only [map_sum, hθ, hb]
  rw [heq]
  exact congrFun (b.repr_sum_self _) i

/-- A fixed basis conjugates the semilinear map to coordinatewise Frobenius. -/
theorem equivFun_apply_eq_pow {ι : Type w} [Fintype ι]
    (p s : ℕ) (θ : V →+ V)
    (hθ : ∀ (c : K) (v : V), θ (c • v) = c ^ p ^ s • θ v)
    (b : Module.Basis ι K V) (hb : ∀ i, θ (b i) = b i) (v : V) :
    b.equivFun (θ v) = fun i => (b.equivFun v i) ^ p ^ s := by
  funext i
  simpa only [Module.Basis.equivFun_apply] using
    repr_apply_eq_pow p s θ hθ b hb v i

/-- A vector is fixed exactly when every coordinate is fixed by Frobenius. -/
theorem fixed_iff_coordinates_fixed {ι : Type w} [Fintype ι]
    (p s : ℕ) (θ : V →+ V)
    (hθ : ∀ (c : K) (v : V), θ (c • v) = c ^ p ^ s • θ v)
    (b : Module.Basis ι K V) (hb : ∀ i, θ (b i) = b i) (v : V) :
    θ v = v ↔ ∀ i, (b.repr v i) ^ p ^ s = b.repr v i := by
  constructor
  · intro hv i
    rw [← repr_apply_eq_pow p s θ hθ b hb, hv]
  · intro hv
    apply b.repr.injective
    ext i
    rw [repr_apply_eq_pow p s θ hθ b hb, hv]

variable [IsAlgClosed K] [FiniteDimensional K V]
variable (p : ℕ) [Fact p.Prime] [CharP K p]
variable (s : ℕ) (hs : s ≠ 0) (θ : V →+ V)
variable (hθ : ∀ (c : K) (v : V), θ (c • v) = c ^ p ^ s • θ v)
variable (hinj : Function.Injective θ)

include hs hθ hinj

/-- The linear Lang theorem, with a basis indexed by the dimension of the space. -/
theorem exists_fixedBasis :
    ∃ b : Module.Basis (Fin (Module.finrank K V)) K V, ∀ i, θ (b i) = b i := by
  classical
  have hspan := Submodule.span_fixedPoints_eq_top_of_frobenius_semilinear_injective
    s hs θ hθ hinj
  let b := Module.Basis.ofSpan hspan.ge
  let := FiniteDimensional.fintypeBasisIndex b
  let e := Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm
  refine ⟨b.reindex e, ?_⟩
  intro i
  have hb : b (e.symm i) ∈ Function.fixedPoints θ :=
    Module.Basis.ofSpan_subset hspan.ge ⟨e.symm i, rfl⟩
  change θ (b (e.symm i)) = b (e.symm i) at hb
  simpa only [Module.Basis.reindex_apply] using hb

/-- A chosen fixed basis for the actual semilinear map. -/
def fixedBasis : Module.Basis (Fin (Module.finrank K V)) K V :=
  (exists_fixedBasis p s hs θ hθ hinj).choose

theorem fixedBasis_apply (i : Fin (Module.finrank K V)) :
    θ (fixedBasis p s hs θ hθ hinj i) = fixedBasis p s hs θ hθ hinj i :=
  (exists_fixedBasis p s hs θ hθ hinj).choose_spec i

/-- The chosen basis gives an actual linear change of coordinates conjugating
the semilinear map to coordinatewise Frobenius. -/
theorem exists_equivFun_apply_eq_pow :
    ∃ e : V ≃ₗ[K] (Fin (Module.finrank K V) → K),
      ∀ v, e (θ v) = fun i => (e v i) ^ p ^ s := by
  refine ⟨(fixedBasis p s hs θ hθ hinj).equivFun, ?_⟩
  exact equivFun_apply_eq_pow p s θ hθ _ (fixedBasis_apply p s hs θ hθ hinj)

end SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentLinear
