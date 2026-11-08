/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusInvariantIdeal
import SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentLinear

/-!
# Scalar extension from Frobenius-fixed vectors

The fixed vectors of an injective Frobenius-semilinear map form a vector space
over the actual finite fixed field. Extending its scalars recovers the original
vector space. The comparison sends a pure tensor to scalar multiplication;
it is not merely an abstract equality of dimensions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v w

namespace SupersingularCurves.Geometry.FrobeniusDescent

open scoped TensorProduct

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
variable (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)

variable (θ : V →+ V)
variable (hθ : ∀ (c : K) (v : V), θ (c • v) = c ^ p ^ s • θ v)

/-- Fixed vectors, with their scalar structure over the Frobenius-fixed field. -/
def fixedSubmodule : Submodule (fixedField K p s) V where
  carrier := {v | θ v = v}
  zero_mem' := map_zero θ
  add_mem' hx hy := by
    change θ (_ + _) = _ + _
    rw [map_add, hx, hy]
  smul_mem' c v hv := by
    change θ ((c : K) • v) = (c : K) • v
    have hc : (c : K) ^ p ^ s = c := c.property
    rw [hθ, hc, hv]

/-- The canonical scalar-product map from the actual scalar extension. -/
def fixedScalarMap :
    K ⊗[fixedField K p s] fixedSubmodule p s θ hθ →ₗ[K] V :=
  TensorProduct.AlgebraTensorModule.lift {
    toFun := fun c => c • (fixedSubmodule p s θ hθ).subtype
    map_add' := fun c d => add_smul c d _
    map_smul' := fun c d => mul_smul c d _ }

@[simp] theorem fixedScalarMap_tmul (c : K) (v : fixedSubmodule p s θ hθ) :
    fixedScalarMap p s θ hθ (c ⊗ₜ[fixedField K p s] v) = c • (v : V) := rfl

variable {ι : Type w}
variable (b : Module.Basis ι K V) (hb : ∀ i, θ (b i) = b i)

include hθ hb in
/-- Coordinatewise Frobenius in any fixed basis, without a finite index type. -/
theorem repr_apply_eq_pow_of_fixedBasis (v : V) (i : ι) :
    b.repr (θ v) i = (b.repr v i) ^ p ^ s := by
  let σ := iterateFrobenius K p s
  let t : V →ₛₗ[σ] V :=
    { toFun := θ
      map_add' := θ.map_add
      map_smul' := hθ }
  let q : (ι →₀ K) →ₛₗ[σ] (ι →₀ K) :=
    Finsupp.mapRange.linearMap σ.toSemilinearMap
  have heq : b.repr.toLinearMap.comp t = q.comp b.repr.toLinearMap := by
    apply b.ext
    intro j
    change b.repr (θ (b j)) = (b.repr (b j)).mapRange σ σ.map_zero
    simp [hb]
  exact congrArg (fun f => f v i) heq

include hθ hb in
theorem fixed_iff_coordinates_of_fixedBasis (v : V) :
    θ v = v ↔ ∀ i, (b.repr v i) ^ p ^ s = b.repr v i := by
  constructor
  · intro hv i
    rw [← repr_apply_eq_pow_of_fixedBasis p s θ hθ b hb, hv]
  · intro hv
    apply b.repr.injective
    ext i
    rw [repr_apply_eq_pow_of_fixedBasis p s θ hθ b hb, hv]

/-- A fixed basis identifies fixed vectors with finitely supported fixed-field coordinates. -/
def fixedCoordinates : fixedSubmodule p s θ hθ ≃ₗ[fixedField K p s]
    (ι →₀ fixedField K p s) where
  toFun v :=
    { support := (b.repr v).support
      toFun i := ⟨b.repr v i, ((fixed_iff_coordinates_of_fixedBasis
        p s θ hθ b hb v).mp v.property) i⟩
      mem_support_toFun i := by
        rw [Finsupp.mem_support_iff]
        constructor
        · intro h hz
          exact h (congrArg Subtype.val hz)
        · intro h hz
          exact h (Subtype.ext hz) }
  invFun a := ⟨b.repr.symm (a.mapRange (fun x : fixedField K p s => (x : K)) rfl), by
    apply (fixed_iff_coordinates_of_fixedBasis p s θ hθ b hb _).mpr
    intro i
    simp only [LinearEquiv.apply_symm_apply, Finsupp.mapRange_apply]
    exact (a i).property⟩
  left_inv v := by
    apply Subtype.ext
    apply b.repr.injective
    ext i
    simp only [LinearEquiv.apply_symm_apply, Finsupp.mapRange_apply]
    rfl
  right_inv a := by
    ext i
    simp only [LinearEquiv.apply_symm_apply, Finsupp.mapRange_apply]
    rfl
  map_add' x y := by
    ext i
    exact map_add (b.coord i) (x : V) (y : V)
  map_smul' c v := by
    ext i
    change b.repr ((c : K) • (v : V)) i = (c : K) * b.repr v i
    simp

/-- The fixed vectors have a basis over the fixed field with the same arbitrary indices. -/
def fixedVectorBasis : Module.Basis ι (fixedField K p s) (fixedSubmodule p s θ hθ) :=
  Finsupp.basisSingleOne.map (fixedCoordinates p s θ hθ b hb).symm

@[simp] theorem fixedVectorBasis_coe (i : ι) :
    (fixedVectorBasis p s θ hθ b hb i : V) = b i := by
  apply b.repr.injective
  change b.repr (b.repr.symm ((Finsupp.single i (1 : fixedField K p s)).mapRange
    (fun x : fixedField K p s => (x : K)) rfl)) = b.repr (b i)
  rw [LinearEquiv.apply_symm_apply, Module.Basis.repr_self, Finsupp.mapRange_single]
  rfl

/-- Scalar extension recovers the original space by its actual fixed vectors. -/
def fixedScalarExtension :
    K ⊗[fixedField K p s] fixedSubmodule p s θ hθ ≃ₗ[K] V :=
  ((fixedVectorBasis p s θ hθ b hb).baseChange K).equiv b (Equiv.refl ι)

@[simp] theorem fixedScalarExtension_one_tmul_basis (i : ι) :
    fixedScalarExtension p s θ hθ b hb
      (1 ⊗ₜ[fixedField K p s] fixedVectorBasis p s θ hθ b hb i) = b i := by
  simpa only [fixedScalarExtension, Module.Basis.baseChange_apply, Equiv.refl_apply] using
    (((fixedVectorBasis p s θ hθ b hb).baseChange K).equiv_apply i b (Equiv.refl ι))

theorem fixedScalarExtension_tmul (c : K) (v : fixedSubmodule p s θ hθ) :
    fixedScalarExtension p s θ hθ b hb (c ⊗ₜ[fixedField K p s] v) = c • (v : V) := by
  have heq : (fixedScalarExtension p s θ hθ b hb).toLinearMap =
      fixedScalarMap p s θ hθ := by
    apply ((fixedVectorBasis p s θ hθ b hb).baseChange K).ext
    intro i
    simp only [Module.Basis.baseChange_apply, LinearEquiv.coe_coe,
      fixedScalarExtension_one_tmul_basis, fixedScalarMap_tmul, one_smul,
      fixedVectorBasis_coe]
  exact congrArg (fun f => f (c ⊗ₜ[fixedField K p s] v)) heq

/-- No fixed basis needs to be supplied: injectivity constructs it by Lang's theorem. -/
theorem exists_fixedScalarExtension [IsAlgClosed K] [FiniteDimensional K V]
    (hs : s ≠ 0) (hinj : Function.Injective θ) :
    ∃ e : K ⊗[fixedField K p s] fixedSubmodule p s θ hθ ≃ₗ[K] V,
      ∀ (c : K) (v : fixedSubmodule p s θ hθ), e (c ⊗ₜ v) = c • (v : V) := by
  obtain ⟨b, hb⟩ := FrobeniusFiniteFieldDescentLinear.exists_fixedBasis p s hs θ hθ hinj
  exact ⟨fixedScalarExtension p s θ hθ b hb, fixedScalarExtension_tmul p s θ hθ b hb⟩

end SupersingularCurves.Geometry.FrobeniusDescent
