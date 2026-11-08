/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusFixedScalarExtension
import SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentSectionAction
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree

/-!
# Actual scalar extension of fixed homogeneous components

A Frobenius-semilinear ring action is linear over its actual finite fixed
field. Its fixed homogeneous components recover the original components
by scalar extension, with the comparison given by the actual inclusion.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FrobeniusDescent
open scoped TensorProduct

variable {K : Type u} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)
variable {R : Type u} [CommRing R] [Algebra K R]
variable (θ : R →+* R) (hθ : ∀ (c : K) (x : R), θ (c • x) = c ^ (p ^ s) • θ x)

/-- The genuine ring action, linear over the actual Frobenius-fixed field. -/
def fixedCoefficientAction : R →ₐ[fixedField K p s] R where
  toRingHom := θ
  commutes' a := by
    rw [IsScalarTower.algebraMap_apply (fixedField K p s) K R a]
    change θ (algebraMap K R (a : K)) = algebraMap K R (a : K)
    have ha : (a : K) ^ (p ^ s) = a := a.property
    have h := hθ (a : K) 1
    simpa only [ha, Algebra.smul_def, mul_one, map_one, Subfield.algebraMap_ofSubfield] using h

/-- The actual subalgebra of fixed elements. -/
abbrev fixedAlgebra : Subalgebra (fixedField K p s) R :=
  (fixedCoefficientAction p s θ hθ).equalizer (AlgHom.id _ _)

variable (𝓡 : ℕ → Submodule K R)
variable (hdeg : ∀ n, ∀ x ∈ 𝓡 n, θ x ∈ 𝓡 n)

/-- Restriction of the action to the actual homogeneous component. -/
def homogeneousAction (n : ℕ) : 𝓡 n →+ 𝓡 n where
  toFun x := ⟨θ x, hdeg n x x.property⟩
  map_zero' := Subtype.ext θ.map_zero
  map_add' x y := Subtype.ext (θ.map_add x y)

omit [Fact p.Prime] [CharP K p] in
include hθ in
theorem homogeneousAction_semilinear (n : ℕ) (c : K) (x : 𝓡 n) :
    homogeneousAction θ 𝓡 hdeg n (c • x) =
      c ^ (p ^ s) • homogeneousAction θ 𝓡 hdeg n x :=
  Subtype.ext (hθ c x)

include hdeg in
theorem homogeneousAction_injective (hinj : Function.Injective θ) (n : ℕ) :
    Function.Injective (homogeneousAction θ 𝓡 hdeg n) := by
  intro x y h
  exact Subtype.ext (hinj (congrArg Subtype.val h))

/-- The degree-n component inside the genuine fixed subalgebra. -/
def fixedComponent (n : ℕ) : Submodule (fixedField K p s) (fixedAlgebra p s θ hθ) :=
  ((𝓡 n).restrictScalars (fixedField K p s)).comap (fixedAlgebra p s θ hθ).val.toLinearMap

/-- The two descriptions of fixed homogeneous elements differ only by the
order in which the fixed and homogeneous conditions are recorded. -/
def fixedComponentEquiv (n : ℕ) :
    fixedComponent p s θ hθ 𝓡 n ≃ₗ[fixedField K p s]
      fixedSubmodule p s (homogeneousAction θ 𝓡 hdeg n)
        (homogeneousAction_semilinear p s θ hθ 𝓡 hdeg n) where
  toFun x := ⟨⟨x.1.1, x.2⟩, Subtype.ext x.1.2⟩
  invFun x := ⟨⟨x.1.1, congrArg Subtype.val x.2⟩, x.1.2⟩
  left_inv _x := rfl
  right_inv _x := rfl
  map_add' _x _y := rfl
  map_smul' _c _x := rfl

/-- The actual inclusion of one fixed homogeneous component. -/
def fixedComponentMap (n : ℕ) :
    fixedComponent p s θ hθ 𝓡 n →ₗ[fixedField K p s] (𝓡 n).restrictScalars (fixedField K p s) where
  toFun x := ⟨x.1.1, x.2⟩
  map_add' _x _y := rfl
  map_smul' _c _x := rfl

include hdeg in
/-- Scalar extension recovers each finite-dimensional homogeneous component
by the actual inclusion, with no fixed basis supplied by the caller. -/
theorem fixedComponent_isBaseChange [IsAlgClosed K] (hs : s ≠ 0)
    (hinj : Function.Injective θ) (n : ℕ) [FiniteDimensional K (𝓡 n)] :
    IsBaseChange K (fixedComponentMap p s θ hθ 𝓡 n) := by
  obtain ⟨e, he⟩ := exists_fixedScalarExtension p s
    (homogeneousAction θ 𝓡 hdeg n)
    (homogeneousAction_semilinear p s θ hθ 𝓡 hdeg n) hs
    (homogeneousAction_injective θ 𝓡 hdeg hinj n)
  let d := fixedComponentEquiv p s θ hθ 𝓡 hdeg n
  apply IsBaseChange.of_equiv ((d.baseChange (fixedField K p s) K).trans e)
  intro x
  change e ((d.baseChange (fixedField K p s) K) (1 ⊗ₜ[fixedField K p s] x)) = _
  rw [LinearEquiv.baseChange_tmul, he, one_smul]
  rfl

end SupersingularCurves.Geometry.FrobeniusDescent
