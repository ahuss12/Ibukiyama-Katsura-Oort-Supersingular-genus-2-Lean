/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.JacobianInfinitesimal

/-!
# The cocycle comparison for actual infinitesimal Picard classes

The comparison sends an actual first-order line bundle to the linear part of
its normalized transition unit, modulo Cech coboundaries. Its construction
reuses the pinned upstream `P2mTJ2.βfun`, including the proofs of independence
of local frames, classification, surjectivity, and coefficient naturality.

We descend that particular cocycle construction to deformation classes and
record its value on every normalized transition unit. No vector-space
dimension argument or arbitrary choice of a linear isomorphism is used.
Curve-morphism naturality is a separate compatibility theorem, not assumed here.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.InfinitesimalPicard
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.RelPicard NeronModelInfra
open scoped TensorProduct
open P2MW.S_AlgebraicGeometry_RelPicard_exists_trivialModDeformations_map_H1_tensor_natural

variable {K : Type u} [Field K] {C : Scheme.{u}}
variable (c : C ⟶ Spec (CommRingCat.of K))
variable (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
variable (𝒱 : C.TwoAffineOpenCover)

/-- Cech H1 of the structure sheaf on the given actual two-affine cover. -/
abbrev CechH1 := (𝒱.structureSheafSections c).H1

variable (V : Type u) [AddCommGroup V] [Module K V]
  [Module Kᵐᵒᵖ V] [IsCentralScalar K V]

/-- The Cech class of the normalized transition function of a deformation. -/
def classToCech : DeformationClasses c s V → CechH1 c 𝒱 ⊗[K] V :=
  Quotient.lift (P2mTJ2.βfun 𝒱 c s V)
    (fun L L' h => (P2mTJ2.βfun_eq_iff 𝒱 c s V L L').mpr h)

theorem classToCech_bijective : Function.Bijective (classToCech c s 𝒱 V) := by
  constructor
  · intro q q'
    induction q using Quotient.inductionOn with
    | h L =>
      induction q' using Quotient.inductionOn with
      | h L' =>
        intro h
        exact Quotient.sound ((P2mTJ2.βfun_eq_iff 𝒱 c s V L L').mp h)
  · intro z
    obtain ⟨L, hL⟩ := P2mTJ2.βfun_surjective 𝒱 c s V z
    exact ⟨deformationClass c s V L, hL⟩

/-- The actual cocycle classification of first-order line-bundle classes. -/
def deformationCechEquiv : DeformationClasses c s V ≃ CechH1 c 𝒱 ⊗[K] V :=
  Equiv.ofBijective (classToCech c s 𝒱 V) (classToCech_bijective c s 𝒱 V)

theorem deformationCechEquiv_class (L : TrivialModDeformations c s V) :
    deformationCechEquiv c s 𝒱 V (deformationClass c s V L) =
      P2mTJ2.βfun 𝒱 c s V L := rfl

variable {V}
variable {W : Type u} [AddCommGroup W] [Module K W]
  [Module Kᵐᵒᵖ W] [IsCentralScalar K W]

/-- Changing the square-zero coefficient module applies the same change to
the linear part of the transition function. -/
theorem deformationCechEquiv_map (φ : V →ₗ[K] W) (q : DeformationClasses c s V) :
    deformationCechEquiv c s 𝒱 W (mapCoefficients φ q) =
      LinearMap.lTensor (CechH1 c 𝒱) φ (deformationCechEquiv c s 𝒱 V q) := by
  induction q using Quotient.inductionOn with
  | h L => exact P2mTJ2.βfun_map 𝒱 c s φ L

variable (V)

/-- The cohomology class of the first-order coefficient of a transition unit. -/
def cocycleClass (τ : (TrivSqZeroExt K V ⊗[K] (𝒱.cover c).A01)ˣ) :
    CechH1 c 𝒱 ⊗[K] V :=
  (LinearMap.range (𝒱.cover c).structureSheaf.cechDiff).mkQ.rTensor V
    ((TensorProduct.comm K V (𝒱.cover c).A01)
      (TensorProduct.map (TrivSqZeroExt.sndHom K V) LinearMap.id
        (τ : TrivSqZeroExt K V ⊗[K] (𝒱.cover c).A01)))

/-- A representative formula for the comparison, valid for every normalized
transition unit gluing the given actual line bundle. -/
theorem deformationCechEquiv_of_cocycle (L : TrivialModDeformations c s V)
    (τ : (TrivSqZeroExt K V ⊗[K] (𝒱.cover c).A01)ˣ)
    (hτ : τ ∈ P2mTJ2.Nset 𝒱 c V L.1.L) :
    deformationCechEquiv c s 𝒱 V (deformationClass c s V L) =
      cocycleClass c 𝒱 V τ :=
  P2mTJ2.βmod_eq_of_mem 𝒱 c V L.1.isInvertible hτ

end SupersingularCurves.Geometry.InfinitesimalPicard
