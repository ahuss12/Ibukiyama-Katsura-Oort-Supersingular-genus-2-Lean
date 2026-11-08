/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.CechRepartition
import SupersingularCurves.Geometry.FrobeniusPicardCohomology

/-!
# The actual Jacobian cotangent space and dual repartition cohomology

The comparison is the specified Poincare-cocycle map followed by generic
restriction and off-chart extension. Its representative formula and
evaluation normalization are proved. Verschiebung is still compared here
with actual Frobenius-pulled-back line-bundle deformations. Identification
with regular differentials and the residue/Cartier adjointness theorem are
separate, still necessary results.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

namespace SupersingularCurves.Geometry.Jacobian
open CategoryTheory AlgebraicGeometry AlgebraicCurve NeronModelInfra
open InfinitesimalPicard
open scoped TensorProduct

variable {K : Type u} [Field K] [IsAlgClosed K]
variable {F : Type v} [Field F] [Algebra K F] {M : CurveModel K F}
variable {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase}
variable (J : Jacobian M s) (𝒱 : M.C.TwoAffineOpenCover)

/-- Tangent vectors give the actual repartition class of their Poincare cocycle. -/
def tangentRepartitionEquiv :
    letI := M.functionFieldAlgebra
    Module.Dual K J.Cotangent ≃ₗ[K] SchemeCech.RepartitionH1 M.toBase :=
  letI := M.functionFieldAlgebra
  (J.tangentCechEquiv 𝒱).trans (SchemeCech.repartitionEquivOfAlgClosed M.toBase 𝒱)

/-- The cotangent/dual-repartition comparison retains the actual cocycle normalization. -/
def cotangentDualRepartitionEquiv :
    letI := M.functionFieldAlgebra
    J.Cotangent ≃ₗ[K] Module.Dual K (SchemeCech.RepartitionH1 M.toBase) :=
  letI := M.functionFieldAlgebra
  (J.cotangentDualCechEquiv 𝒱).trans
    (SchemeCech.repartitionEquivOfAlgClosed M.toBase 𝒱).symm.dualMap

/-- Explicit evaluation through the prescribed Cech/repartition map. -/
theorem cotangentDualRepartitionEquiv_cech (x : J.Cotangent) (q : CechH1 M.toBase 𝒱) :
    J.cotangentDualRepartitionEquiv 𝒱 x (SchemeCech.toRepartition M.toBase 𝒱 q) =
      J.cotangentDualCechEquiv 𝒱 x q := by
  letI := M.functionFieldAlgebra
  change J.cotangentDualCechEquiv 𝒱 x
    ((SchemeCech.repartitionEquivOfAlgClosed M.toBase 𝒱).symm
      (SchemeCech.repartitionEquivOfAlgClosed M.toBase 𝒱 q)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- Formula on actual overlap sections; the repartition is zero on the first
chart's places and equals the generic germ on the complement. -/
theorem cotangentDualRepartitionEquiv_mk (x : J.Cotangent)
    (f : (𝒱.structureSheafSections M.toBase).M01) :
    letI := M.functionFieldAlgebra
    letI := SchemeCech.properCover_overlap_nonempty M.toBase 𝒱
    J.cotangentDualRepartitionEquiv 𝒱 x
      (Submodule.Quotient.mk (extendOffChart K (placesOf M.toBase 𝒱.U0)
        ((M.C.germToFunctionField (𝒱.U0 ⊓ 𝒱.U1)).hom f))) =
      J.cotangentDualCechEquiv 𝒱 x (Submodule.Quotient.mk f) :=
  J.cotangentDualRepartitionEquiv_cech 𝒱 x (Submodule.Quotient.mk f)

/-- Poincare evaluation fixes the normalization of the dual comparison. -/
theorem cotangentDualRepartitionEquiv_tangent (x : J.Cotangent)
    (l : Module.Dual K J.Cotangent) :
    J.cotangentDualRepartitionEquiv 𝒱 x (J.tangentRepartitionEquiv 𝒱 l) = l x := by
  rw [show J.tangentRepartitionEquiv 𝒱 l =
    SchemeCech.toRepartition M.toBase 𝒱 (J.tangentCechEquiv 𝒱 l) from rfl]
  rw [J.cotangentDualRepartitionEquiv_cech, J.cotangentDualCechEquiv_tangent]

/-- The Poincare evaluation formula determines the actual comparison uniquely. -/
theorem cotangentDualRepartitionEquiv_unique :
    letI := M.functionFieldAlgebra
    ∀ e : J.Cotangent →ₗ[K] Module.Dual K (SchemeCech.RepartitionH1 M.toBase),
      (∀ x l, e x (J.tangentRepartitionEquiv 𝒱 l) = l x) →
      e = (J.cotangentDualRepartitionEquiv 𝒱).toLinearMap := by
  letI := M.functionFieldAlgebra
  intro e he
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro z
  obtain ⟨l, rfl⟩ := (J.tangentRepartitionEquiv 𝒱).surjective z
  exact (he x l).trans (J.cotangentDualRepartitionEquiv_tangent 𝒱 x l).symm

variable (p : ℕ) [Fact p.Prime] [CharP K p]

/-- The repartition class obtained from the actual Frobenius pullback of a
twisted Poincare deformation. This does not define a cochain Frobenius map. -/
def frobeniusRepartitionClass (l : Module.Dual K (J.TwistedCotangent p)) :
    SchemeCech.RepartitionH1 M.toBase :=
  SchemeCech.toRepartition M.toBase 𝒱
    (TensorProduct.rid K (CechH1 M.toBase 𝒱)
      (deformationCechEquiv M.toBase s 𝒱 K
        (deformationClass M.toBase s K (J.frobeniusPoincareDeformation p l))))

/-- The independent V differential agrees with the actual pulled-back
deformation class after the canonical repartition comparison. -/
theorem tangentRepartitionEquiv_verschiebung (l : Module.Dual K (J.TwistedCotangent p)) :
    J.tangentRepartitionEquiv 𝒱 (l ∘ₗ J.verschiebungCotangent p) =
      J.frobeniusRepartitionClass 𝒱 p l :=
  congrArg (SchemeCech.toRepartition M.toBase 𝒱)
    (J.tangentCechEquiv_verschiebung 𝒱 p l)

/-- Dual evaluation of the actual Frobenius-pulled-back deformation class. -/
theorem cotangentDualRepartitionEquiv_frobeniusDeformation
    (x : J.Cotangent) (l : Module.Dual K (J.TwistedCotangent p)) :
    J.cotangentDualRepartitionEquiv 𝒱 x (J.frobeniusRepartitionClass 𝒱 p l) =
      l (J.verschiebungCotangent p x) := by
  rw [← J.tangentRepartitionEquiv_verschiebung 𝒱 p l,
    J.cotangentDualRepartitionEquiv_tangent]
  rfl

end SupersingularCurves.Geometry.Jacobian
