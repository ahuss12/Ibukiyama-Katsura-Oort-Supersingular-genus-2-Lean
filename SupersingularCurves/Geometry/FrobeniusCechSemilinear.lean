/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusCechPullback
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange
import SupersingularCurves.Geometry.FrobeniusDifferentialTwist

/-!
# Absolute Frobenius and the actual Frobenius twist on Čech cohomology

The absolute Frobenius map is induced by the actual structure-sheaf pullback.
It is Frobenius-semilinear and sends an overlap representative to its p-th
power. No Cartier or Jacobian map enters its definition.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.SchemeFrobenius
open CategoryTheory AlgebraicGeometry Opposite InfinitesimalPicard
open Scheme.TwoAffineOpenCover

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

variable (p : ℕ) [Fact p.Prime] {K : Type u} [Field K] [CharP K p]
variable {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
variable (𝒱 : C.TwoAffineOpenCover)

/-- The actual absolute Frobenius, as a morphism of the covered scheme over
the Frobenius of the base field. -/
def absoluteCoverHom : HomOver (frobenius K p) 𝒱 c 𝒱 c where
  hom := absolute p c
  comm := absolute_over p c
  U0_le := le_rfl
  U1_le := le_rfl

/-- Absolute Frobenius on actual Čech H1, with its scalar semilinearity. -/
def absoluteCech : CechH1 c 𝒱 →ₛₗ[frobenius K p] CechH1 c 𝒱 :=
  (absoluteCoverHom p c 𝒱).H1map

/-- The actual overlap-section formula for absolute Frobenius. -/
theorem absoluteCoverHom_map01 (a : (𝒱.structureSheafSections c).M01) :
    (absoluteCoverHom p c 𝒱).map01 a = a ^ p := by
  rw [HomOver.map01_apply]
  change ((absolute p c).appLE (𝒱.U0 ⊓ 𝒱.U1)
    ((absolute p c) ⁻¹ᵁ (𝒱.U0 ⊓ 𝒱.U1)) le_rfl).hom a = a ^ p
  rw [Scheme.Hom.appLE_eq_app]
  change a ^ p ^ 1 = a ^ p
  rw [pow_one]

/-- Absolute Frobenius sends every actual overlap representative to its
p-th power; the quotient is the existing structure-sheaf Čech quotient. -/
theorem absoluteCech_mk (a : (𝒱.structureSheafSections c).M01) :
    absoluteCech p c 𝒱 (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (a ^ p : (𝒱.structureSheafSections c).M01) := by
  exact congrArg Submodule.Quotient.mk (absoluteCoverHom_map01 p c 𝒱 a)

/-- The absolute map raises the coefficient to the p-th power. -/
theorem absoluteCech_smul (b : K) (q : CechH1 c 𝒱) :
    absoluteCech p c 𝒱 (b • q) = b ^ p • absoluteCech p c 𝒱 q :=
  (absoluteCech p c 𝒱).map_smul' b q

/-- The relative Frobenius as a morphism of covers over the identity field
homomorphism. The source cover remains the actual Frobenius twist. -/
def relativeCoverHom : HomOver (RingHom.id K)
    (twistedCover p c 𝒱) (toBase p c) 𝒱 c where
  hom := relative p c
  comm := by
    change relative p c ≫ toBase p c = c ≫ Spec.map (𝟙 _)
    rw [Spec.map_id, Category.comp_id, relative_toBase]
  U0_le := (relative_preimage_U0 p c 𝒱).ge
  U1_le := (relative_preimage_U1 p c 𝒱).ge

/-- The general covered-scheme pullback agrees with the previously constructed
relative Frobenius map on Čech cohomology. -/
theorem relativeCoverHom_H1map (q : CechH1 (toBase p c) (twistedCover p c 𝒱)) :
    (relativeCoverHom p c 𝒱).H1map q = cechPullback p c 𝒱 q := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rfl

/-- Pullback along the actual projection to the original curve. Its scalar
map is Frobenius, whereas relative Frobenius is K-linear. -/
def projectionCech : CechH1 c 𝒱 →ₛₗ[frobenius K p]
    CechH1 (toBase p c) (twistedCover p c 𝒱) :=
  (projectionCoverHom p c 𝒱).H1map

/-- Projection pullback is specified by its action on actual overlap sections. -/
theorem projectionCech_mk (a : (𝒱.structureSheafSections c).M01) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (toBase p c)
      (projection p c ⁻¹ᵁ (𝒱.U0 ⊓ 𝒱.U1))
    projectionCech p c 𝒱 (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk
        ((((projection p c).app (𝒱.U0 ⊓ 𝒱.U1)).hom a) :
          ((twistedCover p c 𝒱).structureSheafSections (toBase p c)).M01) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (toBase p c)
    (projection p c ⁻¹ᵁ (𝒱.U0 ⊓ 𝒱.U1))
  change Submodule.Quotient.mk
    ((((projection p c).appLE _ ((projection p c) ⁻¹ᵁ _) le_rfl).hom a) :
      ((twistedCover p c 𝒱).structureSheafSections (toBase p c)).M01) = _
  rw [Scheme.Hom.appLE_eq_app]

/-- The actual factorization of absolute Frobenius descends to Čech H1. -/
theorem cechPullback_projectionCech (q : CechH1 c 𝒱) :
    cechPullback p c 𝒱 (projectionCech p c 𝒱 q) = absoluteCech p c 𝒱 q := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [projectionCech_mk, cechPullback_projection_mk, absoluteCech_mk]

variable [PerfectField K]

/-- The genuine inverse projection gives an inverse on Čech cohomology. -/
theorem inverse_projectionCoverHom_H1 (q : CechH1 c 𝒱) :
    (inverseProjectionCoverHom p c 𝒱).H1map (projectionCech p c 𝒱 q) = q := by
  change (inverseProjectionCoverHom p c 𝒱).H1map
    ((projectionCoverHom p c 𝒱).H1map q) = q
  rw [← HomOver.comp_H1map]
  exact (HomOver.H1map_congr
    (f := (inverseProjectionCoverHom p c 𝒱).comp (projectionCoverHom p c 𝒱))
    (g := HomOver.id 𝒱 c) (IsIso.inv_hom_id (projection p c)) q).trans
      (HomOver.id_H1map q)

/-- The other composition is also the identity on actual Čech classes. -/
theorem projection_inverseCoverHom_H1
    (q : CechH1 (toBase p c) (twistedCover p c 𝒱)) :
    projectionCech p c 𝒱 ((inverseProjectionCoverHom p c 𝒱).H1map q) = q := by
  change (projectionCoverHom p c 𝒱).H1map
    ((inverseProjectionCoverHom p c 𝒱).H1map q) = q
  rw [← HomOver.comp_H1map]
  exact (HomOver.H1map_congr
    (f := (projectionCoverHom p c 𝒱).comp (inverseProjectionCoverHom p c 𝒱))
    (g := HomOver.id (twistedCover p c 𝒱) (toBase p c))
    (IsIso.hom_inv_id (projection p c)) q).trans (HomOver.id_H1map q)

/-- The genuine projection is a Frobenius-semilinear equivalence on Čech H1.
Both directions come from actual scheme maps, independently of Cartier and V. -/
def projectionCechEquiv :
    LinearEquiv (frobeniusEquiv K p).toRingHom
      (σ' := (frobeniusEquiv K p).symm.toRingHom)
      (CechH1 c 𝒱) (CechH1 (toBase p c) (twistedCover p c 𝒱)) where
  toFun := projectionCech p c 𝒱
  invFun := (inverseProjectionCoverHom p c 𝒱).H1map
  left_inv := inverse_projectionCoverHom_H1 p c 𝒱
  right_inv := projection_inverseCoverHom_H1 p c 𝒱
  map_add' := (projectionCech p c 𝒱).map_add
  map_smul' := (projectionCech p c 𝒱).map_smulₛₗ

theorem projectionCechEquiv_mk (a : (𝒱.structureSheafSections c).M01) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (toBase p c)
      (projection p c ⁻¹ᵁ (𝒱.U0 ⊓ 𝒱.U1))
    projectionCechEquiv p c 𝒱 (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk
        ((((projection p c).app (𝒱.U0 ⊓ 𝒱.U1)).hom a) :
          ((twistedCover p c 𝒱).structureSheafSections (toBase p c)).M01) :=
  projectionCech_mk p c 𝒱 a

theorem projectionCechEquiv_smul (b : K) (q : CechH1 c 𝒱) :
    projectionCechEquiv p c 𝒱 (b • q) = b ^ p • projectionCechEquiv p c 𝒱 q :=
  (projectionCechEquiv p c 𝒱).map_smulₛₗ b q

/-- Absolute and relative Frobenius are related by the independently
constructed, genuinely semilinear projection equivalence. -/
theorem cechPullback_projectionCechEquiv (q : CechH1 c 𝒱) :
    cechPullback p c 𝒱 (projectionCechEquiv p c 𝒱 q) = absoluteCech p c 𝒱 q :=
  cechPullback_projectionCech p c 𝒱 q

/-- The relative map can be recovered on every twisted cohomology class. -/
theorem cechPullback_eq_absoluteCech_inverse
    (q : CechH1 (toBase p c) (twistedCover p c 𝒱)) :
    cechPullback p c 𝒱 q =
      absoluteCech p c 𝒱 ((projectionCechEquiv p c 𝒱).symm q) := by
  rw [← cechPullback_projectionCechEquiv, LinearEquiv.apply_symm_apply]

end SupersingularCurves.Geometry.SchemeFrobenius
