/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.JacobianVerschiebungSquare

/-!
# Vanishing is unchanged by the actual twist of Jacobian Verschiebung

Both actual cotangent maps are compared with the actual relative Frobenius
maps on Čech cohomology. Genuine projection equivalences and their
structure-sheaf naturality compare vanishing on the two curve twists.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

namespace SupersingularCurves.Geometry.PicardCohomology
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian InfinitesimalPicard SchemeFrobenius

variable (p : ℕ) [Fact p.Prime]
variable {K : Type u} [Field K] [CharP K p]
variable {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of K)}
variable {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c}
variable {D : RelativePic0Designation K c}
variable (h : RepresentsRelSubPic c s (algEquivZeroCut c s) D)
variable (𝒱 : C.TwoAffineOpenCover)

/-- The actual Picard pullback differential vanishes exactly when the actual
relative Frobenius pullback vanishes on Čech cohomology. -/
theorem frobeniusCotangent_eq_zero_iff_cechPullback_eq_zero :
    frobeniusCotangent p h = 0 ↔ cechPullback p c 𝒱 = 0 := by
  constructor
  · intro hd
    apply LinearMap.ext
    intro q
    obtain ⟨l, rfl⟩ :=
      (tangentCechEquiv (twistRepresents p h) (twistedCover p c 𝒱)).surjective q
    rw [← tangentCechEquiv_frobeniusCotangent, hd, LinearMap.comp_zero, map_zero]
    rfl
  · intro hF
    apply LinearMap.ext
    intro x
    apply (Module.forall_dual_apply_eq_zero_iff K _).mp
    intro l
    have hl : l ∘ₗ frobeniusCotangent p h = 0 := by
      apply (tangentCechEquiv h 𝒱).injective
      rw [tangentCechEquiv_frobeniusCotangent, hF, LinearMap.zero_apply, map_zero]
    exact LinearMap.congr_fun hl x

end SupersingularCurves.Geometry.PicardCohomology

namespace SupersingularCurves.Geometry.SchemeFrobenius
open CategoryTheory AlgebraicGeometry InfinitesimalPicard

variable (p : ℕ) [Fact p.Prime] {K : Type u} [Field K] [CharP K p] [PerfectField K]
variable {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
variable (𝒱 : C.TwoAffineOpenCover)

/-- The actual relative Frobenius cohomology map vanishes precisely when its
counterpart on the actual Frobenius twist does. -/
theorem cechPullback_twist_eq_zero_iff :
    cechPullback p (toBase p c) (twistedCover p c 𝒱) = 0 ↔
      cechPullback p c 𝒱 = 0 := by
  constructor
  · intro h
    apply LinearMap.ext
    intro q₁
    obtain ⟨q, rfl⟩ := (projectionCechEquiv p c 𝒱).surjective q₁
    rw [cechPullback_projectionCechEquiv, LinearMap.zero_apply]
    apply (projectionCechEquiv p c 𝒱).injective
    rw [map_zero, ← absoluteCech_projectionCechEquiv,
      ← cechPullback_projectionCechEquiv, h, LinearMap.zero_apply]
  · intro h
    apply LinearMap.ext
    intro q₂
    obtain ⟨q₁, rfl⟩ :=
      (projectionCechEquiv p (toBase p c) (twistedCover p c 𝒱)).surjective q₂
    obtain ⟨q, rfl⟩ := (projectionCechEquiv p c 𝒱).surjective q₁
    rw [cechPullback_projectionCechEquiv, absoluteCech_projectionCechEquiv,
      ← cechPullback_projectionCechEquiv, h, LinearMap.zero_apply, map_zero]
    rfl

end SupersingularCurves.Geometry.SchemeFrobenius

namespace SupersingularCurves.Geometry.Jacobian
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicCurve NeronModelInfra GoodReductionJacobian SchemeFrobenius

variable {K : Type u} [Field K]
variable {F : Type v} [Field F] [Algebra K F]
variable {M : CurveModel K F}
  {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase}
variable (J : Jacobian M s)
variable (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K]
variable (𝒱 : M.C.TwoAffineOpenCover)
include 𝒱

/-- The genuine cotangent differential of the actual scheme base change of
V vanishes if and only if the original genuine cotangent differential does. -/
theorem twistedVerschiebungCotangent_eq_zero_iff :
    J.twistedVerschiebungCotangent p = 0 ↔ J.verschiebungCotangent p = 0 := by
  rw [← J.frobeniusCotangent_twist_eq_twistedVerschiebungCotangent p,
    ← J.frobeniusCotangent_eq_verschiebungCotangent p,
    PicardCohomology.frobeniusCotangent_eq_zero_iff_cechPullback_eq_zero p
      (J.twistedPicardRepresentation p) (twistedCover p M.toBase 𝒱),
    PicardCohomology.frobeniusCotangent_eq_zero_iff_cechPullback_eq_zero p J.represents 𝒱]
  exact cechPullback_twist_eq_zero_iff p M.toBase 𝒱

/-- Nonvanishing transfers to the actual Frobenius base change of V. -/
theorem twistedVerschiebungCotangent_ne_zero
    (h : J.verschiebungCotangent p ≠ 0) : J.twistedVerschiebungCotangent p ≠ 0 :=
  fun htw => h ((J.twistedVerschiebungCotangent_eq_zero_iff p 𝒱).mp htw)

end SupersingularCurves.Geometry.Jacobian
