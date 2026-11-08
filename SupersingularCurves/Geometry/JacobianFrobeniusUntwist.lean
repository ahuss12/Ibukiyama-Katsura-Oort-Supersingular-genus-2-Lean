/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusCechComparison
import SupersingularCurves.Geometry.FrobeniusCechSemilinear

/-!
# An independently specified cohomological scalar untwist

The dual of an actual semilinear cohomology equivalence is transported
through the Poincare cotangent comparison. This fixes scalar normalization
without using Cartier or Verschiebung in the construction. Identification
with cotangent pullback along the Jacobian scheme projection is a separate
naturality assertion and is not assumed here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

namespace SupersingularCurves.Geometry
open CategoryTheory AlgebraicGeometry AlgebraicCurve InfinitesimalPicard NeronModelInfra
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

section DualTransport
variable {K H H' : Type*} [Field K] [AddCommGroup H] [Module K H]
  [AddCommGroup H'] [Module K H']

local instance (σ : K ≃+* K) : RingHomInvPair σ.toRingHom σ.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv σ

local instance (σ : K ≃+* K) : RingHomInvPair σ.symm.toRingHom σ.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm σ

/-- The contravariant dual of a semilinear equivalence, with inverse scalar
action made explicit on both functionals and their evaluations. -/
def dualSemilinearEquiv (σ : K ≃+* K)
    (e : LinearEquiv σ.toRingHom (σ' := σ.symm.toRingHom) H H') :
    LinearEquiv σ.symm.toRingHom (σ' := σ.toRingHom)
      (Module.Dual K H') (Module.Dual K H) where
  toFun f :=
    { toFun := fun x => σ.symm (f (e x))
      map_add' := by intro x y; simp only [map_add]
      map_smul' := by
        intro a x
        simp only [LinearEquiv.map_smulₛₗ, map_smul, RingHom.id_apply,
          RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, smul_eq_mul,
          map_mul, RingEquiv.symm_apply_apply] }
  invFun g :=
    { toFun := fun y => σ (g (e.symm y))
      map_add' := by intro x y; simp only [map_add]
      map_smul' := by
        intro a y
        simp only [LinearEquiv.map_smulₛₗ, map_smul, RingHom.id_apply,
          RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, smul_eq_mul,
          map_mul, RingEquiv.apply_symm_apply] }
  left_inv f := by
    apply LinearMap.ext
    intro y
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply,
      RingEquiv.apply_symm_apply]
  right_inv g := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.symm_apply_apply,
      RingEquiv.symm_apply_apply]
  map_add' f g := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, map_add]
  map_smul' a f := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, smul_eq_mul, map_mul]

theorem dualSemilinearEquiv_apply (σ : K ≃+* K)
    (e : LinearEquiv σ.toRingHom (σ' := σ.symm.toRingHom) H H')
    (f : Module.Dual K H') (x : H) :
    dualSemilinearEquiv σ e f x = σ.symm (f (e x)) := rfl

end DualTransport

namespace Jacobian
variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
variable {M : CurveModel K F}
  {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase}
variable (J : Jacobian M s) (𝒱 : M.C.TwoAffineOpenCover)
variable (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K]

/-- The cohomological scalar untwist on actual Jacobian cotangent spaces.
It is fixed by actual projection pullback and the two Poincare comparisons,
independently of both Cartier and Verschiebung. -/
def cotangentCohomologicalUntwist :
    LinearEquiv (frobeniusEquiv K p).symm.toRingHom
      (σ' := (frobeniusEquiv K p).toRingHom)
      (J.TwistedCotangent p) J.Cotangent :=
  (J.twistedCotangentDualCechEquiv 𝒱 p).trans
    ((dualSemilinearEquiv (frobeniusEquiv K p)
      (SchemeFrobenius.projectionCechEquiv p M.toBase 𝒱)).trans
        (J.cotangentDualCechEquiv 𝒱).symm)

/-- The evaluation formula specifies every scalar and the actual projection
map used by the untwist. -/
theorem cotangentCohomologicalUntwist_eval (x : J.TwistedCotangent p)
    (q : CechH1 M.toBase 𝒱) :
    J.cotangentDualCechEquiv 𝒱 (J.cotangentCohomologicalUntwist 𝒱 p x) q =
      (frobeniusEquiv K p).symm
        (J.twistedCotangentDualCechEquiv 𝒱 p x
          (SchemeFrobenius.projectionCechEquiv p M.toBase 𝒱 q)) := by
  simp only [cotangentCohomologicalUntwist, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, dualSemilinearEquiv_apply]

/-- The equivalent p-th-power evaluation formula. -/
theorem cotangentCohomologicalUntwist_eval_pow (x : J.TwistedCotangent p)
    (q : CechH1 M.toBase 𝒱) :
    (J.cotangentDualCechEquiv 𝒱 (J.cotangentCohomologicalUntwist 𝒱 p x) q) ^ p =
      J.twistedCotangentDualCechEquiv 𝒱 p x
        (SchemeFrobenius.projectionCechEquiv p M.toBase 𝒱 q) := by
  rw [J.cotangentCohomologicalUntwist_eval, frobeniusEquiv_symm_pow_p]

/-- The prescribed evaluations determine the untwist uniquely. -/
theorem cotangentCohomologicalUntwist_unique
    (e : J.TwistedCotangent p →ₛₗ[(frobeniusEquiv K p).symm.toRingHom] J.Cotangent)
    (he : ∀ x q, J.cotangentDualCechEquiv 𝒱 (e x) q =
      (frobeniusEquiv K p).symm
        (J.twistedCotangentDualCechEquiv 𝒱 p x
          (SchemeFrobenius.projectionCechEquiv p M.toBase 𝒱 q))) :
    e = (J.cotangentCohomologicalUntwist 𝒱 p).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply (J.cotangentDualCechEquiv 𝒱).injective
  apply LinearMap.ext
  intro q
  exact (he x q).trans (J.cotangentCohomologicalUntwist_eval 𝒱 p x q).symm

/-- Evaluation of actual Verschiebung after this independently fixed scalar
untwist is adjoint to actual absolute Frobenius on Čech H1. -/
theorem cotangentCohomologicalUntwist_verschiebung_eval_pow (x : J.Cotangent)
    (q : CechH1 M.toBase 𝒱) :
    (J.cotangentDualCechEquiv 𝒱
      (J.cotangentCohomologicalUntwist 𝒱 p (J.verschiebungCotangent p x)) q) ^ p =
      J.cotangentDualCechEquiv 𝒱 x (SchemeFrobenius.absoluteCech p M.toBase 𝒱 q) := by
  rw [J.cotangentCohomologicalUntwist_eval_pow,
    ← J.cotangentDualCechEquiv_frobenius_cochain,
    SchemeFrobenius.cechPullback_projectionCechEquiv]

/-- The inverse-Frobenius version retains the complete scalar normalization. -/
theorem cotangentCohomologicalUntwist_verschiebung_eval (x : J.Cotangent)
    (q : CechH1 M.toBase 𝒱) :
    J.cotangentDualCechEquiv 𝒱
      (J.cotangentCohomologicalUntwist 𝒱 p (J.verschiebungCotangent p x)) q =
      (frobeniusEquiv K p).symm
        (J.cotangentDualCechEquiv 𝒱 x (SchemeFrobenius.absoluteCech p M.toBase 𝒱 q)) := by
  rw [J.cotangentCohomologicalUntwist_eval,
    ← J.cotangentDualCechEquiv_frobenius_cochain,
    SchemeFrobenius.cechPullback_projectionCechEquiv]

end Jacobian
end SupersingularCurves.Geometry
