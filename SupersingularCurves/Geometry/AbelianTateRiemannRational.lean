/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.LinearAlgebra.Dual.BaseChange
import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-! # Scalar extension of the actual integral Riemann pairing -/
set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.Geometry.AbelianTate
open Module LinearMap TensorProduct
open LinearMap (BilinForm)
open scoped TensorProduct

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

/-- Alternation is preserved by scalar extension of a bilinear form. -/
theorem pairing_baseChange_isAlt (e : BilinForm R M) (he : e.IsAlt) :
    (e.baseChange S).IsAlt := by
  have hskew : (e.baseChange S).flip = -(e.baseChange S) := by
    ext x y
    change (e.baseChange S) ((1 : S) ⊗ₜ[R] y) ((1 : S) ⊗ₜ[R] x) =
      -(e.baseChange S) ((1 : S) ⊗ₜ[R] x) ((1 : S) ⊗ₜ[R] y)
    simp only [LinearMap.flip_apply, LinearMap.neg_apply, BilinForm.baseChange_tmul]
    rw [← he.neg x y, neg_smul]
  have hcross (x y : S ⊗[R] M) : (e.baseChange S) y x = -(e.baseChange S) x y :=
    LinearMap.congr_fun₂ hskew x y
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp only [BilinForm.baseChange_tmul, he m, zero_smul]
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, hx, hy]
    rw [hcross x y]
    abel

variable [Module.Finite R M] [Module.Free R M]

/-- A perfect integral pairing extends to a genuine equivalence with the
dual after scalar extension. -/
def pairingBaseChangePerfectEquiv (e : BilinForm R M) [e.IsPerfPair] :
    S ⊗[R] M ≃ₗ[S] Module.Dual S (S ⊗[R] M) :=
  (e.toPerfPair.baseChange R S M (Module.Dual R M)).trans
    (TensorProduct.isBaseChange R M S).toDualBaseChange

/-- The equivalence constructed from perfectness is exactly the usual
base-changed bilinear form. -/
theorem pairingBaseChangePerfectEquiv_toLinearMap (e : BilinForm R M) [e.IsPerfPair] :
    (pairingBaseChangePerfectEquiv (S := S) e).toLinearMap = e.baseChange S := by
  ext x y
  change ((TensorProduct.isBaseChange R M S).toDualBaseChange
    ((1 : S) ⊗ₜ[R] e.toPerfPair x)) ((TensorProduct.mk R S M 1) y) =
      (e.baseChange S) ((1 : S) ⊗ₜ[R] x) ((1 : S) ⊗ₜ[R] y)
  rw [IsBaseChange.toDualBaseChange_tmul]
  simp only [LinearMap.toPerfPair_apply, BilinForm.baseChange_tmul,
    Algebra.smul_def, smul_eq_mul]
  ring

/-- In particular, the rational Tate pairing is nondegenerate whenever
the actual integral pairing is perfect and alternating. -/
theorem pairing_baseChange_nondegenerate (e : BilinForm R M) [e.IsPerfPair]
    (he : e.IsAlt) : (e.baseChange S).Nondegenerate := by
  have halt := pairing_baseChange_isAlt (S := S) e he
  rw [halt.isRefl.nondegenerate_iff_separatingLeft,
    LinearMap.separatingLeft_iff_ker_eq_bot, LinearMap.ker_eq_bot]
  rw [← pairingBaseChangePerfectEquiv_toLinearMap (S := S) e]
  exact (pairingBaseChangePerfectEquiv (S := S) e).injective

end SupersingularCurves.Geometry.AbelianTate
