/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.IKO.Semilinear

/-!
# Invertibility of the correctly twisted Cartier coordinate action

Entrywise inverse scalar automorphism is a bijection. Thus injectivity,
surjectivity and bijectivity of the semilinear action are each equivalent
to nonvanishing of the determinant of its coefficient matrix.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.IKO
variable {K : Type*} [Field K]

theorem semilinearAction_injective_iff (σ : K ≃+* K)
    (M : Matrix (Fin 2) (Fin 2) K) :
    Function.Injective (semilinearAction σ M) ↔ M.det ≠ 0 := by
  have h : Function.Injective (semilinearAction σ M) ↔
      Function.Injective M.mulVec := by
    constructor
    · intro h v w hvw
      apply h
      exact congrArg (fun q : Fin 2 → K => fun i => σ.symm (q i)) hvw
    · intro h v w hvw
      apply h
      funext i
      apply σ.symm.injective
      exact congrFun hvw i
  rw [h, Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero]

theorem semilinearAction_surjective_iff (σ : K ≃+* K)
    (M : Matrix (Fin 2) (Fin 2) K) :
    Function.Surjective (semilinearAction σ M) ↔ M.det ≠ 0 := by
  have h : Function.Surjective (semilinearAction σ M) ↔
      Function.Surjective M.mulVec := by
    constructor
    · intro h w
      obtain ⟨v, hv⟩ := h (fun i => σ.symm (w i))
      refine ⟨v, ?_⟩
      funext i
      apply σ.symm.injective
      exact congrFun hv i
    · intro h w
      obtain ⟨v, hv⟩ := h (fun i => σ (w i))
      refine ⟨v, ?_⟩
      funext i
      simp only [semilinearAction, hv, RingEquiv.symm_apply_apply]
  rw [h, Matrix.mulVec_surjective_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero]

theorem semilinearAction_bijective_iff (σ : K ≃+* K)
    (M : Matrix (Fin 2) (Fin 2) K) :
    Function.Bijective (semilinearAction σ M) ↔ M.det ≠ 0 := by
  change (Function.Injective _ ∧ Function.Surjective _) ↔ _
  rw [semilinearAction_injective_iff, semilinearAction_surjective_iff, and_self]

end SupersingularCurves.IKO
