/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import Theorems.Thm_AlgebraicCurve_pullbackAlong_mem_regularDifferentials_of_mem_of_algEquiv

/-! # Canonical transport of regular differentials across a function-field isomorphism -/
set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.Geometry
open AlgebraicCurve KaehlerDifferential
variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem pullbackAlong_symm_apply (e : F ≃ₐ[K] F') (ω : Ω[F⁄K]) :
    Differential.pullbackAlong e.symm.toAlgHom (Differential.pullbackAlong e.toAlgHom ω) = ω := by
  have hw : ω ∈ Submodule.span F (Set.range (D K F)) := by
    rw [span_range_derivation]
    trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨x, rfl⟩
    rw [Differential.pullbackAlong_D, Differential.pullbackAlong_D]
    simp
  · simp only [map_zero]
  · intro x y _ _ hx hy
    simp only [map_add, hx, hy]
  · intro a x _ hx
    rw [Differential.pullbackAlong_smul, Differential.pullbackAlong_smul]
    simpa only [AlgEquiv.coe_algHom, AlgEquiv.symm_apply_apply, hx]

variable [PerfectField K] [Algebra.EssFiniteType K F] [Algebra.EssFiniteType K F']
  [IsCurveOver K F] [IsCurveOver K F']
  [∀ v : Place K F, v.DCoordGenerates] [∀ v : Place K F', v.DCoordGenerates]

/-- The map is differential pullback, restricted to forms regular at every place. -/
def regularDifferentialCongr (e : F ≃ₐ[K] F') :
    regularDifferentials K F ≃ₗ[K] regularDifferentials K F' where
  toFun ω := ⟨Differential.pullbackAlong e.toAlgHom ω.val,
    pullbackAlong_mem_regularDifferentials_of_mem_of_algEquiv e ω.val ω.property⟩
  invFun ω := ⟨Differential.pullbackAlong e.symm.toAlgHom ω.val,
    pullbackAlong_mem_regularDifferentials_of_mem_of_algEquiv e.symm ω.val ω.property⟩
  left_inv ω := Subtype.ext (pullbackAlong_symm_apply e ω.val)
  right_inv ω := Subtype.ext (pullbackAlong_symm_apply e.symm ω.val)
  map_add' ω η := Subtype.ext ((Differential.pullbackAlong e.toAlgHom).map_add ω.val η.val)
  map_smul' a ω := Subtype.ext ((Differential.pullbackAlong e.toAlgHom).map_smul a ω.val)

@[simp] theorem regularDifferentialCongr_apply (e : F ≃ₐ[K] F')
    (ω : regularDifferentials K F) :
    (regularDifferentialCongr e ω : Ω[F'⁄K]) = Differential.pullbackAlong e.toAlgHom ω.val := rfl

end SupersingularCurves.Geometry
