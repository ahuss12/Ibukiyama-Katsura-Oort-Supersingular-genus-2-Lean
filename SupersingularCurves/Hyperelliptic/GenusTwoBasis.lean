/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Hyperelliptic.Reciprocal
import SupersingularCurves.Hyperelliptic.Genus
import SupersingularCurves.IKO.RegularCoordinates

/-!
# IKO Section 1.1: a full basis for every separable quintic or sextic

Every input polynomial over an algebraically closed field supplies a simple
root, hence an actual quadratic function field. Regularity at all places,
linear independence, and the independently proved genus computation give the
full basis dx/y, x dx/y. No basis or genus assertion is an input assumption.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.Hyperelliptic
open Polynomial AlgebraicCurve KaehlerDifferential
open SupersingularCurves.IKO
variable {K : Type*} [Field K] [IsAlgClosed K]

/-- Every separable polynomial of degree five or six supplies the simple root
needed for the previously verified quadratic-field construction. -/
def modelOfSeparable (f : K[X]) (hf : f.Separable)
    (hd : f.natDegree = 5 ∨ f.natDegree = 6) : SimpleRootModel K :=
  let h := IsAlgClosed.exists_root f
    (ne_of_gt (natDegree_pos_iff_degree_pos.mp (by omega)))
  { f := f
    root := Classical.choose h
    root_zero := Classical.choose_spec h
    derivative_ne_zero := hf.eval₂_derivative_ne_zero (RingHom.id K)
      (Classical.choose_spec h) }

@[simp] theorem modelOfSeparable_f (f : K[X]) (hf : f.Separable)
    (hd : f.natDegree = 5 ∨ f.natDegree = 6) : (modelOfSeparable f hf hd).f = f := rfl

namespace SimpleRootModel
variable [NeZero (2 : K)] (a : SimpleRootModel K)
  (hf : a.f.Separable) (hd : a.f.natDegree = 5 ∨ a.f.natDegree = 6)

include hf hd

omit [NeZero (2 : K)] in
theorem pair_regular :
    a.y⁻¹ • D K a.FunctionField a.x ∈ regularDifferentials K a.FunctionField ∧
      a.x • (a.y⁻¹ • D K a.FunctionField a.x) ∈ regularDifferentials K a.FunctionField :=
  quintic_sextic_pair_regular a.x a.f hf hd a.y a.equation_in_functionField
    a.x_ne_zero a.y_ne_zero

def regularCoordinates : (Fin 2 → K) →ₗ[K] regularDifferentials K a.FunctionField :=
  regularDifferentialCombination a.x a.y (a.pair_regular hf hd).1 (a.pair_regular hf hd).2

theorem regularCoordinates_injective : Function.Injective (a.regularCoordinates hf hd) :=
  regularDifferentialCombination_injective _ _ _ _
    a.transcendental_x a.dx_ne_zero a.y_ne_zero

/-- Independence and the genus theorem prove spanning of the entire space. -/
theorem regularCoordinates_bijective : Function.Bijective (a.regularCoordinates hf hd) := by
  have hdim := a.finite_and_finrank_regularDifferentials hf hd
  let := hdim.1
  refine ⟨a.regularCoordinates_injective hf hd, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := a.regularCoordinates hf hd) (by simpa using hdim.2.symm)).mp
    (a.regularCoordinates_injective hf hd)

def regularEquiv : (Fin 2 → K) ≃ₗ[K] regularDifferentials K a.FunctionField :=
  LinearEquiv.ofBijective (a.regularCoordinates hf hd) (a.regularCoordinates_bijective hf hd)

def regularBasis : Module.Basis (Fin 2) K (regularDifferentials K a.FunctionField) :=
  (Pi.basisFun K (Fin 2)).map (a.regularEquiv hf hd)

theorem regularBasis_zero :
    (a.regularBasis hf hd 0 : Ω[a.FunctionField⁄K]) = a.y⁻¹ • D K _ a.x := by
  simp [regularBasis, regularEquiv, regularCoordinates,
    regularDifferentialCombination, differentialCombination, Pi.basisFun_apply]

theorem regularBasis_one :
    (a.regularBasis hf hd 1 : Ω[a.FunctionField⁄K]) =
      a.x • (a.y⁻¹ • D K _ a.x) := by
  simp [regularBasis, regularEquiv, regularCoordinates,
    regularDifferentialCombination, differentialCombination, Pi.basisFun_apply]

end SimpleRootModel
end SupersingularCurves.Hyperelliptic
