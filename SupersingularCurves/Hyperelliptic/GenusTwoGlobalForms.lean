/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Hyperelliptic.GenusTwoCartier
import SupersingularCurves.Geometry.GlobalDifferentials

/-!
# General genus-two matrices on scheme-global forms

The forms are actual compatible Kaehler sections on an affine cover of the
constructed smooth proper curve. The operator is transported by the proved
canonical generic-restriction equivalence, as in the earlier two-family API.
-/
set_option autoImplicit false
noncomputable section
namespace SupersingularCurves.Hyperelliptic.SimpleRootModel
open AlgebraicCurve KaehlerDifferential
open SupersingularCurves.Geometry SupersingularCurves.Differentials SupersingularCurves.IKO
variable {K : Type*} [Field K] [IsAlgClosed K] [NeZero (2 : K)]
  (a : SimpleRootModel K)

abbrev GlobalForms := (differentialChart a.curveModel).GlobalForms

def globalRegularEquiv : a.GlobalForms ≃ₗ[K] regularDifferentials K a.FunctionField :=
  (differentialChart a.curveModel).regularEquiv

variable (hf : a.f.Separable) (hd : a.f.natDegree = 5 ∨ a.f.natDegree = 6)

def globalEquiv : (Fin 2 → K) ≃ₗ[K] a.GlobalForms :=
  (a.regularEquiv hf hd).trans a.globalRegularEquiv.symm

def globalBasis : Module.Basis (Fin 2) K a.GlobalForms :=
  (a.regularBasis hf hd).map a.globalRegularEquiv.symm

theorem globalBasis_restrict (i : Fin 2) :
    a.globalRegularEquiv (a.globalBasis hf hd i) = a.regularBasis hf hd i := by
  simp [globalBasis]

include hf hd in
theorem globalForms_finrank : Module.finrank K a.GlobalForms = 2 := by
  rw [← (a.globalEquiv hf hd).finrank_eq]
  simp

variable (p : ℕ) [Fact p.Prime] [CharP K p]

/-- Cartier on global forms through the proved generic restriction. -/
def globalCartier (ω : a.GlobalForms) : a.GlobalForms :=
  a.globalRegularEquiv.symm (regularCartier p a.x (a.globalRegularEquiv ω))

variable (hp : p % 2 = 1)
include hf hd hp

theorem globalCartier_coordinates (ω : a.GlobalForms) :
    (a.globalEquiv hf hd).symm (a.globalCartier p ω) =
      semilinearAction (frobeniusEquiv K p) (coefficientMatrix p a.f)
        ((a.globalEquiv hf hd).symm ω) := by
  simpa [globalEquiv, globalCartier] using
    a.regularCartier_coordinates hf hd p hp (a.globalRegularEquiv ω)

theorem all_globalCartier_zero_iff :
    (∀ ω, a.globalCartier p ω = 0) ↔ coefficientMatrix p a.f = 0 := by
  rw [← a.all_regularCartier_zero_iff hf hd p hp]
  constructor
  · intro h ω
    have hh := congrArg a.globalRegularEquiv (h (a.globalRegularEquiv.symm ω))
    simpa [globalCartier] using hh
  · intro h ω
    simp [globalCartier, h]

theorem all_globalCartier_square_zero_iff :
    (∀ ω, a.globalCartier p (a.globalCartier p ω) = 0) ↔
      (coefficientMatrix p a.f).map (fun c => c^p) * coefficientMatrix p a.f = 0 := by
  rw [← a.all_regularCartier_square_zero_iff hf hd p hp]
  constructor
  · intro h ω
    have hh := congrArg a.globalRegularEquiv (h (a.globalRegularEquiv.symm ω))
    simpa [globalCartier] using hh
  · intro h ω
    simp [globalCartier, h]

end SupersingularCurves.Hyperelliptic.SimpleRootModel
