/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.GlobalDifferentials

/-!
# The IKO matrices on global sections of the actual curves

The sections are compatible Kaehler forms on an affine cover of the constructed
smooth proper scheme. The Cartier operator is transported through the proved
canonical generic-restriction equivalence. No Jacobian classification is used.
-/
set_option autoImplicit false
noncomputable section
namespace SupersingularCurves.IKO
open AlgebraicCurve KaehlerDifferential
open SupersingularCurves.Geometry SupersingularCurves.Differentials
variable {K : Type*} [Field K] [IsAlgClosed K] [NeZero (2 : K)]

abbrev familyAGlobalForms (t : K) (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :=
  (differentialChart (familyACurve t h3 ht0 ht1)).GlobalForms
abbrev familyBGlobalForms (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :=
  (differentialChart (familyBCurve t ht0 ht1)).GlobalForms

def familyAGlobalRegularEquiv (t : K) (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    familyAGlobalForms t h3 ht0 ht1 ≃ₗ[K]
      regularDifferentials K (familyAModel t h3 ht1).FunctionField :=
  (differentialChart (familyACurve t h3 ht0 ht1)).regularEquiv

def familyBGlobalRegularEquiv (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    familyBGlobalForms t ht0 ht1 ≃ₗ[K]
      regularDifferentials K (familyBModel t ht0).FunctionField :=
  (differentialChart (familyBCurve t ht0 ht1)).regularEquiv

def familyAGlobalEquiv (t : K) (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (Fin 2 → K) ≃ₗ[K] familyAGlobalForms t h3 ht0 ht1 :=
  (familyARegularEquiv t h3 ht0 ht1).trans (familyAGlobalRegularEquiv t h3 ht0 ht1).symm

def familyBGlobalEquiv (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (Fin 2 → K) ≃ₗ[K] familyBGlobalForms t ht0 ht1 :=
  (familyBRegularEquiv t ht0 ht1).trans (familyBGlobalRegularEquiv t ht0 ht1).symm

def familyAGlobalBasis (t : K) (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    Module.Basis (Fin 2) K (familyAGlobalForms t h3 ht0 ht1) :=
  (familyARegularBasis t h3 ht0 ht1).map (familyAGlobalRegularEquiv t h3 ht0 ht1).symm

def familyBGlobalBasis (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    Module.Basis (Fin 2) K (familyBGlobalForms t ht0 ht1) :=
  (familyBRegularBasis t ht0 ht1).map (familyBGlobalRegularEquiv t ht0 ht1).symm

theorem familyAGlobalBasis_restrict (t : K) (h3 : (3 : K) ≠ 0)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (i : Fin 2) :
    familyAGlobalRegularEquiv t h3 ht0 ht1 (familyAGlobalBasis t h3 ht0 ht1 i) =
      familyARegularBasis t h3 ht0 ht1 i := by
  simp [familyAGlobalBasis]

theorem familyBGlobalBasis_restrict (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (i : Fin 2) :
    familyBGlobalRegularEquiv t ht0 ht1 (familyBGlobalBasis t ht0 ht1 i) =
      familyBRegularBasis t ht0 ht1 i := by
  simp [familyBGlobalBasis]

theorem familyAGlobalForms_finrank (t : K) (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    Module.finrank K (familyAGlobalForms t h3 ht0 ht1) = 2 := by
  rw [← (familyAGlobalEquiv t h3 ht0 ht1).finrank_eq]
  simp

theorem familyBGlobalForms_finrank (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    Module.finrank K (familyBGlobalForms t ht0 ht1) = 2 := by
  rw [← (familyBGlobalEquiv t ht0 ht1).finrank_eq]
  simp

variable (p : ℕ) [Fact p.Prime] [CharP K p]

/-- Cartier on the actual global sections, defined through canonical restriction. -/
def familyAGlobalCartier (t : K) (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (ω : familyAGlobalForms t h3 ht0 ht1) : familyAGlobalForms t h3 ht0 ht1 :=
  (familyAGlobalRegularEquiv t h3 ht0 ht1).symm
    (regularCartier p (familyAModel t h3 ht1).x (familyAGlobalRegularEquiv t h3 ht0 ht1 ω))

def familyBGlobalCartier (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (ω : familyBGlobalForms t ht0 ht1) : familyBGlobalForms t ht0 ht1 :=
  (familyBGlobalRegularEquiv t ht0 ht1).symm
    (regularCartier p (familyBModel t ht0).x (familyBGlobalRegularEquiv t ht0 ht1 ω))

theorem familyA_globalCartier_coordinates (hp5 : 5 ≤ p) (t : K)
    (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (ω : familyAGlobalForms t h3 ht0 ht1) :
    (familyAGlobalEquiv t h3 ht0 ht1).symm (familyAGlobalCartier p t h3 ht0 ht1 ω) =
      semilinearAction (frobeniusEquiv K p) (coefficientMatrix p (familyA t))
        ((familyAGlobalEquiv t h3 ht0 ht1).symm ω) := by
  simpa [familyAGlobalEquiv, familyAGlobalCartier] using
    familyA_regularCartier_coordinates p hp5 t h3 ht0 ht1
      (familyAGlobalRegularEquiv t h3 ht0 ht1 ω)

theorem familyB_globalCartier_coordinates (hp3 : 3 ≤ p) (t : K)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (ω : familyBGlobalForms t ht0 ht1) :
    (familyBGlobalEquiv t ht0 ht1).symm (familyBGlobalCartier p t ht0 ht1 ω) =
      semilinearAction (frobeniusEquiv K p) (coefficientMatrix p (familyB t))
        ((familyBGlobalEquiv t ht0 ht1).symm ω) := by
  simpa [familyBGlobalEquiv, familyBGlobalCartier] using
    familyB_regularCartier_coordinates p hp3 t ht0 ht1
      (familyBGlobalRegularEquiv t ht0 ht1 ω)

theorem familyA_all_globalCartier_zero_iff (hp5 : 5 ≤ p) (t : K)
    (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (∀ ω, familyAGlobalCartier p t h3 ht0 ht1 ω = 0) ↔ (gPolynomial p).eval t = 0 := by
  rw [← familyA_all_regularCartier_zero_iff p hp5 t h3 ht0 ht1]
  constructor
  · intro h ω
    have hh := congrArg (familyAGlobalRegularEquiv t h3 ht0 ht1)
      (h ((familyAGlobalRegularEquiv t h3 ht0 ht1).symm ω))
    simpa [familyAGlobalCartier] using hh
  · intro h ω
    simp [familyAGlobalCartier, h]

theorem familyB_all_globalCartier_zero_iff (hp3 : 3 ≤ p) (t : K)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (∀ ω, familyBGlobalCartier p t ht0 ht1 ω = 0) ↔ (hPolynomial p).eval t = 0 := by
  rw [← familyB_all_regularCartier_zero_iff p hp3 t ht0 ht1]
  constructor
  · intro h ω
    have hh := congrArg (familyBGlobalRegularEquiv t ht0 ht1)
      (h ((familyBGlobalRegularEquiv t ht0 ht1).symm ω))
    simpa [familyBGlobalCartier] using hh
  · intro h ω
    simp [familyBGlobalCartier, h]

theorem familyA_all_globalCartier_square_zero_iff (hp5 : 5 ≤ p) (t : K)
    (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (∀ ω, familyAGlobalCartier p t h3 ht0 ht1 (familyAGlobalCartier p t h3 ht0 ht1 ω) = 0) ↔
      (gPolynomial p).eval t = 0 := by
  rw [← familyA_all_regularCartier_square_zero_iff p hp5 t h3 ht0 ht1]
  constructor
  · intro h ω
    have hh := congrArg (familyAGlobalRegularEquiv t h3 ht0 ht1)
      (h ((familyAGlobalRegularEquiv t h3 ht0 ht1).symm ω))
    simpa [familyAGlobalCartier] using hh
  · intro h ω
    simp [familyAGlobalCartier, h]

theorem familyB_all_globalCartier_square_zero_iff (hp3 : 3 ≤ p) (t : K)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (∀ ω, familyBGlobalCartier p t ht0 ht1 (familyBGlobalCartier p t ht0 ht1 ω) = 0) ↔
      (hPolynomial p).eval t = 0 := by
  rw [← familyB_all_regularCartier_square_zero_iff p hp3 t ht0 ht1]
  constructor
  · intro h ω
    have hh := congrArg (familyBGlobalRegularEquiv t ht0 ht1)
      (h ((familyBGlobalRegularEquiv t ht0 ht1).symm ω))
    simpa [familyBGlobalCartier] using hh
  · intro h ω
    simp [familyBGlobalCartier, h]

end SupersingularCurves.IKO
