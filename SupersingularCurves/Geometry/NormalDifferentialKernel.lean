/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.PerfectFieldDifferentialKernel

/-!
# The differential kernel in a normal domain

For a normal domain over a perfect field of characteristic p, the kernel of
the universal derivation consists exactly of pth powers. Map a differential
to the fraction field, apply the field theorem, and use integral closedness
to bring the pth root back into the domain. This works in every dimension
and does not require a curve hypothesis or a chosen differential basis.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.Geometry.NormalDifferentialKernel
open KaehlerDifferential

variable (K A : Type*) [Field K] [CommRing A] [IsDomain A]
  [Algebra K A] [IsIntegrallyClosed A]
  (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectRing K p]

/-- A function with zero universal differential in a normal domain has a
pth root in the domain itself, not merely in its fraction field. -/
theorem exists_pow_eq_of_D_eq_zero (x : A) (hx : D K A x = 0) :
    ∃ y : A, y ^ p = x := by
  classical
  have : CharP (FractionRing A) p :=
    charP_of_injective_algebraMap (algebraMap K (FractionRing A)).injective p
  have hFrac : D K (FractionRing A) (algebraMap A (FractionRing A) x) = 0 := by
    rw [← map_D K K A (FractionRing A), hx, map_zero]
  obtain ⟨y, hy⟩ :=
    PerfectFieldDifferentialKernel.exists_pow_eq_of_D_eq_zero K (FractionRing A) p
      (algebraMap A (FractionRing A) x) hFrac
  have hyInt : IsIntegral A (y ^ p) := by
    rw [hy]
    exact isIntegral_algebraMap
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
    (Fact.out : p.Prime).pos hyInt
  refine ⟨z, IsFractionRing.injective A (FractionRing A) ?_⟩
  rw [map_pow, hz, hy]

/-- The universal differential vanishes exactly on pth powers for a normal
domain over a perfect field. -/
theorem D_eq_zero_iff_exists_pow (x : A) :
    D K A x = 0 ↔ ∃ y : A, y ^ p = x := by
  have : CharP A p := charP_of_injective_algebraMap (algebraMap K A).injective p
  constructor
  · exact exists_pow_eq_of_D_eq_zero K A p x
  · rintro ⟨y, rfl⟩
    rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul A,
      CharP.cast_eq_zero A p, zero_smul]

end SupersingularCurves.Geometry.NormalDifferentialKernel
