/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import Theorems.Thm_KaehlerDifferential_D_ne_zero_of_forall_pow_ne

/-!
# The differential kernel over a perfect field

For any extension of a perfect characteristic-p field, the kernel of the
actual universal derivation consists exactly of pth powers. There is no
restriction on transcendence degree or on the dimension of a variety.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace SupersingularCurves.Geometry.PerfectFieldDifferentialKernel

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
  (p : ℕ) [Fact p.Prime] [CharP K p] [CharP F p] [PerfectRing K p]

include p in
/-- The absolute universal derivation vanishes on a perfect base field. -/
theorem absolute_D_algebraMap_eq_zero (a : K) :
    KaehlerDifferential.D (⊥ : Subfield F) F (algebraMap K F a) = 0 := by
  obtain ⟨b, hb⟩ := surjective_frobenius K p a
  rw [← hb, frobenius_def, map_pow, Derivation.leibniz_pow,
    ← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero F p, zero_smul]

/-- Absolute differentiation becomes a derivation over any perfect base. -/
def absoluteDerivation (p : ℕ) [Fact p.Prime] [CharP K p] [CharP F p]
    [PerfectRing K p] : Derivation K F Ω[F⁄(⊥ : Subfield F)] where
  toFun := KaehlerDifferential.D (⊥ : Subfield F) F
  map_add' := map_add _
  map_smul' a b := by
    rw [Algebra.smul_def, Derivation.leibniz, absolute_D_algebraMap_eq_zero K F p, smul_zero,
      add_zero, algebraMap_smul]
    rfl
  map_one_eq_zero' := Derivation.map_one_eq_zero _
  leibniz' := Derivation.leibniz _

/-- Vanishing of a relative differential forces an actual pth root in the
extension field, using the pinned general-field differential theorem. -/
theorem exists_pow_eq_of_D_eq_zero (x : F)
    (hx : KaehlerDifferential.D K F x = 0) : ∃ y : F, y ^ p = x := by
  by_contra h
  push Not at h
  apply KaehlerDifferential.D_ne_zero_of_forall_pow_ne p (Fact.out : p.Prime) x h
  have hzero := congrArg (absoluteDerivation K F p).liftKaehlerDifferential hx
  rw [Derivation.liftKaehlerDifferential_comp_D, map_zero] at hzero
  exact hzero

/-- The kernel of universal differentiation over a perfect base is precisely
the image of Frobenius, in arbitrary transcendence degree. -/
theorem D_eq_zero_iff_exists_pow (x : F) :
    KaehlerDifferential.D K F x = 0 ↔ ∃ y : F, y ^ p = x := by
  refine ⟨exists_pow_eq_of_D_eq_zero K F p x, ?_⟩
  rintro ⟨y, rfl⟩
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul F,
    CharP.cast_eq_zero F p, zero_smul]

end SupersingularCurves.Geometry.PerfectFieldDifferentialKernel
