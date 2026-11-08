/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.PicardTorsion.Logarithm
import Theorems.Thm_AlgebraicCurve_exists_mem_D_eq_smul_D_of_isCurveOver

/-!
# Divisor-class p-torsion embeds in regular Cartier-fixed differentials

The source is `AlgebraicCurve.Pic0.torsion`, defined before any of the
cohomological computations. Regularity is proved at every valuation place
by writing a function with p-divisible order as a unit times a pth power.
The target uses the previously constructed, coordinate-independent Cartier
operator and the existing space of actual regular differentials.

This file does not assert the missing Cartier/Frobenius duality or a
Jacobian supersingularity criterion.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.PicardTorsion

open AlgebraicCurve KaehlerDifferential SupersingularCurves.Differentials

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
  [PerfectField K] [IsCurveOver K F] [Algebra.EssFiniteType K F]
  (p : ℕ) [CharP K p]

omit [CharP K p] in
/-- The logarithmic differential of a local unit is regular. -/
theorem logDerivative_unit_regular (v : Place K F) (u : v.toValuationSubringˣ) :
    v.IsRegularAt (logDerivative (K := K) ((u : v.toValuationSubring) : F)) := by
  obtain ⟨c, hc, hd⟩ := exists_mem_D_eq_smul_D_of_isCurveOver
    (K := K) v v.ord_uniformizer (u : v.toValuationSubring).property
  have huinv : (((u : v.toValuationSubring) : F))⁻¹ ∈ v.toValuationSubring := by
    have h : (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F) =
        (((u : v.toValuationSubring) : F))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      exact congrArg (fun z : v.toValuationSubring => (z : F)) u.inv_val
    rw [← h]
    exact ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring).property
  refine ⟨_, mul_mem huinv hc, ?_⟩
  change (((u : v.toValuationSubring) : F))⁻¹ • D K F ((u : v.toValuationSubring) : F) = _
  rw [hd, smul_smul]
  rfl

/-- The multiple-of-p order makes the uniformizer's logarithmic contribution vanish. -/
theorem logDerivative_regular_of_order_dvd (v : Place K F) {f : F} (hf : f ≠ 0)
    (hord : (p : ℤ) ∣ v.ord f) : v.IsRegularAt (logDerivative (K := K) f) := by
  let : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
  obtain ⟨n, hn⟩ := hord
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf v.irreducible_mk_uniformizer
  have hπ : v.uniformizer ≠ 0 := by
    intro hzero
    have h := v.ord_uniformizer
    rw [hzero, v.ord_zero] at h
    exact zero_ne_one h
  have hu0 : ((u : v.toValuationSubring) : F) ≠ 0 := by
    exact_mod_cast u.ne_zero
  have hlog : logDerivative (K := K) f =
      logDerivative (K := K) ((u : v.toValuationSubring) : F) := by
    rw [hu, logDerivative_mul hu0 (zpow_ne_zero _ hπ),
      logDerivative_zpow _ hπ, hn]
    have hz : ((p : ℤ) * n) • logDerivative (K := K) v.uniformizer = 0 := by
      rw [← Int.cast_smul_eq_zsmul F, Int.cast_mul, Int.cast_natCast,
        CharP.cast_eq_zero F p, zero_mul, zero_smul]
    rw [hz, add_zero]
  rw [hlog]
  exact logDerivative_unit_regular v u

/-- The actual logarithmic map lands in the existing global regular-differential space. -/
theorem logarithm_mem_regular (q : Pic0.torsion K F p) :
    logarithm p q ∈ regularDifferentials K F := by
  intro v
  apply logDerivative_regular_of_order_dvd p v (representativeFunction_ne_zero p q)
  exact ⟨(representativeDivisor p q : Divisor K F) v,
    (representativeFunction_orders p q v).symm⟩

/-- The canonical logarithmic map with its proved regular codomain. -/
def regularLogarithm (hC : ConstantsAreBase K F) :
    Pic0.torsion K F p →+ regularDifferentials K F where
  toFun q := ⟨logarithm p q, logarithm_mem_regular p q⟩
  map_zero' := Subtype.ext (logarithm_zero p hC)
  map_add' q r := Subtype.ext (logarithm_add p hC q r)

@[simp] theorem regularLogarithm_coe (hC : ConstantsAreBase K F)
    (q : Pic0.torsion K F p) :
    (regularLogarithm p hC q : Ω[F⁄K]) = logarithm p q := rfl

variable [Fact p.Prime] (x : F) [FiniteDimensional (IntermediateField.adjoin K {x}) F]

include x in
theorem regularLogarithm_injective (hC : ConstantsAreBase K F) :
    Function.Injective (regularLogarithm p hC) := by
  intro q r h
  exact logarithmHom_injective p x hC (congrArg Subtype.val h)

omit [Algebra.EssFiniteType K F] in
/-- The Cartier laws fix df/f; this is proved for the existing constructed operator. -/
theorem cartier_logDerivative {f : F} (hf : f ≠ 0) :
    cartier (K := K) p x (logDerivative f) = logDerivative f := by
  have hp : p - 1 + 1 = p := Nat.sub_add_cancel (Fact.out : p.Prime).one_le
  have hscalar : (f⁻¹) ^ p * f ^ (p - 1) = f⁻¹ := by
    apply (mul_left_inj' hf).mp
    rw [mul_assoc, ← pow_succ, hp, inv_pow, inv_mul_cancel₀ (pow_ne_zero p hf),
      inv_mul_cancel₀ hf]
  have hrepr : logDerivative (K := K) f =
      (f⁻¹) ^ p • (f ^ (p - 1) • D K F f) := by
    rw [smul_smul, hscalar]
    rfl
  conv_lhs => rw [hrepr]
  rw [cartier_pow_smul, cartier_normalization]
  rfl

theorem regularCartier_logarithm (hC : ConstantsAreBase K F) (q : Pic0.torsion K F p) :
    regularCartier p x (regularLogarithm p hC q) = regularLogarithm p hC q := by
  apply Subtype.ext
  exact cartier_logDerivative p x (representativeFunction_ne_zero p q)

/-- Fixed points of the already defined operator on actual regular differentials. -/
def regularFixed : AddSubgroup (regularDifferentials K F) :=
  (regularCartier p x - AddMonoidHom.id _).ker

omit [Algebra.EssFiniteType K F] in
theorem mem_regularFixed_iff (ω : regularDifferentials K F) :
    ω ∈ regularFixed p x ↔ regularCartier p x ω = ω := by
  change regularCartier p x ω - ω = 0 ↔ _
  exact sub_eq_zero

/-- The embedding reaches genuine regular Cartier fixed points. -/
def toRegularFixed (hC : ConstantsAreBase K F) : Pic0.torsion K F p →+ regularFixed (K := K) p x :=
  (regularLogarithm p hC).codRestrict (regularFixed p x)
    (fun q => (mem_regularFixed_iff p x _).mpr (regularCartier_logarithm p x hC q))

@[simp] theorem toRegularFixed_coe (hC : ConstantsAreBase K F) (q : Pic0.torsion K F p) :
    ((toRegularFixed p x hC q : regularFixed p x) : regularDifferentials K F) =
      regularLogarithm p hC q := rfl

theorem toRegularFixed_injective (hC : ConstantsAreBase K F) :
    Function.Injective (toRegularFixed p x hC) := by
  intro q r h
  exact regularLogarithm_injective p x hC (congrArg Subtype.val h)

/-- A usable vanishing consequence. The regular Cartier nilpotence hypothesis
is explicit and is not supplied by the earlier Frobenius theorem in this file. -/
theorem torsion_eq_zero_of_regularCartierCubed_zero (hC : ConstantsAreBase K F)
    (hN : ∀ ω : regularDifferentials K F,
      regularCartier p x (regularCartier p x (regularCartier p x ω)) = 0)
    (q : Pic0.torsion K F p) : q = 0 := by
  apply regularLogarithm_injective p x hC
  rw [map_zero]
  have h := hN (regularLogarithm p hC q)
  rwa [regularCartier_logarithm, regularCartier_logarithm, regularCartier_logarithm] at h

end SupersingularCurves.PicardTorsion
