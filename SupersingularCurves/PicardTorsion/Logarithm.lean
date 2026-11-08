/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Differentials.Cartier
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_ModularCurve_KwNo6HspecCartierDlogCampaignFrame

/-!
# Logarithmic differentials of actual p-torsion divisor classes

The source is the existing degree-zero divisor-class group, modulo actual
principal divisors. For pD = div(f), the map sends [D] to df/f. We prove
independence of both choices and injectivity; no cohomology group is used
as a replacement definition of divisor-class torsion.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.PicardTorsion

open AlgebraicCurve KaehlerDifferential SupersingularCurves.Differentials

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The usual logarithmic Kähler differential. -/
abbrev logDerivative (f : F) : Ω[F⁄K] := kw_hwcd_dlog K f

@[simp] theorem logDerivative_one : logDerivative (K := K) (1 : F) = 0 :=
  kw_hwcd_dlog_one

theorem logDerivative_pow {f : F} (hf : f ≠ 0) (n : ℕ) :
    logDerivative (K := K) (f ^ n) = n • logDerivative f :=
  kw_hwcd_dlog_pow n hf

theorem logDerivative_mul {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    logDerivative (K := K) (f * g) = logDerivative f + logDerivative g :=
  kw_hwcd_dlog_mul hf hg

theorem logDerivative_inv {f : F} (hf : f ≠ 0) :
    logDerivative (K := K) f⁻¹ = -logDerivative f := by
  have h := logDerivative_mul (K := K) hf (inv_ne_zero hf)
  rw [mul_inv_cancel₀ hf, logDerivative_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem logDerivative_zpow (f : F) (hf : f ≠ 0) (n : ℤ) :
    logDerivative (K := K) (f ^ n) = n • logDerivative f := by
  cases n with
  | ofNat n =>
      change logDerivative (f ^ (n : ℤ)) = (n : ℤ) • logDerivative f
      simpa only [zpow_natCast, natCast_zsmul] using logDerivative_pow (K := K) hf n
  | negSucc n =>
      rw [zpow_negSucc, logDerivative_inv (pow_ne_zero _ hf), logDerivative_pow hf,
        negSucc_zsmul]

theorem logDerivative_algebraMap (c : K) :
    logDerivative (K := K) (algebraMap K F c) = 0 := by
  rw [logDerivative, kw_hwcd_dlog, Derivation.map_algebraMap, smul_zero]

theorem logDerivative_eq_of_same_orders (hC : ConstantsAreBase K F)
    {f g : F} (hf : f ≠ 0) (hg : g ≠ 0)
    (hord : ∀ v : Place K F, v.ord f = v.ord g) :
    logDerivative (K := K) f = logDerivative g := by
  have hmem : f * g⁻¹ ∈ LSpace (0 : Divisor K F) := by
    apply mem_lSpace_iff_ord.mpr
    right
    intro v
    rw [Finsupp.zero_apply, neg_zero, v.ord_mul hf (inv_ne_zero hg),
      v.ord_inv, hord v, add_neg_cancel]
  rw [hC] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hzero : logDerivative (K := K) (f * g⁻¹) = 0 := by
    rw [← hc]
    exact logDerivative_algebraMap c
  rw [logDerivative_mul hf (inv_ne_zero hg), logDerivative_inv hg,
    ← sub_eq_add_neg, sub_eq_zero] at hzero
  exact hzero

variable (p : ℕ) [CharP K p]

theorem logDerivative_pow_char {f : F} (hf : f ≠ 0) :
    logDerivative (K := K) (f ^ p) = 0 := by
  let : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
  exact kw_hwcd_dlog_pow_char p hf

/-- Equality of divisor classes suffices; the representing divisors need not be equal. -/
theorem logDerivative_eq_of_class_eq (hC : ConstantsAreBase K F)
    (D E : Divisor.degZero (K := K) (F := F))
    (hDE : Pic0.mk D = Pic0.mk E) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0)
    (hD : ∀ v : Place K F, (p : ℤ) * (D : Divisor K F) v = v.ord f)
    (hE : ∀ v : Place K F, (p : ℤ) * (E : Divisor K F) v = v.ord g) :
    logDerivative (K := K) f = logDerivative g := by
  have hprincipal : ((D - E : Divisor.degZero (K := K) (F := F)) :
      Divisor K F).IsPrincipal := (QuotientAddGroup.eq_iff_sub_mem).mp hDE
  obtain ⟨r, hr, horders⟩ := hprincipal
  have heq : logDerivative (K := K) f = logDerivative (g * r ^ p) := by
    apply logDerivative_eq_of_same_orders hC hf (mul_ne_zero hg (pow_ne_zero p hr))
    intro v
    rw [v.ord_mul hg (pow_ne_zero p hr), ← zpow_natCast r p, v.ord_zpow,
      ← hD v, ← hE v, ← horders v]
    change (p : ℤ) * (D : Divisor K F) v =
      (p : ℤ) * (E : Divisor K F) v +
        (p : ℤ) * ((D : Divisor K F) v - (E : Divisor K F) v)
    ring
  rw [logDerivative_mul hg (pow_ne_zero p hr), logDerivative_pow_char p hr,
    add_zero] at heq
  exact heq

/-- An actual divisor representative of the existing quotient class. -/
def representativeDivisor (q : Pic0.torsion K F p) : Divisor.degZero (K := K) (F := F) :=
  (Pic0.mk_surjective q.val).choose

omit [CharP K p] in
theorem representativeDivisor_class (q : Pic0.torsion K F p) :
    Pic0.mk (representativeDivisor p q) = q.val :=
  (Pic0.mk_surjective q.val).choose_spec

omit [CharP K p] in
/-- Torsion in the quotient supplies a genuine rational function with divisor pD. -/
theorem exists_representativeFunction (q : Pic0.torsion K F p) :
    ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F,
      (p : ℤ) * (representativeDivisor p q : Divisor K F) v = v.ord f := by
  have hz : Pic0.mk ((p : ℤ) • representativeDivisor p q) = 0 := by
    change (QuotientAddGroup.mk' _) ((p : ℤ) • representativeDivisor p q) = 0
    rw [map_zsmul]
    change (p : ℤ) • Pic0.mk (representativeDivisor p q) = 0
    rw [representativeDivisor_class]
    exact (Pic0.mem_torsion.mp q.property)
  have hprincipal : (((p : ℤ) • representativeDivisor p q :
      Divisor.degZero (K := K) (F := F)) : Divisor K F).IsPrincipal :=
    (QuotientAddGroup.eq_zero_iff _).mp hz
  obtain ⟨f, hf, hdiv⟩ := hprincipal
  exact ⟨f, hf, fun v => by simpa only [AddSubgroup.coe_zsmul, Finsupp.smul_apply,
    zsmul_eq_mul, Int.cast_id] using hdiv v⟩

def representativeFunction (q : Pic0.torsion K F p) : F :=
  (exists_representativeFunction p q).choose

omit [CharP K p] in
theorem representativeFunction_ne_zero (q : Pic0.torsion K F p) :
    representativeFunction p q ≠ 0 := (exists_representativeFunction p q).choose_spec.1

omit [CharP K p] in
theorem representativeFunction_orders (q : Pic0.torsion K F p) (v : Place K F) :
    (p : ℤ) * (representativeDivisor p q : Divisor K F) v =
      v.ord (representativeFunction p q) :=
  (exists_representativeFunction p q).choose_spec.2 v

/-- The chosen formula; independence of the presentation is proved below. -/
def logarithm (q : Pic0.torsion K F p) : Ω[F⁄K] :=
  logDerivative (representativeFunction p q)

theorem logarithm_eq (hC : ConstantsAreBase K F) (q : Pic0.torsion K F p)
    (D : Divisor.degZero (K := K) (F := F)) (hD : Pic0.mk D = q.val)
    {f : F} (hf : f ≠ 0)
    (hord : ∀ v : Place K F, (p : ℤ) * (D : Divisor K F) v = v.ord f) :
    logarithm p q = logDerivative (K := K) f :=
  logDerivative_eq_of_class_eq p hC _ D
    ((representativeDivisor_class p q).trans hD.symm)
    (representativeFunction_ne_zero p q) hf (representativeFunction_orders p q) hord

theorem logarithm_zero (hC : ConstantsAreBase K F) :
    logarithm (K := K) (F := F) p 0 = 0 := by
  rw [logarithm_eq p hC 0 0 rfl one_ne_zero (fun v => by simp [v.ord_one])]
  exact kw_hwcd_dlog_one

theorem logarithm_add (hC : ConstantsAreBase K F) (q r : Pic0.torsion K F p) :
    logarithm p (q + r) = logarithm p q + logarithm p r := by
  rw [logarithm_eq p hC (q + r) (representativeDivisor p q + representativeDivisor p r)
    (by rw [Pic0.mk_add, representativeDivisor_class, representativeDivisor_class]; rfl)
    (mul_ne_zero (representativeFunction_ne_zero p q) (representativeFunction_ne_zero p r))
    (fun v => by
      rw [v.ord_mul (representativeFunction_ne_zero p q) (representativeFunction_ne_zero p r),
        ← representativeFunction_orders p q v, ← representativeFunction_orders p r v]
      change (p : ℤ) * ((representativeDivisor p q : Divisor K F) v +
        (representativeDivisor p r : Divisor K F) v) = _
      ring)]
  exact logDerivative_mul (representativeFunction_ne_zero p q) (representativeFunction_ne_zero p r)

/-- An additive map from independently defined divisor-class p-torsion. -/
def logarithmHom (hC : ConstantsAreBase K F) : Pic0.torsion K F p →+ Ω[F⁄K] where
  toFun := logarithm p
  map_zero' := logarithm_zero p hC
  map_add' := logarithm_add p hC

section Injectivity

variable [Fact p.Prime] [IsCurveOver K F] [PerfectField K]
  (x : F) [FiniteDimensional (IntermediateField.adjoin K {x}) F]

include x in
/-- The kernel of the actual universal derivation consists of pth powers.
The finite-coordinate and perfect-base hypotheses discharge the expansion input. -/
theorem exists_pow_of_differential_eq_zero {f : F} (hf : D K F f = 0) :
    ∃ g : F, f = g ^ p := by
  let : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
  obtain ⟨t, ht⟩ := AlgebraicCurve.exists_D_ne_zero (K := K) (F := F)
  apply KwPke.kw_pke_ker_d_pthPower t ?_ ht hf
  intro z
  have hz : z ∈ KwPke.kw_pke_expansionField (ℓ := p) t := by
    obtain ⟨a, ha, -⟩ := AlgebraicCurve.pDigits_existsUnique p x ht z
    rw [ha]
    apply sum_mem
    intro i _
    apply mul_mem ?_ (pow_mem
      (IntermediateField.mem_adjoin_simple_self (KwPke.kw_pke_pthPowers F p) t) _)
    have hmem : a i ^ p ∈ KwPke.kw_pke_pthPowers F p :=
      (KwPke.kw_pke_mem_pthPowers_iff F p).mpr ⟨a i, rfl⟩
    exact (KwPke.kw_pke_expansionField (ℓ := p) t).algebraMap_mem ⟨a i ^ p, hmem⟩
  exact isSeparable_algebraMap
    (⟨z, (IntermediateField.mem_toSubfield _ z).mpr hz⟩ :
      (KwPke.kw_pke_expansionField (ℓ := p) t).toSubfield)

include x in
/-- A zero logarithmic differential forces the original divisor class to be zero. -/
theorem eq_zero_of_logarithm_eq_zero (q : Pic0.torsion K F p)
    (hq : logarithm p q = 0) : q = 0 := by
  have hd : D K F (representativeFunction p q) = 0 := by
    change (representativeFunction p q)⁻¹ • D K F (representativeFunction p q) = 0 at hq
    exact (smul_eq_zero.mp hq).resolve_left (inv_ne_zero (representativeFunction_ne_zero p q))
  obtain ⟨g, hg⟩ := exists_pow_of_differential_eq_zero p x hd
  have hg0 : g ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow (Fact.out : p.Prime).ne_zero] at hg
    exact representativeFunction_ne_zero p q hg
  have hprincipal : (representativeDivisor p q : Divisor K F).IsPrincipal := by
    refine ⟨g, hg0, fun v => ?_⟩
    apply mul_left_cancel₀ (Int.natCast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
    rw [representativeFunction_orders, hg, ← zpow_natCast g p, v.ord_zpow]
  apply Subtype.ext
  change q.val = 0
  rw [← representativeDivisor_class p q]
  exact (QuotientAddGroup.eq_zero_iff _).mpr hprincipal

include x in
theorem logarithm_eq_zero_iff (hC : ConstantsAreBase K F) (q : Pic0.torsion K F p) :
    logarithm p q = 0 ↔ q = 0 :=
  ⟨eq_zero_of_logarithm_eq_zero p x q, fun h => h ▸ logarithm_zero p hC⟩

include x in
/-- No nonzero p-torsion class is lost by the logarithmic map. -/
theorem logarithmHom_injective (hC : ConstantsAreBase K F) :
    Function.Injective (logarithmHom p hC) := by
  apply (injective_iff_map_eq_zero (logarithmHom p hC)).mpr
  exact eq_zero_of_logarithm_eq_zero p x

end Injectivity

end SupersingularCurves.PicardTorsion
