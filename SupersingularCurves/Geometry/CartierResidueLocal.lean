/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Differentials.Cartier
import SupersingularCurves.Geometry.ResidueFoundation
import Definitions.Def_AlgebraicCurve_SerrePairing

/-! # Cartier and canonical local residues

The local identity is proved for arbitrary pole order. The proof characterizes
the canonical residue by regular terms, the simple pole, and higher pole
monomials; it uses the existing Cartier operator and actual local residues.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

namespace SupersingularCurves.Geometry.CartierResidue
open AlgebraicCurve KaehlerDifferential
open SupersingularCurves.Differentials

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [IsCurveOver K F] [PerfectField K]
variable (p : ℕ) [hp : Fact p.Prime] [CharP K p]
variable (x : F) [FiniteDimensional (IntermediateField.adjoin K {x}) F]

theorem cartier_small_power (t : F) {i : ℕ} (hi : i < p - 1) :
    cartier p x (t ^ i • D K F t) = 0 := by
  let : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
  have hi1 : ((i + 1 : ℕ) : F) ≠ 0 := by
    intro h0
    have hdvd := (CharP.cast_eq_zero_iff F p (i + 1)).mp h0
    have hlt : i + 1 < p := by omega
    exact absurd (Nat.le_of_dvd (Nat.succ_pos _) hdvd) (not_le.mpr hlt)
  have hep : (((i + 1 : ℕ) : F)⁻¹) ^ p = (((i + 1 : ℕ) : F)⁻¹) := by
    rw [inv_pow, ← frobenius_def, map_natCast]
  have hD : t ^ i • D K F t = (((i + 1 : ℕ) : F)⁻¹) • D K F (t ^ (i + 1)) := by
    rw [Derivation.leibniz_pow, Nat.add_sub_cancel, ← Nat.cast_smul_eq_nsmul F (i + 1),
      smul_smul, inv_mul_cancel₀ hi1, one_smul]
  rw [hD, ← hep, cartier_pow_smul, cartier_exact, smul_zero]

/-- Cartier on negative monomials, including every possible pole order. -/
theorem cartier_inverse_power (t : F) (ht : t ≠ 0) (n : ℕ) :
    cartier p x ((t ^ (n + 1))⁻¹ • D K F t) =
      if n % p = 0 then (t ^ (n / p + 1))⁻¹ • D K F t else 0 := by
  have hp0 : 0 < p := hp.out.pos
  have hr : n % p < p := Nat.mod_lt n hp0
  have he : (t ^ (n + 1))⁻¹ =
      ((t ^ (n / p + 1))⁻¹) ^ p * t ^ (p - 1 - n % p) := by
    have hexp : (n / p + 1) * p = (n + 1) + (p - 1 - n % p) := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (n / p) p]
      have := Nat.mod_add_div n p
      omega
    rw [inv_pow, ← pow_mul, hexp, pow_add t (n + 1) (p - 1 - n % p), mul_inv, mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ ht), mul_one]
  rw [he, mul_smul, cartier_pow_smul]
  split_ifs with hn
  · rw [hn, Nat.sub_zero, cartier_normalization]
  · rw [cartier_small_power p x t (by omega), smul_zero]

variable (v : Place K F) [v.DCoordGenerates]
variable [HasCanonicalLocalResidueKStar K F]

/-- Residue of the actual Kähler differential in the fixed uniformizer. -/
def differentialResidue (ω : Ω[F⁄K]) : v.ResidueField :=
  v.localResidue (v.differentialCoeff ω)

omit [PerfectField K] in
theorem differentialResidue_smul_dCoord (f : F) :
    differentialResidue v (f • v.dCoord) = v.localResidue f := by
  simp [differentialResidue, v.differentialCoeff_smul, v.differentialCoeff_dCoord]

omit [PerfectField K] in
theorem differentialResidue_add (ω η : Ω[F⁄K]) :
    differentialResidue v (ω + η) = differentialResidue v ω + differentialResidue v η := by
  simp [differentialResidue, v.differentialCoeff_add]

omit [PerfectField K] in
theorem differentialResidue_smul (a : K) (ω : Ω[F⁄K]) :
    differentialResidue v (a • ω) = a • differentialResidue v ω := by
  simp only [differentialResidue, v.differentialCoeff_smul_algebraMap,
    ← Algebra.smul_def, map_smul]

theorem differentialResidue_of_regular {ω : Ω[F⁄K]} (hω : v.IsRegularAt ω) :
    differentialResidue v ω = 0 := by
  obtain ⟨f, hf, rfl⟩ := hω
  rw [differentialResidue_smul_dCoord, v.localResidue_of_mem hf]

theorem differentialResidue_of_simpleResidue {ω : Ω[F⁄K]} {r : K}
    (hω : v.HasSimpleResidue ω r) :
    differentialResidue v ω = algebraMap K v.ResidueField r := by
  obtain ⟨f, rfl, hf, hres⟩ := hω
  rw [differentialResidue_smul_dCoord, v.localResidue_simplePole f hf]
  exact hres

omit [HasCanonicalLocalResidueKStar K F] in
theorem cartier_smul (a : K) (ω : Ω[F⁄K]) :
    cartier p x (a • ω) = (frobeniusEquiv K p).symm a • cartier p x ω := by
  have h := cartier_pow_smul p x
    (algebraMap K F ((frobeniusEquiv K p).symm a)) ω
  simpa only [← (algebraMap K F).map_pow, frobeniusEquiv_symm_pow_p,
    algebraMap_smul] using h

/-- Taking the pth power after Cartier makes the residue K-linear. -/
def cartierResidueCandidate : F →ₗ[K] v.ResidueField := by
  letI : CharP v.ResidueField p :=
    charP_of_injective_algebraMap (algebraMap K v.ResidueField).injective p
  exact
  { toFun := fun f => differentialResidue v (cartier p x (f • v.dCoord)) ^ p
    map_add' := by
      intro a b
      simp only [add_smul, map_add, differentialResidue_add, add_pow_char]
    map_smul' := by
      intro a f
      rw [smul_assoc, cartier_smul, differentialResidue_smul]
      simp only [Algebra.smul_def, mul_pow, ← (algebraMap K v.ResidueField).map_pow,
        frobeniusEquiv_symm_pow_p, RingHom.id_apply] }

theorem cartierResidueCandidate_regular (f : F) (hf : f ∈ v.toValuationSubring) :
    cartierResidueCandidate p x v f = 0 := by
  change differentialResidue v (cartier p x (f • v.dCoord)) ^ p = 0
  rw [differentialResidue_of_regular v (cartier_regularAt p x v ⟨f, hf, rfl⟩),
    zero_pow hp.out.ne_zero]

theorem cartierResidueCandidate_higherPole (n : ℕ) (hn : 1 ≤ n) :
    cartierResidueCandidate p x v (v.uniformizer ^ (n + 1))⁻¹ = 0 := by
  change differentialResidue v
    (cartier p x ((v.uniformizer ^ (n + 1))⁻¹ • v.dCoord)) ^ p = 0
  rw [v.dCoord_eq, cartier_inverse_power p x v.uniformizer v.uniformizer_ne_zero]
  split_ifs with hmod
  · rw [← v.dCoord_eq, differentialResidue_smul_dCoord,
      v.localResidue_higherPoleMonomial]
    · exact zero_pow hp.out.ne_zero
    · change 1 ≤ n / p
      have := Nat.mod_add_div n p
      have := hp.out.pos
      by_contra h
      have hquot : (n / p : ℕ) = 0 := Nat.eq_zero_of_not_pos h
      simp only [hquot, hmod, mul_zero, zero_add] at *
      omega
  · simp [differentialResidue, v.differentialCoeff_zero, hp.out.ne_zero]

variable [IsAlgClosed K]

omit [PerfectField K] [v.DCoordGenerates] [HasCanonicalLocalResidueKStar K F] in
theorem residueField_surjective : Function.Surjective (algebraMap K v.ResidueField) := by
  let : Module.Finite K v.ResidueField := IsCurveOver.finite_residueField v
  let : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral.2

theorem cartierResidueCandidate_simplePole (f : F)
    (hf : v.uniformizer * f ∈ v.toValuationSubring) :
    cartierResidueCandidate p x v f = IsLocalRing.residue _ ⟨v.uniformizer * f, hf⟩ := by
  obtain ⟨r, hr⟩ := residueField_surjective v
    (IsLocalRing.residue _ ⟨v.uniformizer * f, hf⟩)
  have hs : v.HasSimpleResidue (f • v.dCoord) r := ⟨f, rfl, hf, hr.symm⟩
  obtain ⟨s, hsr, hCs⟩ :=
    (AlgebraicCurve.Place.isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_of_cartierLaws_of_finiteDimensional
      p x (cartier p x) (cartier_laws p x).1 (cartier_laws p x).2.1
      (cartier_laws p x).2.2 v (f • v.dCoord)).2.2 r hs
  change differentialResidue v (cartier p x (f • v.dCoord)) ^ p = _
  rw [differentialResidue_of_simpleResidue v hCs, ← map_pow, hsr, hr]

/-- The candidate satisfies the existing canonical-residue characterization. -/
def cartierCanonicalResidue : v.CanonicalLocalResidueDataK where
  res := cartierResidueCandidate p x v
  res_of_mem := cartierResidueCandidate_regular p x v
  res_simplePole := cartierResidueCandidate_simplePole p x v
  res_higherPoleMonomial := cartierResidueCandidate_higherPole p x v

/-- The Cartier residue identity for every rational coefficient, with arbitrary poles. -/
theorem localResidue_cartier_pow (f : F) :
    differentialResidue v (cartier p x (f • v.dCoord)) ^ p = v.localResidue f := by
  change (cartierCanonicalResidue p x v).res f =
    (HasCanonicalLocalResidueKStar.dataKStar v).res f
  rcases eq_or_ne f 0 with rfl | hf
  · rw [map_zero, map_zero]
  apply v.canonicalLocalResidueDataK_agree_on_poleSubmodule_of_surj
    (residueField_surjective v) _ _ (-v.ord f).toNat
  rw [v.mem_poleSubmodule_iff_ord hf]
  have := Int.self_le_toNat (-v.ord f)
  omega

theorem differentialResidue_cartier_pow (ω : Ω[F⁄K]) :
    differentialResidue v (cartier p x ω) ^ p = differentialResidue v ω := by
  conv_lhs => rw [← v.differentialCoeff_smul_dCoord ω]
  exact localResidue_cartier_pow p x v _

/-- The local adjointness formula used in the global residue pairing. -/
theorem differentialResidue_cartier_adjoint (f : F) (ω : Ω[F⁄K]) :
    differentialResidue v (f • cartier p x ω) ^ p =
      differentialResidue v (f ^ p • ω) := by
  rw [← cartier_pow_smul]
  exact differentialResidue_cartier_pow p x v _

omit hp [CharP K p] [PerfectField K] [v.DCoordGenerates]
  [HasCanonicalLocalResidueKStar K F] in
theorem trace_residueField_pow (r : v.ResidueField) :
    Algebra.trace K v.ResidueField (r ^ p) =
      (Algebra.trace K v.ResidueField r) ^ p := by
  let : Module.Finite K v.ResidueField := IsCurveOver.finite_residueField v
  obtain ⟨a, rfl⟩ := residueField_surjective v r
  rw [← map_pow, Algebra.trace_algebraMap, Algebra.trace_algebraMap]
  have hdim : Module.finrank K v.ResidueField = 1 :=
    IsCurveOver.deg_eq_one_of_isAlgClosed v
  simp [hdim]

/-- Canonical traced local residues make Cartier adjoint to pth-power pullback. -/
theorem kaehlerResidueTerm_cartier_pow (ω : Ω[F⁄K]) (a : Place K F → F) :
    kaehlerResidueTerm (cartier p x ω) a v ^ p =
      kaehlerResidueTerm ω (fun w => a w ^ p) v := by
  have h := congrArg (Algebra.trace K v.ResidueField)
    (differentialResidue_cartier_adjoint p x v (a v) ω)
  rw [trace_residueField_pow] at h
  simpa only [kaehlerResidueTerm, differentialResidue, v.differentialCoeff_smul] using h

end SupersingularCurves.Geometry.CartierResidue
