/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_eq_natCast_smul_of_two_le_padicValRat_nrd
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_mem_dvd_nrd_forall_ne_smul
import Theorems.Thm_QuaternionAlgebra_IsOrder_relIndex_span_smul_eq_pow_four
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Theorems.Thm_QuaternionAlgebra_nrd_mul

/-! # Residue scalars of a ramified definite quaternion order

The finite quotient argument is adapted from the pinned FLT proof for
indefinite orders. Here the local division input is instead supplied by
the proved definite maximal-order norm-divisibility theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000
noncomputable section
open scoped Quaternion
open QuaternionAlgebra
namespace SupersingularCurves.Geometry.EllipticTorsionLiftingEndResidue

namespace RamIdeal2

variable {a b : ℚ}

theorem star_mem_of_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hO : IsOrder Λ) {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) : star x ∈ Λ := by
  obtain ⟨-, t, ht⟩ := IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hO hx
  have hs : star x = ((trd x : ℚ) : ℍ[ℚ, a, b]) - x := by
    rw [← add_star_eq_coe_trd, add_sub_cancel_left]
  have hc : ((trd x : ℚ) : ℍ[ℚ, a, b]) = (t : ℤ) • (1 : ℍ[ℚ, a, b]) := by
    rw [← ht, ← Int.cast_smul_eq_zsmul ℚ, ← coe_mul_eq_smul, mul_one]
  rw [hs, hc]
  exact Λ.sub_mem (Λ.smul_mem _ hO.one_mem) hx

theorem nrd_add_coe (x : ℍ[ℚ, a, b]) (c : ℚ) : nrd (x + (c : ℍ[ℚ, a, b])) = nrd x + c * trd x + c ^ 2 := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  have hc : ((c : ℚ) : ℍ[ℚ, a, b]) = ⟨c, 0, 0, 0⟩ := rfl
  rw [hc, QuaternionAlgebra.mk_add_mk, nrd_mk, nrd_mk, trd_mk]
  ring

theorem mem_of_smul_mem_of_not_dvd {r : ℕ} (hrp : r.Prime) (J : Submodule ℤ ℍ[ℚ, a, b]) {z : ℍ[ℚ, a, b]} {m : ℤ}
    (hm : ¬ (r : ℤ) ∣ m) (h1 : m • z ∈ J) (h2 : (r : ℤ) • z ∈ J) : z ∈ J := by
  have hcop : IsCoprime (r : ℤ) m := (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hrp)).mpr hm
  obtain ⟨u, w, huw⟩ := hcop
  have : z = u • ((r : ℤ) • z) + w • (m • z) := by
    rw [smul_smul, smul_smul, ← add_smul, huw, one_smul]
  rw [this]
  exact J.add_mem (J.smul_mem u h2) (J.smul_mem w h1)

section Ramified



theorem two_le_padicValRat_mul_mul {r : ℕ} (hrp : r.Prime) {K : ℤ} (hK : K ≠ 0) :
    haveI : Fact r.Prime := ⟨hrp⟩
    2 ≤ padicValRat r ((r : ℚ) * (r : ℚ) * (K : ℚ)) := by
  haveI : Fact r.Prime := ⟨hrp⟩
  have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast hrp.ne_zero
  have hK0 : ((K : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hK
  rw [padicValRat.mul (mul_ne_zero hr0 hr0) hK0, padicValRat.mul hr0 hr0, padicValRat.self hrp.one_lt, padicValRat.of_int]
  have : (0 : ℤ) ≤ (padicValInt r K : ℤ) := by exact_mod_cast Nat.zero_le _
  omega

theorem coe_intCast_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hO : IsOrder Λ) (c : ℤ) : (((c : ℤ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
  have : (((c : ℤ) : ℚ) : ℍ[ℚ, a, b]) = (c : ℤ) • (1 : ℍ[ℚ, a, b]) := by
    rw [← Int.cast_smul_eq_zsmul ℚ, ← coe_mul_eq_smul, mul_one]
  rw [this]
  exact Λ.smul_mem _ hO.one_mem

theorem exists_eq_smul_of_nrd_eq_zero {r : ℕ} [Fact r.Prime]
    (hB : IsDefiniteRamifiedExactlyAt a b r)
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ)
    {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) (hx0 : nrd x = 0) :
    ∃ y ∈ Λ, x = (r : ℤ) • y := by
  have hxz : x = 0 := by
    by_contra hne
    have hpos :=
      P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_eq_natCast_smul_of_two_le_padicValRat_nrd.RamifiedHecke.nrd_pos_of_ne_zero
        hB.1 hB.2.1 hne
    rw [hx0] at hpos
    exact lt_irrefl _ hpos
  exact ⟨0, Λ.zero_mem, by simp [hxz]⟩

theorem exists_eq_smul_of_nrd_eq_sq_mul {r : ℕ} [Fact r.Prime]
    (hB : IsDefiniteRamifiedExactlyAt a b r)
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ)
    {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) (k : ℤ) (hk : nrd x = (r : ℚ) * (r : ℚ) * (k : ℚ)) :
    ∃ y ∈ Λ, x = (r : ℤ) • y := by
  have hrp : r.Prime := Fact.out
  by_cases hk0 : k = 0
  · exact exists_eq_smul_of_nrd_eq_zero hB hΛ hx (by rw [hk, hk0]; simp)
  · exact QuaternionAlgebra.IsMaximalOrder.exists_eq_natCast_smul_of_two_le_padicValRat_nrd hrp hB hΛ hx (Or.inr (by rw [hk]; exact two_le_padicValRat_mul_mul hrp hk0))

end Ramified

end RamIdeal2

open RamIdeal2 in
theorem leftIdeal_trichotomy
    {a b : ℚ} {r : ℕ} [Fact r.Prime]
    (hB : IsDefiniteRamifiedExactlyAt a b r)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) :

    ((∀ m ∈ Λ, ∀ x ∈ Λ, (∃ n : ℤ, nrd x = (r : ℚ) * n) → ∃ n : ℤ, nrd (m * x) = (r : ℚ) * n) ∧
      (∀ y ∈ Λ, ∃ n : ℤ, nrd ((r : ℤ) • y) = (r : ℚ) * n) ∧
      (∃ x ∈ Λ, (∃ n : ℤ, nrd x = (r : ℚ) * n) ∧ ¬ ∃ y ∈ Λ, x = (r : ℤ) • y) ∧
      (∃ x ∈ Λ, ¬ ∃ n : ℤ, nrd x = (r : ℚ) * n) ∧

      (∀ x ∈ Λ, ∀ x' ∈ Λ, (∃ n : ℤ, nrd x = (r : ℚ) * n) → (∃ n : ℤ, nrd x' = (r : ℚ) * n) →
        ∃ y ∈ Λ, x * x' = (r : ℤ) • y)) ∧

    ∀ J : Submodule ℤ ℍ[ℚ, a, b], J ≤ Λ → (∀ y ∈ Λ, (r : ℤ) • y ∈ J) → (∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) →
      (∀ x, x ∈ J ↔ ∃ y ∈ Λ, x = (r : ℤ) • y) ∨
      (∀ x, x ∈ J ↔ x ∈ Λ ∧ ∃ n : ℤ, nrd x = (r : ℚ) * n) ∨
      J = Λ := by
  classical
  have hO : IsOrder Λ := hΛ.isOrder
  have hrp : r.Prime := Fact.out
  haveI : Fact r.Prime := ⟨hrp⟩
  have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast hrp.ne_zero
  have hint : ∀ x ∈ Λ, ∃ n : ℤ, nrd x = (n : ℚ) := fun x hx => by
    obtain ⟨⟨n, hn⟩, -⟩ := IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hO hx
    exact ⟨n, hn.symm⟩

  have hsmul : ∀ y : ℍ[ℚ, a, b], (r : ℤ) • y = ((r : ℚ) : ℍ[ℚ, a, b]) * y := fun y => by
    rw [coe_mul_eq_smul, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  ·
    rintro m hm x hx ⟨n, hn⟩
    obtain ⟨k, hk⟩ := hint m hm
    exact ⟨k * n, by rw [QuaternionAlgebra.nrd_mul, hk, hn]; push_cast; ring⟩
  ·
    intro y hy
    obtain ⟨k, hk⟩ := hint y hy
    refine ⟨(r : ℤ) * k, ?_⟩
    rw [hsmul, QuaternionAlgebra.nrd_mul, nrd_coe, hk]; push_cast; ring
  ·
    obtain ⟨h, hh, hne, n, hn, ⟨k, hk⟩⟩ := IsOrder.exists_mem_dvd_nrd_forall_ne_smul hO r
    refine ⟨h, hh, ⟨k, ?_⟩, ?_⟩
    · rw [← hn, hk]; push_cast; ring
    · rintro ⟨y, hy, hhy⟩
      exact hne y hy hhy
  ·
    refine ⟨1, hO.one_mem, ?_⟩
    rintro ⟨n, hn⟩
    rw [nrd_one] at hn
    have h1 : (r : ℤ) * n = 1 := by exact_mod_cast hn.symm
    have hdvd : (r : ℤ) ∣ 1 := ⟨n, h1.symm⟩
    have : r ∣ 1 := by exact_mod_cast Int.natCast_dvd_natCast.mp (by simpa using hdvd)
    exact hrp.one_lt.ne' (Nat.dvd_one.mp this)
  ·
    rintro x hx y hy ⟨m, hm⟩ ⟨n, hn⟩
    exact RamIdeal2.exists_eq_smul_of_nrd_eq_sq_mul hB hΛ (hO.mul_mem hx hy) (m * n)
      (by rw [QuaternionAlgebra.nrd_mul, hm, hn]; push_cast; ring)

  intro J hJ hrJ hmulJ
  by_cases hA : ∃ x ∈ J, ¬ ∃ n : ℤ, nrd x = (r : ℚ) * n
  ·
    right; right
    obtain ⟨x, hxJ, hxn⟩ := hA
    have hxΛ : x ∈ Λ := hJ hxJ
    obtain ⟨n, hn⟩ := hint x hxΛ
    have hndvd : ¬ (r : ℤ) ∣ n := by
      rintro ⟨k, hk⟩
      exact hxn ⟨k, by rw [hn, hk]; push_cast; ring⟩
    apply le_antisymm hJ
    intro y hy
    have h1 : n • y ∈ J := by
      have hmem : y * star x * x ∈ J := hmulJ (y * star x) (hO.mul_mem hy (RamIdeal2.star_mem_of_mem hO hxΛ)) x hxJ
      rw [mul_assoc, star_mul_eq_coe_nrd, mul_coe_eq_smul, hn, Int.cast_smul_eq_zsmul] at hmem
      exact hmem
    exact RamIdeal2.mem_of_smul_mem_of_not_dvd hrp J hndvd h1 (hrJ y hy)
  · have hA' : ∀ x ∈ J, ∃ n : ℤ, nrd x = (r : ℚ) * n := by
      intro x hx
      by_contra hno
      exact hA ⟨x, hx, hno⟩
    by_cases hB' : ∃ x ∈ J, ¬ ∃ y ∈ Λ, x = (r : ℤ) • y
    ·
      right; left
      obtain ⟨x, hxJ, hxR⟩ := hB'
      have hxΛ : x ∈ Λ := hJ hxJ
      obtain ⟨m, hm⟩ := hA' x hxJ
      have hmdvd : ¬ (r : ℤ) ∣ m := by
        rintro ⟨k, hk⟩
        apply hxR
        exact RamIdeal2.exists_eq_smul_of_nrd_eq_sq_mul hB hΛ hxΛ k (by rw [hm, hk]; push_cast; ring)
      intro z
      constructor
      · intro hz; exact ⟨hJ hz, hA' z hz⟩
      · rintro ⟨hzΛ, n, hzn⟩
        have hzs : z * star x ∈ Λ := hO.mul_mem hzΛ (RamIdeal2.star_mem_of_mem hO hxΛ)
        obtain ⟨w, hw, hzw⟩ := RamIdeal2.exists_eq_smul_of_nrd_eq_sq_mul hB hΛ hzs (n * m)
          (by rw [QuaternionAlgebra.nrd_mul, nrd_star, hzn, hm]; push_cast; ring)

        have e1 : z * star x * x = ((r : ℚ) * m) • z := by
          rw [mul_assoc, star_mul_eq_coe_nrd, mul_coe_eq_smul, hm]
        have e2 : z * star x * x = (r : ℚ) • (w * x) := by
          rw [hzw, hsmul, mul_assoc, coe_mul_eq_smul]
        have e3 : (m : ℤ) • z = w * x := by
          have h12 : (r : ℚ) • ((m : ℚ) • z) = (r : ℚ) • (w * x) := by rw [smul_smul, ← e1, e2]
          have := smul_right_injective ℍ[ℚ, a, b] hr0 h12
          rw [← Int.cast_smul_eq_zsmul ℚ]
          exact this
        have h1 : (m : ℤ) • z ∈ J := by rw [e3]; exact hmulJ w hw x hxJ
        exact RamIdeal2.mem_of_smul_mem_of_not_dvd hrp J hmdvd h1 (hrJ z hzΛ)
    ·
      left
      have hC : ∀ x ∈ J, ∃ y ∈ Λ, x = (r : ℤ) • y := by
        intro x hx
        by_contra hno
        exact hB' ⟨x, hx, hno⟩
      intro z
      exact ⟨hC z, fun ⟨y, hy, hzy⟩ => hzy ▸ hrJ y hy⟩

namespace UnramTheta

variable {a b : ℚ}

theorem nrd_add_star_mul (x y : ℍ[ℚ, a, b]) : nrd (x + y) = nrd x + nrd y + trd (x * star y) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [nrd, trd, QuaternionAlgebra.mk_add_mk, QuaternionAlgebra.star_mk, QuaternionAlgebra.mk_mul_mk]
  ring

theorem nrd_add_coe (x : ℍ[ℚ, a, b]) (c : ℚ) : nrd (x + (c : ℍ[ℚ, a, b])) = nrd x + c * trd x + c ^ 2 := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  have hc : ((c : ℚ) : ℍ[ℚ, a, b]) = ⟨c, 0, 0, 0⟩ := rfl
  rw [hc, QuaternionAlgebra.mk_add_mk, nrd_mk, nrd_mk, trd_mk]
  ring

theorem trd_coe_mul (c : ℚ) (x : ℍ[ℚ, a, b]) : trd ((c : ℍ[ℚ, a, b]) * x) = c * trd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  have hc : ((c : ℚ) : ℍ[ℚ, a, b]) = ⟨c, 0, 0, 0⟩ := rfl
  rw [hc, QuaternionAlgebra.mk_mul_mk, trd_mk, trd_mk]
  ring

theorem zsmul_eq_coe_mul (r : ℕ) (y : ℍ[ℚ, a, b]) : (r : ℤ) • y = ((r : ℚ) : ℍ[ℚ, a, b]) * y := by
  rw [coe_mul_eq_smul, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast]

theorem mul_zsmul_comm' (m z : ℍ[ℚ, a, b]) (c : ℤ) : m * (c • z) = c • (m * z) := by
  rw [← Int.cast_smul_eq_zsmul ℚ, mul_smul_comm, Int.cast_smul_eq_zsmul]

theorem zsmul_mul_assoc' (m z : ℍ[ℚ, a, b]) (c : ℤ) : (c • m) * z = c • (m * z) := by
  rw [← Int.cast_smul_eq_zsmul ℚ, smul_mul_assoc, Int.cast_smul_eq_zsmul]

theorem star_mem_of_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hO : IsOrder Λ) {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) : star x ∈ Λ := by
  obtain ⟨-, t, ht⟩ := IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hO hx
  have hs : star x = ((trd x : ℚ) : ℍ[ℚ, a, b]) - x := by
    rw [← add_star_eq_coe_trd, add_sub_cancel_left]
  have hc : ((trd x : ℚ) : ℍ[ℚ, a, b]) = (t : ℤ) • (1 : ℍ[ℚ, a, b]) := by
    rw [← ht, ← Int.cast_smul_eq_zsmul ℚ, ← coe_mul_eq_smul, mul_one]
  rw [hs, hc]
  exact Λ.sub_mem (Λ.smul_mem _ hO.one_mem) hx

theorem coe_intCast_eq_zsmul (c : ℤ) : (((c : ℤ) : ℚ) : ℍ[ℚ, a, b]) = (c : ℤ) • (1 : ℍ[ℚ, a, b]) := by
  rw [← Int.cast_smul_eq_zsmul ℚ, ← coe_mul_eq_smul, mul_one]

theorem coe_intCast_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hO : IsOrder Λ) (c : ℤ) : (((c : ℤ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
  rw [coe_intCast_eq_zsmul]
  exact Λ.smul_mem _ hO.one_mem

theorem exists_irreducible_element {r : ℕ} [Fact r.Prime]
    (hB : IsDefiniteRamifiedExactlyAt a b r)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) :
    ∃ θ ∈ Λ, ∃ t n : ℤ, trd θ = (t : ℚ) ∧ nrd θ = (n : ℚ) ∧
      ∀ x : ZMod r, x ^ 2 - (t : ZMod r) * x + (n : ZMod r) ≠ 0 := by
  classical
  have hO : IsOrder Λ := hΛ.isOrder
  have hrp : r.Prime := Fact.out
  haveI : NeZero r := ⟨hrp.ne_zero⟩

  obtain ⟨⟨hleft, hrP, ⟨y, hyΛ, ⟨ny, hny⟩, hynot⟩, ⟨w, hwΛ, hwnot⟩, hsq⟩, htri⟩ :=
    leftIdeal_trichotomy hB Λ hΛ

  let InP : ℍ[ℚ, a, b] → Prop := fun x => x ∈ Λ ∧ ∃ n : ℤ, nrd x = (r : ℚ) * n
  have haddP : ∀ x x', InP x → InP x' → InP (x + x') := by
    rintro x x' ⟨hx, n, hn⟩ ⟨hx', n', hn'⟩
    refine ⟨Λ.add_mem hx hx', ?_⟩
    have hsx' : star x' ∈ Λ := star_mem_of_mem hO hx'
    obtain ⟨z, hz, hxz⟩ := hsq x hx (star x') hsx' ⟨n, hn⟩ ⟨n', by rw [nrd_star, hn']⟩
    obtain ⟨-, tz, htz⟩ := IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hO hz
    refine ⟨n + n' + tz, ?_⟩
    rw [nrd_add_star_mul, hxz, zsmul_eq_coe_mul, trd_coe_mul, ← htz, hn, hn']
    push_cast
    ring

  by_contra hcon
  push Not at hcon
  have hZP : ∀ θ ∈ Λ, ∃ c : ℤ, InP (θ + (((c : ℤ) : ℚ) : ℍ[ℚ, a, b])) := by
    intro θ hθ
    obtain ⟨⟨n, hn⟩, t, ht⟩ := IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hO hθ
    obtain ⟨x, hx⟩ := hcon θ hθ t n ht.symm hn.symm
    refine ⟨-(x.val : ℤ), Λ.add_mem hθ (coe_intCast_mem hO _), ?_⟩
    have hdiv : (r : ℤ) ∣ (x.val : ℤ) ^ 2 - t * x.val + n := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ZMod.natCast_zmod_val]
      exact hx
    obtain ⟨k, hk⟩ := hdiv
    refine ⟨k, ?_⟩
    rw [nrd_add_coe, ← hn, ← ht]
    have hk' : ((x.val : ℤ) : ℚ) ^ 2 - (t : ℚ) * ((x.val : ℤ) : ℚ) + (n : ℚ) = (r : ℚ) * (k : ℚ) := by
      exact_mod_cast hk
    push_cast
    linear_combination hk'

  set H : AddSubgroup ℍ[ℚ, a, b] :=
    (Submodule.span ℤ ((fun z : ℍ[ℚ, a, b] => (r : ℤ) • z) '' (Λ : Set ℍ[ℚ, a, b]))).toAddSubgroup with hH
  have hindex : H.relIndex Λ.toAddSubgroup = r ^ 4 :=
    QuaternionAlgebra.IsOrder.relIndex_span_smul_eq_pow_four hO r hrp.pos
  have hHmem : ∀ μ ∈ Λ, (r : ℤ) • μ ∈ H := by
    intro μ hμ
    rw [hH, Submodule.mem_toAddSubgroup]
    exact Submodule.subset_span ⟨μ, hμ, rfl⟩
  have hHmem' : ∀ z ∈ H, ∃ μ ∈ Λ, z = (r : ℤ) • μ := by
    intro z hz
    rw [hH, Submodule.mem_toAddSubgroup] at hz
    have hle : Submodule.span ℤ ((fun z : ℍ[ℚ, a, b] => (r : ℤ) • z) '' (Λ : Set ℍ[ℚ, a, b]))
        ≤ Λ.map ((r : ℤ) • (LinearMap.id : ℍ[ℚ, a, b] →ₗ[ℤ] ℍ[ℚ, a, b])) := by
      rw [Submodule.span_le]
      rintro z ⟨μ, hμ, rfl⟩
      exact Submodule.mem_map.2 ⟨μ, hμ, rfl⟩
    obtain ⟨μ, hμ, hμz⟩ := Submodule.mem_map.1 (hle hz)
    exact ⟨μ, hμ, by rw [← hμz]; rfl⟩
  have hHΛ : ∀ z ∈ H, z ∈ Λ := by
    intro z hz
    obtain ⟨μ, hμ, rfl⟩ := hHmem' z hz
    exact Λ.smul_mem _ hμ
  have hHP : ∀ z ∈ H, InP z := by
    intro z hz
    obtain ⟨μ, hμ, rfl⟩ := hHmem' z hz
    exact ⟨Λ.smul_mem _ hμ, hrP μ hμ⟩
  have hHzsmul : ∀ (c : ℤ), ∀ z ∈ H, c • z ∈ H := by
    intro c z hz
    obtain ⟨μ, hμ, rfl⟩ := hHmem' z hz
    rw [smul_comm]
    exact hHmem _ (Λ.smul_mem c hμ)
  set N : AddSubgroup ↥Λ.toAddSubgroup := H.addSubgroupOf Λ.toAddSubgroup with hN
  have hcardG : Nat.card (↥Λ.toAddSubgroup ⧸ N) = r ^ 4 := hindex
  haveI hfinG : Finite (↥Λ.toAddSubgroup ⧸ N) :=
    Nat.finite_of_card_ne_zero (by rw [hcardG]; exact pow_ne_zero _ hrp.ne_zero)
  have hmemN : ∀ m : ↥Λ.toAddSubgroup, m ∈ N ↔ (m : ℍ[ℚ, a, b]) ∈ H := fun m => Iff.rfl
  have hmk0 : ∀ m : ↥Λ.toAddSubgroup,
      (QuotientAddGroup.mk m : ↥Λ.toAddSubgroup ⧸ N) = 0 ↔ (m : ℍ[ℚ, a, b]) ∈ H := by
    intro m
    rw [QuotientAddGroup.eq_zero_iff, hmemN]

  let f : ↥Λ.toAddSubgroup →+ ↥Λ.toAddSubgroup :=
    { toFun := fun m => ⟨(m : ℍ[ℚ, a, b]) * y, hO.mul_mem m.2 hyΛ⟩
      map_zero' := by apply Subtype.ext; simp
      map_add' := fun m m' => by apply Subtype.ext; simp [add_mul] }
  have hf : ∀ m : ↥Λ.toAddSubgroup, ((f m : ↥Λ.toAddSubgroup) : ℍ[ℚ, a, b]) = (m : ℍ[ℚ, a, b]) * y :=
    fun _ => rfl
  have hfN : N ≤ N.comap f := by
    intro m hm
    rw [AddSubgroup.mem_comap, hmemN, hf]
    rw [hmemN] at hm
    obtain ⟨μ, hμ, hμe⟩ := hHmem' _ hm
    rw [hμe, zsmul_mul_assoc']
    exact hHmem _ (hO.mul_mem hμ hyΛ)
  let ψ : ↥Λ.toAddSubgroup ⧸ N →+ ↥Λ.toAddSubgroup ⧸ N := QuotientAddGroup.map N N f hfN
  have hψ : ∀ m : ↥Λ.toAddSubgroup, ψ (QuotientAddGroup.mk m) = QuotientAddGroup.mk (f m) := fun _ => rfl

  obtain ⟨z₀, hz₀, hyy⟩ := hsq y hyΛ y hyΛ ⟨ny, hny⟩ ⟨ny, hny⟩
  have hψψ : ∀ g : ↥Λ.toAddSubgroup ⧸ N, ψ (ψ g) = 0 := by
    intro g
    induction g using QuotientAddGroup.induction_on with | H m => ?_
    rw [hψ, hψ, hmk0, hf, hf, mul_assoc, hyy, mul_zsmul_comm']
    exact hHmem _ (hO.mul_mem m.2 hz₀)
  have hrk : ψ.range ≤ ψ.ker := by
    rintro g ⟨g', rfl⟩
    exact hψψ g'

  have hcard_mul : Nat.card (↥Λ.toAddSubgroup ⧸ N) = Nat.card ψ.range * Nat.card ψ.ker := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup ψ.ker,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange ψ).toEquiv]
  have hrange_le_ker : Nat.card ψ.range ≤ Nat.card ψ.ker :=
    Nat.card_le_card_of_injective (AddSubgroup.inclusion hrk) (AddSubgroup.inclusion_injective hrk)
  have hrange : Nat.card ψ.range ≤ r ^ 2 := by
    have h1 : Nat.card ψ.range * Nat.card ψ.range ≤ r ^ 2 * r ^ 2 := by
      calc Nat.card ψ.range * Nat.card ψ.range ≤ Nat.card ψ.range * Nat.card ψ.ker :=
            Nat.mul_le_mul_left _ hrange_le_ker
        _ = r ^ 4 := by rw [← hcard_mul, hcardG]
        _ = r ^ 2 * r ^ 2 := by ring
    exact Nat.mul_self_le_mul_self_iff.1 h1

  let J : Submodule ℤ ℍ[ℚ, a, b] :=
    { carrier := {x | ∃ l ∈ Λ, ∃ z ∈ H, x = l * y + z}
      add_mem' := by
        rintro x x' ⟨l, hl, z, hz, rfl⟩ ⟨l', hl', z', hz', rfl⟩
        exact ⟨l + l', Λ.add_mem hl hl', z + z', H.add_mem hz hz', by rw [add_mul]; abel⟩
      zero_mem' := ⟨0, Λ.zero_mem, 0, H.zero_mem, by simp⟩
      smul_mem' := by
        rintro c x ⟨l, hl, z, hz, rfl⟩
        exact ⟨c • l, Λ.smul_mem c hl, c • z, hHzsmul c z hz, by rw [smul_add, zsmul_mul_assoc']⟩ }
  have hJmem : ∀ x, x ∈ J ↔ ∃ l ∈ Λ, ∃ z ∈ H, x = l * y + z := fun x => Iff.rfl
  have hJΛ : J ≤ Λ := by
    intro x hx
    obtain ⟨l, hl, z, hz, rfl⟩ := (hJmem x).1 hx
    exact Λ.add_mem (hO.mul_mem hl hyΛ) (hHΛ z hz)
  have hJr : ∀ μ ∈ Λ, (r : ℤ) • μ ∈ J := fun μ hμ =>
    (hJmem _).2 ⟨0, Λ.zero_mem, (r : ℤ) • μ, hHmem μ hμ, by simp⟩
  have hJleft : ∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J := by
    intro m hm x hx
    obtain ⟨l, hl, z, hz, rfl⟩ := (hJmem x).1 hx
    obtain ⟨μ, hμ, rfl⟩ := hHmem' z hz
    refine (hJmem _).2 ⟨m * l, hO.mul_mem hm hl, (r : ℤ) • (m * μ), hHmem _ (hO.mul_mem hm hμ), ?_⟩
    rw [mul_add, mul_assoc, mul_zsmul_comm']
  have hJP : ∀ x ∈ J, InP x := by
    intro x hx
    obtain ⟨l, hl, z, hz, rfl⟩ := (hJmem x).1 hx
    exact haddP _ _ ⟨hO.mul_mem hl hyΛ, hleft l hl y hyΛ ⟨ny, hny⟩⟩ (hHP z hz)
  have hJeq : ∀ x, x ∈ J ↔ x ∈ Λ ∧ ∃ n : ℤ, nrd x = (r : ℚ) * n := by
    rcases htri J hJΛ hJr hJleft with h | h | h
    · exfalso
      apply hynot
      have hyJ : y ∈ J := (hJmem _).2 ⟨1, hO.one_mem, 0, H.zero_mem, by simp⟩
      exact (h y).1 hyJ
    · exact h
    · exfalso
      apply hwnot
      have hwJ : w ∈ J := by rw [h]; exact hwΛ
      exact (hJP w hwJ).2

  set one' : ↥Λ.toAddSubgroup := ⟨1, hO.one_mem⟩ with hone'
  set g₁ : ↥Λ.toAddSubgroup ⧸ N := QuotientAddGroup.mk one' with hg₁
  have hsurj : Function.Surjective
      (fun pr : ↥(AddSubgroup.zmultiples g₁) × ↥ψ.range =>
        (pr.1 : ↥Λ.toAddSubgroup ⧸ N) + (pr.2 : ↥Λ.toAddSubgroup ⧸ N)) := by
    intro g
    induction g using QuotientAddGroup.induction_on with | H m => ?_
    obtain ⟨c, hcP⟩ := hZP m m.2
    obtain ⟨l, hl, z, hz, hlz⟩ := (hJeq _).2 hcP
    refine ⟨⟨⟨(-c) • g₁, AddSubgroup.zsmul_mem_zmultiples g₁ (-c)⟩,
      ⟨ψ (QuotientAddGroup.mk ⟨l, hl⟩), ⟨_, rfl⟩⟩⟩, ?_⟩
    change (-c) • g₁ + ψ (QuotientAddGroup.mk ⟨l, hl⟩) = QuotientAddGroup.mk m
    rw [hψ, hg₁, ← QuotientAddGroup.mk_zsmul, ← QuotientAddGroup.mk_add]
    apply QuotientAddGroup.eq.2
    rw [hmemN]
    have e : ((-((-c) • one' + f ⟨l, hl⟩) + m : ↥Λ.toAddSubgroup) : ℍ[ℚ, a, b]) = z := by
      have hm : (m : ℍ[ℚ, a, b]) = l * y + z - (c : ℤ) • (1 : ℍ[ℚ, a, b]) := by
        rw [← hlz, coe_intCast_eq_zsmul, add_sub_cancel_right]
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, AddSubgroupClass.coe_zsmul, hf, hone', hm, neg_smul]
      abel
    rw [e]
    exact hz
  have hcard_le : Nat.card (↥Λ.toAddSubgroup ⧸ N) ≤
      Nat.card ↥(AddSubgroup.zmultiples g₁) * Nat.card ↥ψ.range := by
    rw [← Nat.card_prod]
    exact Nat.card_le_card_of_surjective _ hsurj
  have hzm : Nat.card ↥(AddSubgroup.zmultiples g₁) ≤ r := by
    rw [Nat.card_zmultiples]
    have h0 : r • g₁ = 0 := by
      rw [hg₁, ← QuotientAddGroup.mk_nsmul, hmk0]
      have : ((r • one' : ↥Λ.toAddSubgroup) : ℍ[ℚ, a, b]) = (r : ℤ) • (1 : ℍ[ℚ, a, b]) := by
        rw [AddSubmonoidClass.coe_nsmul, hone', natCast_zsmul]
      rw [this]
      exact hHmem 1 hO.one_mem
    exact Nat.le_of_dvd hrp.pos (addOrderOf_dvd_of_nsmul_eq_zero h0)

  have hle : r ^ 4 ≤ r * r ^ 2 :=
    calc r ^ 4 = Nat.card (↥Λ.toAddSubgroup ⧸ N) := hcardG.symm
      _ ≤ Nat.card ↥(AddSubgroup.zmultiples g₁) * Nat.card ↥ψ.range := hcard_le
      _ ≤ r * r ^ 2 := Nat.mul_le_mul hzm hrange
  have hle' : r ^ 3 * r ≤ r ^ 3 * 1 := by
    calc r ^ 3 * r = r ^ 4 := by ring
      _ ≤ r * r ^ 2 := hle
      _ = r ^ 3 * 1 := by ring
  have hr1 : r ≤ 1 := Nat.le_of_mul_le_mul_left hle' (pow_pos hrp.pos 3)
  exact absurd hrp.two_le (by omega)

end UnramTheta

end SupersingularCurves.Geometry.EllipticTorsionLiftingEndResidue
