/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import Mathlib

/-! # Rational symplectic coordinates for alternating forms in dimension four -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
universe u v
namespace SupersingularCurves.Geometry.ScalarFrobeniusTate.Symplectic
open LinearMap
variable {F : Type u} [Field F]
variable {V : Type v} [AddCommGroup V] [Module F V]

def area (x y : F × F) : F := x.1 * y.2 - x.2 * y.1

theorem exists_normalized_pair [Nontrivial V] (B : LinearMap.BilinForm F V)
    (hB : B.Nondegenerate) : ∃ x y : V, B x y = 1 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  have hn : ∃ y, B x y ≠ 0 := by
    by_contra! hh
    exact hx (hB.1 x hh)
  obtain ⟨y, hy⟩ := hn
  refine ⟨x, (B x y)⁻¹ • y, ?_⟩
  rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hy]

def pairSection (x y : V) : (F × F) →ₗ[F] V :=
  (LinearMap.toSpanSingleton F V x).coprod (LinearMap.toSpanSingleton F V y)

@[simp] theorem pairSection_apply (x y : V) (z : F × F) :
    pairSection x y z = z.1 • x + z.2 • y := rfl

def pairProjection (B : LinearMap.BilinForm F V) (x y : V) : V →ₗ[F] F × F :=
  (B.flip y).prod (-(B.flip x))

@[simp] theorem pairProjection_apply (B : LinearMap.BilinForm F V) (x y z : V) :
    pairProjection B x y z = (B z y, -B z x) := rfl

variable (B : LinearMap.BilinForm F V) (hAlt : B.IsAlt) (x y : V) (hxy : B x y = 1)

include hAlt hxy in
theorem pair_reverse : B y x = -1 := by rw [← hAlt.neg_eq, hxy]

include hAlt hxy in
theorem pairProjection_section (z : F × F) :
    pairProjection B x y (pairSection x y z) = z := by
  apply Prod.ext <;>
    simp [map_add, map_smul, hAlt.self_eq_zero, hxy, pair_reverse B hAlt x y hxy]

include B hAlt hxy in
theorem pairSection_injective : Function.Injective (pairSection (F := F) x y) :=
  (show Function.LeftInverse (pairProjection B x y) (pairSection x y) from
    pairProjection_section B hAlt x y hxy).injective

include hAlt hxy in
theorem pairSection_form (a b : F × F) :
    B (pairSection x y a) (pairSection x y b) = area a b := by
  simp only [pairSection_apply, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, hAlt.self_eq_zero, hxy,
    pair_reverse B hAlt x y hxy, area]
  ring

abbrev PairComplement := LinearMap.ker (pairProjection B x y)

def remainder : V →ₗ[F] PairComplement B x y :=
  (LinearMap.id - (pairSection x y).comp (pairProjection B x y)).codRestrict
    (PairComplement B x y) (fun z => by
      change pairProjection B x y (z - pairSection x y (pairProjection B x y z)) = 0
      rw [map_sub, pairProjection_section B hAlt x y hxy, sub_self])

@[simp] theorem remainder_coe (z : V) :
    (remainder B hAlt x y hxy z : V) = z - pairSection x y (pairProjection B x y z) := rfl

def pairSplit : V ≃ₗ[F] (F × F) × PairComplement B x y :=
  LinearEquiv.ofLinearMap ((pairProjection B x y).prod (remainder B hAlt x y hxy))
    ((pairSection x y).coprod (PairComplement B x y).subtype)
    (by
      apply LinearMap.ext
      intro z
      apply Prod.ext
      · change pairProjection B x y (pairSection x y z.1 + z.2) = z.1
        rw [map_add, pairProjection_section B hAlt x y hxy, z.2.2, add_zero]
      · apply Subtype.ext
        change (pairSection x y z.1 + (z.2 : V)) -
          pairSection x y (pairProjection B x y (pairSection x y z.1 + z.2)) = z.2
        rw [map_add, pairProjection_section B hAlt x y hxy, z.2.2, add_zero]
        abel)
    (by
      apply LinearMap.ext
      intro z
      change pairSection x y (pairProjection B x y z) +
        (z - pairSection x y (pairProjection B x y z)) = z
      abel)

theorem complement_first (z : PairComplement B x y) : B (z : V) x = 0 := by
  have h := congrArg Prod.snd z.2
  change -B (z : V) x = 0 at h
  exact neg_eq_zero.mp h

theorem complement_second (z : PairComplement B x y) : B (z : V) y = 0 := by
  exact congrArg Prod.fst z.2

theorem complement_pair_left (z : PairComplement B x y) (a : F × F) :
    B (z : V) (pairSection x y a) = 0 := by
  simp [map_add, map_smul, complement_first B x y z, complement_second B x y z]

include hAlt in
theorem pair_complement_right (z : PairComplement B x y) (a : F × F) :
    B (pairSection x y a) (z : V) = 0 := by
  rw [← hAlt.neg_eq, complement_pair_left, neg_zero]

include hAlt hxy in
theorem complement_nondegenerate (hB : B.Nondegenerate) :
    (B.restrict (PairComplement B x y)).Nondegenerate := by
  have hl : (B.restrict (PairComplement B x y)).SeparatingLeft := by
    intro z hz
    apply Subtype.ext
    apply hB.1
    intro v
    have hv : v = pairSection x y (pairProjection B x y v) +
        (remainder B hAlt x y hxy v : V) := by simp only [remainder_coe]; abel
    rw [hv, map_add, complement_pair_left, zero_add]
    exact hz (remainder B hAlt x y hxy v)
  refine ⟨hl, ?_⟩
  intro z hz
  apply hl z
  intro w
  change B (z : V) (w : V) = 0
  rw [← hAlt.neg_eq]
  change -((B.restrict (PairComplement B x y)) w z) = 0
  rw [hz w, neg_zero]

theorem pairSplit_form (v w : V) :
    B v w = area (pairSplit B hAlt x y hxy v).1 (pairSplit B hAlt x y hxy w).1 +
      (B.restrict (PairComplement B x y))
        (pairSplit B hAlt x y hxy v).2 (pairSplit B hAlt x y hxy w).2 := by
  have hv := (pairSplit B hAlt x y hxy).symm_apply_apply v
  have hw := (pairSplit B hAlt x y hxy).symm_apply_apply w
  change pairSection x y (pairProjection B x y v) +
      (remainder B hAlt x y hxy v : V) = v at hv
  change pairSection x y (pairProjection B x y w) +
      (remainder B hAlt x y hxy w : V) = w at hw
  calc
    B v w = B (pairSection x y (pairProjection B x y v) + remainder B hAlt x y hxy v)
      (pairSection x y (pairProjection B x y w) + remainder B hAlt x y hxy w) := by
        rw [hv, hw]
    _ = _ := by
      simp only [map_add, LinearMap.add_apply,
        pair_complement_right B hAlt x y, complement_pair_left B x y,
        pairSection_form B hAlt x y hxy, add_zero, zero_add]
      rfl

section Coordinates
variable [FiniteDimensional F V]

/-- A genuine nondegenerate alternating plane has normalized coordinates. -/
theorem exists_coordinates_two (B : LinearMap.BilinForm F V) (hAlt : B.IsAlt)
    (hB : B.Nondegenerate) (hdim : Module.finrank F V = 2) :
    ∃ e : V ≃ₗ[F] F × F, ∀ v w, B v w = area (e v) (e w) := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (M := V) (by omega)
  obtain ⟨x, y, hxy⟩ := exists_normalized_pair B hB
  let e : (F × F) ≃ₗ[F] V := LinearEquiv.ofInjectiveOfFinrankEq
    (pairSection x y) (pairSection_injective B hAlt x y hxy)
    (by simpa using hdim.symm)
  have he (a b : F × F) : B (e a) (e b) = area a b :=
    pairSection_form B hAlt x y hxy a b
  refine ⟨e.symm, fun v w => ?_⟩
  simpa only [LinearEquiv.apply_symm_apply] using he (e.symm v) (e.symm w)

def areaFour (x y : (F × F) × (F × F)) : F := area x.1 y.1 + area x.2 y.2

/-- Actual symplectic coordinates in dimension four, constructed by splitting
off two normalized alternating planes. -/
theorem exists_coordinates_four (B : LinearMap.BilinForm F V) (hAlt : B.IsAlt)
    (hB : B.Nondegenerate) (hdim : Module.finrank F V = 4) :
    ∃ e : V ≃ₗ[F] (F × F) × (F × F), ∀ v w, B v w = areaFour (e v) (e w) := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (M := V) (by omega)
  obtain ⟨x, y, hxy⟩ := exists_normalized_pair B hB
  let e₁ := pairSplit B hAlt x y hxy
  have hpdim : Module.finrank F (PairComplement B x y) = 2 := by
    have hh := e₁.finrank_eq
    simp only [Module.finrank_prod, Module.finrank_self] at hh
    omega
  have hpalt : (B.restrict (PairComplement B x y)).IsAlt :=
    fun z => hAlt.self_eq_zero (z : V)
  obtain ⟨e₂, he₂⟩ := exists_coordinates_two (B.restrict (PairComplement B x y))
    hpalt (complement_nondegenerate B hAlt x y hxy hB) hpdim
  let e := e₁.trans ((LinearEquiv.refl F (F × F)).prodCongr e₂)
  refine ⟨e, fun v w => ?_⟩
  change B v w = area (e₁ v).1 (e₁ w).1 + area (e₂ (e₁ v).2) (e₂ (e₁ w).2)
  rw [← he₂]
  exact pairSplit_form B hAlt x y hxy v w

def reverseFour : ((F × F) × (F × F)) ≃ₗ[F] (F × F) × (F × F) :=
  (LinearEquiv.prodComm F F F).prodCongr (LinearEquiv.prodComm F F F)

theorem areaFour_reverse (v w : (F × F) × (F × F)) :
    areaFour (reverseFour v) (reverseFour w) = -areaFour v w := by
  simp only [reverseFour, LinearEquiv.prodCongr_apply, LinearEquiv.prodComm_apply,
    areaFour, area, Prod.swap]
  ring

variable {W : Type v} [AddCommGroup W] [Module F W] [FiniteDimensional F W]

/-- Any two nondegenerate alternating spaces of dimension four admit an
anti-isometry; the reversal supplies the sign required for a product graph. -/
theorem exists_antiIsometry_four (B : LinearMap.BilinForm F V) (C : LinearMap.BilinForm F W)
    (hBalt : B.IsAlt) (hCalt : C.IsAlt) (hB : B.Nondegenerate) (hC : C.Nondegenerate)
    (hV : Module.finrank F V = 4) (hW : Module.finrank F W = 4) :
    ∃ e : V ≃ₗ[F] W, ∀ v w, C (e v) (e w) = -B v w := by
  obtain ⟨eV, heV⟩ := exists_coordinates_four B hBalt hB hV
  obtain ⟨eW, heW⟩ := exists_coordinates_four C hCalt hC hW
  refine ⟨eV.trans (reverseFour.trans eW.symm), fun v w => ?_⟩
  rw [heW]
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [areaFour_reverse, ← heV]

end Coordinates

end SupersingularCurves.Geometry.ScalarFrobeniusTate.Symplectic
