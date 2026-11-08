/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.NewtonPolygon.WittValuation

/-!
# Newton polygons of actual F-isocrystals over finite fields

For k of cardinality p^r, Witt Frobenius has period r, so the r-th iterate of
isocrystal Frobenius is an actual linear automorphism. Its reverse characteristic
polynomial, valued using the Witt DVR and divided by r, defines its Newton
polygon. The period and linearity are proved, rather than assumed in the input.
No crystalline realization of a curve is asserted by this module.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SupersingularCurves.NewtonPolygon
open WittVector Polynomial
open scoped Isocrystal

variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [CharP k p] [PerfectRing k p]

theorem wittFrobenius_pow_coeff (r : ℕ) (x : WittVector p k) (i : ℕ) :
    (((WittVector.frobeniusEquiv p k) ^ r) x).coeff i = (x.coeff i) ^ (p ^ r) := by
  induction r generalizing x with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, RingAut.mul_apply, ih]
    change ((WittVector.frobenius x).coeff i) ^ (p ^ r) = _
    rw [WittVector.coeff_frobenius_charP, ← pow_mul, pow_succ]
    congr 1
    exact Nat.mul_comm _ _

theorem wittFrobenius_pow_eq_one [Fintype k] {r : ℕ}
    (hcard : Fintype.card k = p ^ r) : (WittVector.frobeniusEquiv p k) ^ r = 1 := by
  ext x i
  rw [wittFrobenius_pow_coeff, ← hcard, FiniteField.pow_card]
  rfl

/-- The scalar Frobenius period follows from the actual cardinality of k. -/
theorem fractionFrobenius_pow_eq_one [Fintype k] {r : ℕ}
    (hcard : Fintype.card k = p ^ r) : (WittVector.FractionRing.frobenius p k) ^ r = 1 := by
  have h := congrArg
    (IsFractionRing.ringEquivOfRingEquivHom (WittVector p k) K(p, k))
    (wittFrobenius_pow_eq_one p k hcard)
  simpa only [map_pow, map_one, IsFractionRing.ringEquivOfRingEquivHom_apply,
    WittVector.FractionRing.frobenius] using h

theorem fractionFrobenius_iterate [Fintype k] {r : ℕ}
    (hcard : Fintype.card k = p ^ r) (a : K(p, k)) :
    (φ(p, k) : K(p, k) → K(p, k))^[r] a = a := by
  have h := congrArg (fun e : K(p, k) ≃+* K(p, k) => e a)
    (fractionFrobenius_pow_eq_one p k hcard)
  change (⇑(WittVector.FractionRing.frobenius p k))^[r] a = a
  simpa only [RingAut.coe_pow, RingAut.coe_one, id_eq] using h

variable {V : Type*} [AddCommGroup V] [Isocrystal p k V]

theorem isocrystalFrobenius_iterate_add (r : ℕ) (x y : V) :
    (⇑(Φ(p, k) : V ≃ᶠˡ[p, k] V))^[r] (x + y) =
      (⇑(Φ(p, k) : V ≃ᶠˡ[p, k] V))^[r] x + (⇑(Φ(p, k) : V ≃ᶠˡ[p, k] V))^[r] y := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [Function.iterate_succ_apply', ih, map_add]

theorem isocrystalFrobenius_iterate_smul (r : ℕ) (a : K(p, k)) (x : V) :
    (⇑(Φ(p, k) : V ≃ᶠˡ[p, k] V))^[r] (a • x) =
      (φ(p, k) : K(p, k) → K(p, k))^[r] a • (⇑(Φ(p, k) : V ≃ᶠˡ[p, k] V))^[r] x := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [Function.iterate_succ_apply', ih, map_smulₛₗ]

/-- The q-Frobenius is an actual linear automorphism, constructed from the
semilinear isocrystal Frobenius and a proof that #k = p^r. -/
def frobeniusPower [Fintype k] (r : ℕ) (hcard : Fintype.card k = p ^ r) :
    V ≃ₗ[K(p, k)] V :=
  LinearEquiv.ofBijective
    { toFun := (⇑(Φ(p, k) : V ≃ᶠˡ[p, k] V))^[r]
      map_add' := isocrystalFrobenius_iterate_add p k r
      map_smul' := fun a x => by
        rw [isocrystalFrobenius_iterate_smul, fractionFrobenius_iterate p k hcard]
        rfl }
    ((Φ(p, k) : V ≃ᶠˡ[p, k] V).bijective.iterate r)

@[simp] theorem frobeniusPower_apply [Fintype k] (r : ℕ)
    (hcard : Fintype.card k = p ^ r) (x : V) :
    frobeniusPower p k r hcard x = (⇑(Φ(p, k) : V ≃ᶠˡ[p, k] V))^[r] x := rfl

/-- The normalized Newton polygon of an actual finite-field F-isocrystal. -/
def ofIsocrystal [Fintype k] (r : ℕ) [NeZero r]
    (hcard : Fintype.card k = p ^ r) (V : Type*) [AddCommGroup V]
    [Isocrystal p k V] [FiniteDimensional K(p, k) V] : Set (ℚ × ℚ) :=
  witt p k r (frobeniusPower p k (V := V) r hcard).toLinearMap.charpoly.reverse

variable {W : Type*} [AddCommGroup W] [Isocrystal p k W]

theorem isocrystalEquiv_iterate (e : V ≃ᶠⁱ[p, k] W) (r : ℕ) (x : V) :
    (⇑(Φ(p, k) : W ≃ᶠˡ[p, k] W))^[r] (e.toLinearEquiv x) =
      e.toLinearEquiv ((⇑(Φ(p, k) : V ≃ᶠˡ[p, k] V))^[r] x) := by
  induction r with
  | zero => rfl
  | succ r ih => rw [Function.iterate_succ_apply', ih, e.frob_equivariant,
      Function.iterate_succ_apply']

theorem frobeniusPower_conj [Fintype k] (r : ℕ) (hcard : Fintype.card k = p ^ r)
    (e : V ≃ᶠⁱ[p, k] W) :
    e.toLinearEquiv.conj (frobeniusPower p k (V := V) r hcard).toLinearMap =
      (frobeniusPower p k (V := W) r hcard).toLinearMap := by
  ext x
  change e.toLinearEquiv ((⇑(Φ(p, k) : V ≃ᶠˡ[p, k] V))^[r] (e.toLinearEquiv.symm x)) =
    (⇑(Φ(p, k) : W ≃ᶠˡ[p, k] W))^[r] x
  simpa using (isocrystalEquiv_iterate p k e r (e.toLinearEquiv.symm x)).symm

/-- Isomorphic F-isocrystals have the same Newton polygon. -/
theorem ofIsocrystal_eq_of_equiv [Fintype k] (r : ℕ) [NeZero r]
    (hcard : Fintype.card k = p ^ r)
    [FiniteDimensional K(p, k) V] [FiniteDimensional K(p, k) W]
    (e : V ≃ᶠⁱ[p, k] W) :
    ofIsocrystal p k r hcard V = ofIsocrystal p k r hcard W := by
  unfold ofIsocrystal
  rw [← frobeniusPower_conj p k r hcard e, LinearEquiv.charpoly_conj]

end SupersingularCurves.NewtonPolygon
