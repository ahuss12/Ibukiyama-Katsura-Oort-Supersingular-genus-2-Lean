/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.EllipticTorsionLiftingEndResidue
import Theorems.Thm_WeierstrassCurve_exists_isDefiniteRamifiedExactlyAt_isMaximalOrder_range_eq_rationalEndSubring

/-! # At least p² scalar values from a supersingular elliptic endomorphism order -/

set_option autoImplicit false
noncomputable section
namespace SupersingularCurves.Geometry.EllipticTorsionLiftingEndScalarImage
variable {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    [Algebra (ZMod p) K]

theorem affine_injective (z : K)
    (hz : ∀ c : ZMod p, algebraMap (ZMod p) K c ≠ z) :
    Function.Injective (fun ab : ZMod p × ZMod p =>
      algebraMap (ZMod p) K ab.1 + algebraMap (ZMod p) K ab.2 * z) := by
  intro x y h
  dsimp only at h
  have hs : x.2 = y.2 := by
    by_contra hne
    have hd : algebraMap (ZMod p) K (x.2 - y.2) ≠ 0 :=
      (map_ne_zero (algebraMap (ZMod p) K)).mpr (sub_ne_zero.mpr hne)
    apply hz ((y.1 - x.1) / (x.2 - y.2))
    rw [map_div₀, map_sub, map_sub]
    apply (div_eq_iff (by simpa using hd)).mpr
    linear_combination -h
  have hf : x.1 = y.1 := by
    apply (algebraMap (ZMod p) K).injective
    rw [hs] at h
    exact add_right_cancel h
  exact Prod.ext hf hs

theorem ring_image_contains_plane {R : Type*} [Ring R] (χ : R →+* K)
    (θ : R) (t n : ℤ) (hquad : θ ^ 2 - t * θ + n = 0)
    (hirr : ∀ c : ZMod p, c ^ 2 - (t : ZMod p) * c + (n : ZMod p) ≠ 0) :
    ∃ f : ZMod p × ZMod p → R, Function.Injective (χ ∘ f) := by
  have hq : (χ θ) ^ 2 - (t : K) * χ θ + (n : K) = 0 := by
    simpa using congrArg χ hquad
  have hnot : ∀ c : ZMod p, algebraMap (ZMod p) K c ≠ χ θ := by
    intro c hc
    apply hirr c
    apply (algebraMap (ZMod p) K).injective
    simpa [hc] using hq
  let f : ZMod p × ZMod p → R := fun ab => (ab.1.val : R) + (ab.2.val : R) * θ
  have heq : χ ∘ f = fun ab : ZMod p × ZMod p =>
      algebraMap (ZMod p) K ab.1 + algebraMap (ZMod p) K ab.2 * χ θ := by
    funext ab
    have hv : ∀ c : ZMod p, (c.val : K) = algebraMap (ZMod p) K c := by
      intro c
      rw [← map_natCast (algebraMap (ZMod p) K), ZMod.natCast_zmod_val]
    simp only [Function.comp_apply, f, map_add, map_mul, map_natCast, hv]
  exact ⟨f, heq ▸ affine_injective (χ θ) hnot⟩
theorem quadratic_pow_sq (x : K) (t n : ℤ)
    (hq : x ^ 2 - (t : K) * x + (n : K) = 0) : x ^ (p ^ 2) = x := by
  have ht : (t : K) ^ p = (t : K) := by
    simpa only [frobenius_def] using (map_intCast (frobenius K p) t)
  have hqp : (x ^ p) ^ 2 - (t : K) * (x ^ p) + (n : K) = 0 := by
    simpa only [map_sub, map_add, map_mul, map_pow, map_intCast, map_zero,
      frobenius_def] using congrArg (frobenius K p) hq
  have hfactor : (x ^ p - x) * (x ^ p + x - t) = 0 := by
    linear_combination hqp - hq
  rcases mul_eq_zero.mp hfactor with h | h
  · have hx : x ^ p = x := sub_eq_zero.mp h
    rw [pow_two, pow_mul, hx, hx]
  · have hx : x ^ p = (t : K) - x := by linear_combination h
    rw [pow_two, pow_mul, hx, sub_pow_char, ht, hx, sub_sub_cancel]

theorem range_eq_frobenius_fixed_of_plane {R : Type*} [Ring R] (χ : R →+* K)
    (hpow : ∀ r, χ r ^ (p ^ 2) = χ r)
    (hplane : ∃ f : ZMod p × ZMod p → R, Function.Injective (χ ∘ f)) :
    Set.range χ = {x : K | x ^ (p ^ 2) = x} := by
  classical
  obtain ⟨f, hf⟩ := hplane
  let values : Finset K := Finset.univ.image (χ ∘ f)
  let poly : Polynomial K := Polynomial.X ^ (p ^ 2) - Polynomial.X
  have hp : 1 < p ^ 2 := Nat.one_lt_pow (by decide) (Fact.out : p.Prime).one_lt
  have hd : poly.natDegree = p ^ 2 := FiniteField.X_pow_card_sub_X_natDegree_eq K hp
  have hp0 : poly ≠ 0 := by
    intro he
    rw [he, Polynomial.natDegree_zero] at hd
    exact (Nat.ne_of_gt hp) (by omega)
  have hmem : ∀ x, x ∈ poly.roots.toFinset ↔ x ^ (p ^ 2) = x := by
    intro x
    simp only [Multiset.mem_toFinset, Polynomial.mem_roots hp0, Polynomial.IsRoot.def,
      poly, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero]
  have hvcard : values.card = p ^ 2 := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ]
    simp [Fintype.card_prod, ZMod.card, pow_two]
  have hsub : values ⊆ poly.roots.toFinset := by
    intro x hx
    obtain ⟨ab, -, rfl⟩ := Finset.mem_image.mp hx
    exact (hmem _).mpr (hpow (f ab))
  have heq : values = poly.roots.toFinset :=
    Finset.eq_of_subset_of_card_le hsub (by
      rw [hvcard]
      exact (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' poly).trans_eq hd))
  ext x
  constructor
  · rintro ⟨r, rfl⟩
    exact hpow r
  · intro hx
    have hxv : x ∈ values := by rw [heq]; exact (hmem x).mpr hx
    obtain ⟨ab, -, hab⟩ := Finset.mem_image.mp hxv
    exact ⟨f ab, hab⟩

open scoped Quaternion
open QuaternionAlgebra

theorem quaternion_quadratic_relation {a b : ℚ} (θ : ℍ[ℚ, a, b]) (t n : ℤ)
    (ht : trd θ = (t : ℚ)) (hn : nrd θ = (n : ℚ)) :
    θ ^ 2 - t * θ + n = 0 := by
  rw [pow_two, ← QuaternionAlgebra.coe_intCast, ← QuaternionAlgebra.coe_intCast, ← ht, ← hn,
    ← add_star_eq_coe_trd, ← star_mul_eq_coe_nrd, add_mul]
  noncomm_ring

/-- Any scalar ring action of a maximal definite quaternion order ramified
at p contains p² different values. No faithfulness of the scalar action is
assumed. -/
theorem maximal_order_image_contains_plane {R : Type*} [Ring R]
    {a b : ℚ} (hdef : IsDefiniteRamifiedExactlyAt a b p)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (θ : R →+* ℍ[ℚ, a, b]) (hθ : Function.Injective θ)
    (hθΛ : Set.range θ = (Λ : Set ℍ[ℚ, a, b])) (χ : R →+* K) :
    ∃ f : ZMod p × ZMod p → R, Function.Injective (χ ∘ f) := by
  obtain ⟨q, hq, t, n, ht, hn, hirr⟩ :=
    EllipticTorsionLiftingEndResidue.UnramTheta.exists_irreducible_element hdef Λ hΛ
  have hrange : q ∈ Set.range θ := by rw [hθΛ]; exact hq
  obtain ⟨x, hx⟩ := hrange
  have hrel : x ^ 2 - t * x + n = 0 := by
    apply hθ
    simpa only [map_add, map_sub, map_pow, map_mul, map_intCast, map_zero, hx]
      using quaternion_quadratic_relation q t n ht hn
  exact ring_image_contains_plane χ x t n hrel hirr

/-- The full rational endomorphism order of a supersingular elliptic curve
has p² distinct values under every scalar ring action in characteristic p. -/
theorem rationalEnd_image_contains_plane
    {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k]
    [CharP k p] [Algebra (ZMod p) k] [Algebra.IsAlgebraic (ZMod p) k]
    (X : WeierstrassCurve k) [X.IsElliptic]
    (hss : ∀ P : X.toAffine.Point, p • P = 0 → P = 0)
    (χ : ↥(WeierstrassCurve.rationalEndSubring k X) →+* K) :
    ∃ f : ZMod p × ZMod p → ↥(WeierstrassCurve.rationalEndSubring k X),
      Function.Injective (χ ∘ f) := by
  obtain ⟨a, b, hdef, Λ, hΛ, θ, hθ, hθΛ⟩ :=
    WeierstrassCurve.exists_isDefiniteRamifiedExactlyAt_isMaximalOrder_range_eq_rationalEndSubring
      p X hss
  exact maximal_order_image_contains_plane hdef Λ hΛ θ hθ hθΛ χ

/-- Every scalar image of a quaternion order is fixed by p² Frobenius. -/
theorem order_scalar_pow_sq {R : Type*} [Ring R]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ)
    (θ : R →+* ℍ[ℚ, a, b]) (hθ : Function.Injective θ)
    (hθΛ : Set.range θ = (Λ : Set ℍ[ℚ, a, b])) (χ : R →+* K) (x : R) :
    χ x ^ (p ^ 2) = χ x := by
  have hxΛ : θ x ∈ Λ := by
    change θ x ∈ (Λ : Set ℍ[ℚ, a, b])
    rw [← hθΛ]
    exact ⟨x, rfl⟩
  obtain ⟨⟨n, hn⟩, t, ht⟩ :=
    IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hΛ hxΛ
  have hrel : x ^ 2 - t * x + n = 0 := by
    apply hθ
    simpa only [map_add, map_sub, map_pow, map_mul, map_intCast, map_zero]
      using quaternion_quadratic_relation (θ x) t n ht.symm hn.symm
  apply quadratic_pow_sq (χ x) t n
  simpa using congrArg χ hrel

/-- Exact residue-scalar image, with the ramified-order input proved above. -/
theorem maximal_order_range_eq_frobenius_fixed {R : Type*} [Ring R]
    {a b : ℚ} (hdef : IsDefiniteRamifiedExactlyAt a b p)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (θ : R →+* ℍ[ℚ, a, b]) (hθ : Function.Injective θ)
    (hθΛ : Set.range θ = (Λ : Set ℍ[ℚ, a, b])) (χ : R →+* K) :
    Set.range χ = {x : K | x ^ (p ^ 2) = x} :=
  range_eq_frobenius_fixed_of_plane χ
    (order_scalar_pow_sq Λ hΛ.isOrder θ hθ hθΛ χ)
    (maximal_order_image_contains_plane hdef Λ hΛ θ hθ hθΛ χ)

/-- The scalar image of the genuine rational endomorphism order is exactly
Fp² inside K. No assumed restriction-surjectivity or p-saturation is used. -/
theorem rationalEnd_range_eq_frobenius_fixed
    {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k]
    [CharP k p] [Algebra (ZMod p) k] [Algebra.IsAlgebraic (ZMod p) k]
    (X : WeierstrassCurve k) [X.IsElliptic]
    (hss : ∀ P : X.toAffine.Point, p • P = 0 → P = 0)
    (χ : ↥(WeierstrassCurve.rationalEndSubring k X) →+* K) :
    Set.range χ = {x : K | x ^ (p ^ 2) = x} := by
  obtain ⟨a, b, hdef, Λ, hΛ, θ, hθ, hθΛ⟩ :=
    WeierstrassCurve.exists_isDefiniteRamifiedExactlyAt_isMaximalOrder_range_eq_rationalEndSubring
      p X hss
  exact maximal_order_range_eq_frobenius_fixed hdef Λ hΛ θ hθ hθΛ χ

end SupersingularCurves.Geometry.EllipticTorsionLiftingEndScalarImage
