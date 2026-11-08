/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Theorems.Thm_PDivisibleGroup_Hopf_nsmulAlgHom_eq_sum_pow_apply_smul_pow

/-!
# Canonical Verschiebung over a perfect field

The transpose of Frobenius on the Cartier dual of a finite commutative Hopf
algebra is inverse-Frobenius semilinear. The pairing characterizes it uniquely,
so it is natural under every finite group morphism, including morphisms which
are not yet known to lift to abelian varieties.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v w

namespace SupersingularCurves.Geometry.PerfectHopfVerschiebung
open CartierDual
open scoped TensorProduct

variable {K : Type u} [Field K] (p : ℕ) [Fact p.Prime]
  [hchar : CharP K p] [PerfectRing K p]
variable (A : Type v) [CommRing A] [hHopf : HopfAlgebra K A]
  [Coalgebra.IsCocomm K A] [Module.Finite K A]

include hHopf in
private theorem nontrivial_coord : Nontrivial A := by
  refine ⟨⟨1, 0, fun h => ?_⟩⟩
  have hh := congrArg (Coalgebra.counit (R := K) (A := A)) h
  rw [Bialgebra.counit_one, map_zero] at hh
  exact one_ne_zero hh

include hHopf hchar in
private theorem coord_charP : CharP A p := by
  letI := nontrivial_coord (K := K) A
  exact charP_of_injective_algebraMap (algebraMap K A).injective p

private theorem dual_nontrivial : Nontrivial (CartierDual K A) := by
  refine ⟨⟨1, 0, fun h => ?_⟩⟩
  have hh := congrArg (fun φ : CartierDual K A => φ 1) h
  rw [CartierDual.one_apply, Bialgebra.counit_one] at hh
  exact one_ne_zero hh

private theorem dual_charP : CharP (CartierDual K A) p := by
  letI := dual_nontrivial (K := K) A
  exact charP_of_injective_algebraMap (algebraMap K (CartierDual K A)).injective p

private def basisMap {ι : Type*} [Fintype ι] (b : Module.Basis ι K A) (a : A) : A :=
  ∑ i, (frobeniusEquiv K p).symm ((ofDual K A (b.coord i) ^ p) a) • b i

private theorem dual_expansion {ι : Type*} [Fintype ι] (b : Module.Basis ι K A)
    (φ : CartierDual K A) :
    φ = ∑ i, φ (b i) • ofDual K A (b.coord i) := by
  apply CartierDual.ext
  intro a
  have h := Module.Basis.sum_dual_apply_smul_coord b (toDual K A φ)
  have ha := congrArg (fun ψ : Module.Dual K A => ψ a) h
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, toDual_apply] at ha
  rw [← ha]
  change _ = (toDual K A (∑ i, φ (b i) • ofDual K A (b.coord i))) a
  rw [map_sum]
  simp only [map_smul, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
    toDual_ofDual]

private theorem basisMap_pairing {ι : Type*} [Fintype ι]
    (b : Module.Basis ι K A) (φ : CartierDual K A) (a : A) :
    φ (basisMap (K := K) p A b a) ^ p = (φ ^ p) a := by
  letI := dual_charP (K := K) p A
  rw [basisMap, map_sum, sum_pow_char]
  simp only [map_smul, smul_eq_mul, mul_pow, frobeniusEquiv_symm_pow_p]
  conv_rhs => rw [dual_expansion (K := K) A b φ, sum_pow_char]
  simp only [smul_pow]
  change _ = (toDual K A (∑ i, φ (b i) ^ p • ofDual K A (b.coord i) ^ p)) a
  rw [map_sum]
  simp only [map_smul, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, toDual_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The canonical inverse-Frobenius semilinear map, constructed from the
Cartier pairing. Independence from the basis follows from `unique`. -/
def verschiebung (a : A) : A := basisMap (K := K) p A (Module.finBasis K A) a

/-- Cartier-dual Frobenius characterizes canonical Verschiebung over any
perfect field, with the necessary p-th power on the pairing. -/
theorem pairing (φ : CartierDual K A) (a : A) :
    φ (verschiebung (K := K) p A a) ^ p = (φ ^ p) a :=
  basisMap_pairing (K := K) p A (Module.finBasis K A) φ a

private theorem eq_of_pairing {x y : A}
    (h : ∀ φ : CartierDual K A, φ x ^ p = φ y ^ p) : x = y := by
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff K (x - y)).1 fun ψ => ?_
  rw [map_sub, sub_eq_zero]
  exact (frobenius_inj K p) (h (ofDual K A ψ))

/-- The pairing condition gives uniqueness without choosing a basis. -/
theorem unique (V : A → A)
    (hV : ∀ (φ : CartierDual K A) (a : A), φ (V a) ^ p = (φ ^ p) a) :
    V = verschiebung (K := K) p A := by
  funext a
  apply eq_of_pairing (K := K) p A
  intro φ
  rw [hV, pairing]

@[simp] theorem verschiebung_zero : verschiebung (K := K) p A 0 = 0 := by
  apply eq_of_pairing (K := K) p A
  intro φ
  rw [pairing, map_zero, map_zero, zero_pow (Fact.out : p.Prime).ne_zero]

@[simp] theorem verschiebung_add (a b : A) :
    verschiebung (K := K) p A (a + b) = verschiebung (K := K) p A a + verschiebung (K := K) p A b := by
  apply eq_of_pairing (K := K) p A
  intro φ
  rw [pairing, map_add, map_add, add_pow_char, pairing, pairing]

/-- Canonical Verschiebung is inverse-Frobenius semilinear. -/
theorem verschiebung_smul (c : K) (a : A) :
    verschiebung (K := K) p A (c • a) = (frobeniusEquiv K p).symm c • verschiebung (K := K) p A a := by
  apply eq_of_pairing (K := K) p A
  intro φ
  rw [pairing, map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_pow,
    frobeniusEquiv_symm_pow_p, pairing]

/-- The semilinear form of the constructed map. -/
def semilinear : A →ₛₗ[(frobeniusEquiv K p).symm.toRingHom] A where
  toFun := verschiebung (K := K) p A
  map_add' := verschiebung_add (K := K) p A
  map_smul' := verschiebung_smul (K := K) p A

/-- Frobenius composed with canonical Verschiebung is multiplication by p. -/
theorem verschiebung_pow (a : A) :
    verschiebung (K := K) p A a ^ p = PDivisibleGroup.Hopf.nsmulAlgHom K A p a := by
  letI := coord_charP (K := K) p A
  rw [verschiebung, basisMap, sum_pow_char]
  simp only [smul_pow, frobeniusEquiv_symm_pow_p]
  exact (PDivisibleGroup.Hopf.nsmulAlgHom_eq_sum_pow_apply_smul_pow
    (Module.finBasis K A) a).symm

private theorem dual_pow_one (φ : CartierDual K A) (n : ℕ) :
    (φ ^ n) 1 = (φ 1) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, one_apply, Bialgebra.counit_one]
  | succ n ih =>
    rw [pow_succ, pow_succ, mul_apply, Bialgebra.comul_one,
      Algebra.TensorProduct.one_def, TensorProduct.dualDistrib_apply,
      toDual_apply, toDual_apply, ih]

@[simp] theorem verschiebung_one : verschiebung (K := K) p A 1 = 1 := by
  apply eq_of_pairing (K := K) p A
  intro φ
  rw [pairing, dual_pow_one]

private theorem tensor_pairing (x y : A)
    (w : CartierDual K A ⊗[K] CartierDual K A) :
    (TensorProduct.dualDistrib K A A
      (TensorProduct.map (toDual K A).toLinearMap (toDual K A).toLinearMap w)
      (verschiebung (K := K) p A x ⊗ₜ[K] verschiebung (K := K) p A y)) ^ p =
    TensorProduct.dualDistrib K A A
      (TensorProduct.map (toDual K A).toLinearMap (toDual K A).toLinearMap (w ^ p))
      (x ⊗ₜ[K] y) := by
  letI := dual_charP (K := K) p A
  letI : Nontrivial (CartierDual K A) := dual_nontrivial (K := K) A
  letI : Nontrivial (CartierDual K A ⊗[K] CartierDual K A) :=
    (Algebra.TensorProduct.lmul' (S := CartierDual K A) K).toRingHom.domain_nontrivial
  letI : CharP (CartierDual K A ⊗[K] CartierDual K A) p :=
    charP_of_injective_algebraMap (algebraMap K _).injective p
  induction w using TensorProduct.induction_on with
  | zero => simp [zero_pow (Fact.out : p.Prime).ne_zero]
  | tmul φ ψ =>
    rw [Algebra.TensorProduct.tmul_pow, TensorProduct.map_tmul,
      TensorProduct.map_tmul, TensorProduct.dualDistrib_apply,
      TensorProduct.dualDistrib_apply, mul_pow]
    exact congrArg₂ (· * ·) (pairing (K := K) p A φ x) (pairing (K := K) p A ψ y)
  | add w₁ w₂ h₁ h₂ =>
    simp only [map_add, LinearMap.add_apply, add_pow_char, h₁, h₂]

@[simp] theorem verschiebung_mul (x y : A) :
    verschiebung (K := K) p A (x * y) = verschiebung (K := K) p A x * verschiebung (K := K) p A y := by
  letI := dual_charP (K := K) p A
  apply eq_of_pairing (K := K) p A
  intro φ
  rw [pairing, ← comul_pairing (φ ^ p) x y,
    ← comul_pairing φ (verschiebung (K := K) p A x) (verschiebung (K := K) p A y), tensor_pairing]
  rw [show Coalgebra.comul (R := K) (φ ^ p) = (Coalgebra.comul (R := K) φ) ^ p from
    map_pow (Bialgebra.comulAlgHom K (CartierDual K A)) φ p]

/-- Canonical Verschiebung as a ring homomorphism. Its scalar behavior is
recorded by `ringHom_algebraMap` rather than K-linearity. -/
def ringHom : A →+* A where
  toFun := verschiebung (K := K) p A
  map_zero' := verschiebung_zero (K := K) p A
  map_add' := verschiebung_add (K := K) p A
  map_one' := verschiebung_one (K := K) p A
  map_mul' := verschiebung_mul (K := K) p A

@[simp] theorem ringHom_apply (a : A) : ringHom (K := K) p A a = verschiebung (K := K) p A a := rfl

theorem ringHom_algebraMap (c : K) :
    ringHom (K := K) p A (algebraMap K A c) =
      algebraMap K A ((frobeniusEquiv K p).symm c) := by
  change verschiebung (K := K) p A _ = _
  rw [Algebra.algebraMap_eq_smul_one, verschiebung_smul, verschiebung_one,
    ← Algebra.algebraMap_eq_smul_one]

/-- Canonical Verschiebung also composed in the reverse order gives [p]. -/
theorem verschiebung_pow_arg (a : A) :
    verschiebung (K := K) p A (a ^ p) = PDivisibleGroup.Hopf.nsmulAlgHom K A p a := by
  change ringHom (K := K) p A (a ^ p) = _
  rw [map_pow, ringHom_apply, verschiebung_pow]

/-- Compatibility with the identity section, retaining the scalar twist. -/
theorem counit_verschiebung (a : A) :
    Coalgebra.counit (R := K) (verschiebung (K := K) p A a) =
      (frobeniusEquiv K p).symm (Coalgebra.counit (R := K) a) := by
  apply (frobenius_inj K p)
  change (_ : K) ^ p = (_ : K) ^ p
  rw [frobeniusEquiv_symm_pow_p]
  simpa only [one_apply, one_pow] using pairing (K := K) p A (1 : CartierDual K A) a

private theorem pairing_map_semilinear (φ ψ : CartierDual K A) (w : A ⊗[K] A) :
    (TensorProduct.dualDistrib K A A (toDual K A φ ⊗ₜ[K] toDual K A ψ)
      (TensorProduct.map (semilinear (K := K) p A) (semilinear (K := K) p A) w)) ^ p =
    TensorProduct.dualDistrib K A A (toDual K A (φ ^ p) ⊗ₜ[K] toDual K A (ψ ^ p)) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp [zero_pow (Fact.out : p.Prime).ne_zero]
  | tmul x y =>
    rw [TensorProduct.map_tmul, TensorProduct.dualDistrib_apply,
      TensorProduct.dualDistrib_apply, mul_pow]
    exact congrArg₂ (· * ·) (pairing (K := K) p A φ x) (pairing (K := K) p A ψ y)
  | add x y hx hy =>
    simp only [map_add, add_pow_char, hx, hy]

/-- The constructed inverse-semilinear map respects comultiplication.
Thus it is the actual Cartier-dual Frobenius on the finite group scheme. -/
theorem comul_verschiebung (a : A) :
    Coalgebra.comul (R := K) (verschiebung (K := K) p A a) =
      TensorProduct.map (semilinear (K := K) p A) (semilinear (K := K) p A)
        (Coalgebra.comul (R := K) a) := by
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff K _).1 fun θ => ?_
  obtain ⟨z, rfl⟩ := (TensorProduct.dualDistribEquiv K A A).surjective θ
  rw [map_sub, sub_eq_zero]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul φ ψ =>
    apply (frobenius_inj K p)
    change (_ : K) ^ p = (_ : K) ^ p
    change (TensorProduct.dualDistrib K A A (φ ⊗ₜ[K] ψ)
      (Coalgebra.comul (R := K) (verschiebung (K := K) p A a))) ^ p =
      (TensorProduct.dualDistrib K A A (φ ⊗ₜ[K] ψ)
        (TensorProduct.map (semilinear (K := K) p A) (semilinear (K := K) p A)
          (Coalgebra.comul (R := K) a))) ^ p
    have hm := pairing_map_semilinear (K := K) p A (ofDual K A φ)
      (ofDual K A ψ) (Coalgebra.comul (R := K) a)
    simp only [toDual_ofDual] at hm
    rw [hm]
    have hp := pairing (K := K) p A (ofDual K A φ * ofDual K A ψ) a
    simpa only [mul_pow, mul_apply, toDual_ofDual] using hp
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, hx, hy]

variable {A}
variable {B : Type w} [CommRing B] [HopfAlgebra K B]
  [Coalgebra.IsCocomm K B] [Module.Finite K B]

/-- Every finite commutative group morphism respects canonical Verschiebung.
No ambient elliptic or abelian morphism is assumed. -/
theorem naturality (f : A →ₐc[K] B) (a : A) :
    f (verschiebung (K := K) p A a) = verschiebung (K := K) p B (f a) := by
  apply eq_of_pairing (K := K) p B
  intro φ
  change (CartierDual.map f φ) (verschiebung (K := K) p A a) ^ p = _
  rw [pairing, pairing, ← map_pow (CartierDual.map f)]
  rfl

end SupersingularCurves.Geometry.PerfectHopfVerschiebung
