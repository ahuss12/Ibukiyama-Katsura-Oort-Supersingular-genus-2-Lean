/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Differentials.Regularity
import Theorems.Thm_KaehlerDifferential_D_ne_zero_of_transcendental

/-!
# Quadratic function fields from an actual simple root

The construction generalizes the LegendreField construction in the user's
genus-five checkpoint. A simple root gives Eisenstein irreducibility, so the
quotient is a field. Its coordinate extension is separable in characteristic
different from two; in particular dx is nonzero. No regular-basis or genus
conclusion is included in the input data.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.Hyperelliptic

open Polynomial AlgebraicCurve KaehlerDifferential

variable {K : Type*} [Field K]

structure SimpleRootModel (K : Type*) [Field K] where
  f : K[X]
  root : K
  root_zero : f.eval root = 0
  derivative_ne_zero : f.derivative.eval root ≠ 0

namespace SimpleRootModel

variable (a : SimpleRootModel K)

def equation : K[X][X] := X ^ 2 - C a.f

theorem monic_equation : a.equation.Monic := monic_X_pow_sub_C _ (by decide)

/-- The simple root supplies a genuine Eisenstein prime. -/
theorem irreducible_equation : Irreducible a.equation := by
  have hprime : (Ideal.span {X - C a.root}).IsPrime :=
    (Ideal.span_singleton_prime (prime_X_sub_C a.root).ne_zero).mpr (prime_X_sub_C a.root)
  have hs : ¬ (X - C a.root) ^ 2 ∣ a.f := by
    rintro ⟨q, hq⟩
    apply a.derivative_ne_zero
    rw [hq]
    simp [derivative_mul, derivative_pow]
  have he : a.equation.IsEisensteinAt (Ideal.span {X - C a.root}) := by
    apply a.monic_equation.isEisensteinAt_of_mem_of_notMem hprime.ne_top
    · intro i hi
      have hi' : i < 2 := by simpa [equation] using hi
      by_cases hi0 : i = 0
      · subst i
        have hc : a.equation.coeff 0 = -a.f := by simp [equation]
        rw [hc, Ideal.mem_span_singleton, dvd_neg]
        exact (dvd_iff_isRoot).mpr a.root_zero
      · have hi1 : i = 1 := by omega
        subst i
        simp [equation]
    · simpa [equation, Ideal.span_singleton_pow, Ideal.mem_span_singleton] using hs
  exact he.irreducible hprime a.monic_equation.isPrimitive (by simp [equation])

def polynomial : (RatFunc K)[X] := a.equation.map (algebraMap K[X] (RatFunc K))

instance irreducible_polynomial : Fact (Irreducible a.polynomial) :=
  ⟨a.monic_equation.irreducible_iff_irreducible_map_fraction_map.mp a.irreducible_equation⟩

abbrev FunctionField := AdjoinRoot a.polynomial

def radicand : RatFunc K := algebraMap K[X] (RatFunc K) a.f

theorem polynomial_eq : a.polynomial = X ^ 2 - C a.radicand := by
  simp [polynomial, equation, radicand]

theorem monic_polynomial : a.polynomial.Monic := a.monic_equation.map _

instance finiteDimensional_base : FiniteDimensional (RatFunc K) a.FunctionField :=
  (AdjoinRoot.powerBasis a.monic_polynomial.ne_zero).finite

theorem finrank_functionField : Module.finrank (RatFunc K) a.FunctionField = 2 := by
  have hd : a.polynomial.natDegree = 2 := by rw [a.polynomial_eq, natDegree_X_pow_sub_C]
  simpa only [AdjoinRoot.powerBasis_dim, hd] using
    (AdjoinRoot.powerBasis a.monic_polynomial.ne_zero).finrank

def x : a.FunctionField := algebraMap (RatFunc K) a.FunctionField RatFunc.X
def y : a.FunctionField := AdjoinRoot.root a.polynomial

theorem y_sq : a.y ^ 2 = algebraMap (RatFunc K) a.FunctionField a.radicand := by
  have h : a.polynomial.eval₂ (algebraMap (RatFunc K) a.FunctionField) a.y = 0 := by
    simpa only [y, AdjoinRoot.algebraMap_eq] using AdjoinRoot.eval₂_root a.polynomial
  have he := congrArg (fun q : (RatFunc K)[X] =>
    q.eval₂ (algebraMap (RatFunc K) a.FunctionField) a.y) a.polynomial_eq
  rw [he] at h
  simpa only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] using h

theorem equation_in_functionField : a.y ^ 2 = aeval a.x a.f := by
  rw [a.y_sq]
  have h : (IsScalarTower.toAlgHom K (RatFunc K) a.FunctionField).comp
      (Polynomial.aeval RatFunc.X) = Polynomial.aeval a.x := by
    ext
    simp [x]
  have hmap : Polynomial.aeval (RatFunc.X : RatFunc K) =
      IsScalarTower.toAlgHom K K[X] (RatFunc K) := by
    ext
    simp
  rw [hmap] at h
  exact congrArg (fun φ : K[X] →ₐ[K] a.FunctionField => φ a.f) h

theorem transcendental_x : Transcendental K a.x :=
  (transcendental_algebraMap_iff (algebraMap (RatFunc K) a.FunctionField).injective).mpr
    RatFunc.transcendental_X

theorem x_ne_zero : a.x ≠ 0 := a.transcendental_x.ne_zero

theorem radicand_ne_zero : a.radicand ≠ 0 := by
  intro hz
  have hf : a.f = 0 :=
    (IsFractionRing.injective K[X] (RatFunc K)) (by simpa [radicand] using hz)
  exact a.derivative_ne_zero (by simp [hf])

theorem y_ne_zero : a.y ≠ 0 := by
  intro hy
  have h := a.y_sq
  rw [hy, zero_pow (by decide)] at h
  exact a.radicand_ne_zero ((map_eq_zero (algebraMap (RatFunc K) a.FunctionField)).mp h.symm)

def coordinateEquiv : RatFunc K ≃ₐ[K] IntermediateField.adjoin K {a.x} := by
  let φ : RatFunc K →ₐ[K] a.FunctionField := IsScalarTower.toAlgHom K (RatFunc K) a.FunctionField
  have hm : (⊤ : IntermediateField K (RatFunc K)).map φ =
      IntermediateField.adjoin K {a.x} := by
    rw [← RatFunc.adjoin_X, IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  exact IntermediateField.topEquiv.symm |>.trans
    (((⊤ : IntermediateField K (RatFunc K)).equivMap φ).trans
      (IntermediateField.equivOfEq hm))

theorem coordinateEquiv_compatible :
    (algebraMap (IntermediateField.adjoin K {a.x}) a.FunctionField).comp
        a.coordinateEquiv.toRingEquiv.toRingHom = algebraMap (RatFunc K) a.FunctionField := by
  ext z
  rfl

instance finiteDimensional_coordinate :
    FiniteDimensional (IntermediateField.adjoin K {a.x}) a.FunctionField :=
  Module.Finite.of_equiv_equiv a.coordinateEquiv.toRingEquiv (RingEquiv.refl a.FunctionField)
    a.coordinateEquiv_compatible

instance isCurveOver [PerfectField K] : IsCurveOver K a.FunctionField :=
  isCurveOver_of_transcendental_of_perfectField a.transcendental_x a.finiteDimensional_coordinate

variable [NeZero (2 : K)]

theorem separable_polynomial : a.polynomial.Separable := by
  rw [a.polynomial_eq]
  apply separable_X_pow_sub_C _ _ a.radicand_ne_zero
  simpa only [map_ofNat, Nat.cast_ofNat] using
    (map_ne_zero (algebraMap K (RatFunc K))).mpr (NeZero.ne (2 : K))

instance splittingField : IsSplittingField (RatFunc K) a.FunctionField a.polynomial := by
  constructor
  · have hm : a.polynomial.map (algebraMap (RatFunc K) a.FunctionField) =
        X ^ 2 - C (algebraMap (RatFunc K) a.FunctionField a.radicand) := by
      calc
        _ = (X ^ 2 - C a.radicand).map (algebraMap (RatFunc K) a.FunctionField) :=
          congrArg (Polynomial.map (algebraMap (RatFunc K) a.FunctionField)) a.polynomial_eq
        _ = _ := by simp
    rw [hm]
    have h : (X ^ 2 - C (algebraMap (RatFunc K) a.FunctionField a.radicand) :
        a.FunctionField[X]) = (X - C a.y) * (X + C a.y) := by
      rw [← a.y_sq, map_pow]
      ring
    rw [h]
    exact (Splits.X_sub_C _).mul (Splits.X_add_C _)
  · rw [eq_top_iff, ← AdjoinRoot.adjoinRoot_eq_top]
    apply Algebra.adjoin_mono
    rw [Set.singleton_subset_iff, mem_rootSet_of_ne a.monic_polynomial.ne_zero,
      aeval_def, AdjoinRoot.algebraMap_eq, AdjoinRoot.eval₂_root]

instance separable_base : Algebra.IsSeparable (RatFunc K) a.FunctionField :=
  Algebra.isSeparable_of_separable_splitting_field _ _ a.separable_polynomial

instance separable_coordinate : Algebra.IsSeparable (IntermediateField.adjoin K {a.x})
    a.FunctionField :=
  Algebra.IsSeparable.of_equiv_equiv a.coordinateEquiv.toRingEquiv
    (RingEquiv.refl a.FunctionField) a.coordinateEquiv_compatible

theorem dx_ne_zero : D K a.FunctionField a.x ≠ 0 :=
  D_ne_zero_of_transcendental K a.x a.transcendental_x

end SimpleRootModel
end SupersingularCurves.Hyperelliptic
