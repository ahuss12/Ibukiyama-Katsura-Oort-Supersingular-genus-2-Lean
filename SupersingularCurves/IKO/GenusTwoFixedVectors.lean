/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.IKO.FixedVectors

/-!
# General genus-two Cartier fixed vectors

Over an algebraically closed field, a two-dimensional inverse-Frobenius
operator has no nonzero fixed vector exactly when its square vanishes.
This is an elementary polynomial argument, with the IKO convention
`C(v) = Frobenius⁻¹(Mv)` and twisted square `M^(p) M`.
-/

set_option autoImplicit false
noncomputable section
namespace SupersingularCurves.IKO
open Polynomial Matrix
variable {K : Type*} [Field K] [IsAlgClosed K]

private theorem polynomial_eq_monomial_of_only_zero_root
    (f : K[X]) (h : ∀ x : K, f.eval x = 0 → x = 0) :
    f = C f.leadingCoeff * X ^ f.natDegree := by
  conv_lhs => rw [(IsAlgClosed.splits f).eq_prod_roots]
  congr 1
  calc
    (f.roots.map (fun x => X - C x)).prod =
        (f.roots.map (fun _ => (X : K[X]))).prod := by
      congr 1
      apply Multiset.map_congr rfl
      intro x hx
      rw [h x ((mem_roots (by
        intro hf
        simp [hf] at hx)).mp hx), C_0, sub_zero]
    _ = X ^ f.roots.card := by simp
    _ = X ^ f.natDegree := by rw [IsAlgClosed.card_roots_eq_natDegree]

private theorem exists_nonzero_scalar_fixed (p : ℕ) (hp : 1 < p)
    (a : K) (ha : a ≠ 0) : ∃ z : K, z ≠ 0 ∧ z ^ p = a * z := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq a (n := p - 1) (by omega)
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    simp only [zero_pow (show p - 1 ≠ 0 by omega)] at hz
    exact ha hz.symm
  refine ⟨z, hz0, ?_⟩
  calc
    z ^ p = z ^ (p - 1) * z := by rw [← pow_succ]; congr 1; omega
    _ = a * z := by rw [hz]

variable (p : ℕ) [Fact p.Prime] [CharP K p]

private theorem twisted_square_zero_of_fixed_trivial
    (a b c d : K)
    (hfix : ∀ x y : K, a * x + b * y = x ^ p → c * x + d * y = y ^ p →
      x = 0 ∧ y = 0) :
    (!![a, b; c, d]).map (fun x => x ^ p) * !![a, b; c, d] = 0 := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hp0 : p ≠ 0 := by omega
  by_cases hb : b = 0
  · subst b
    have hd : d = 0 := by
      by_contra hd
      obtain ⟨y, hy, hye⟩ := exists_nonzero_scalar_fixed p hp d hd
      exact hy (hfix 0 y (by simp [hp0]) (by simpa using hye.symm)).2
    subst d
    have ha : a = 0 := by
      by_contra ha
      obtain ⟨x, hx, hxe⟩ := exists_nonzero_scalar_fixed p hp a ha
      obtain ⟨y, hye⟩ := IsAlgClosed.exists_pow_nat_eq (c * x) (n := p) (by omega)
      exact hx (hfix x y (by simpa using hxe.symm) (by simpa using hye.symm)).1
    subst a
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hp0]
  · let A := a ^ p + d * b ^ p / b
    let B := (a * d - b * c) * b ^ p / b
    let f : K[X] := X ^ (p * p) - C A * X ^ p + C B * X
    have hdeg : f.natDegree = p * p := by
      have hpp : p < p * p := by nlinarith
      dsimp [f]
      compute_degree! <;> (try simp [ne_of_gt hpp, hp.ne']) <;> omega
    have hlc : f.leadingCoeff = 1 := by
      rw [← coeff_natDegree, hdeg]
      simp [f, coeff_X_pow, coeff_X, (show p * p ≠ p by nlinarith),
        (show 1 ≠ p * p by nlinarith)]
    have hroot : ∀ x : K, f.eval x = 0 → x = 0 := by
      intro x hx
      let y := (x ^ p - a * x) / b
      have he : x ^ (p * p) - A * x ^ p + B * x = 0 := by
        simpa [f] using hx
      have hfirst : a * x + b * y = x ^ p := by
        dsimp [y]
        field_simp
        ring
      have hsecond : c * x + d * y = y ^ p := by
        dsimp [y]
        rw [div_pow, sub_pow_char, mul_pow, ← pow_mul]
        apply (eq_div_iff (pow_ne_zero p hb)).mpr
        dsimp [A, B] at he
        field_simp at he ⊢
        linear_combination -he
      exact (hfix x y hfirst hsecond).1
    have heq : f = X ^ (p * p) := by
      rw [polynomial_eq_monomial_of_only_zero_root f hroot,
        hlc, C_1, one_mul, hdeg]
    have hA : A = 0 := by
      have h := congrArg (fun q : K[X] => q.coeff p) heq
      simpa [f, coeff_X_pow, coeff_X, (show p ≠ p * p by nlinarith),
        (show 1 ≠ p by omega)] using h
    have hB : B = 0 := by
      have h := congrArg (fun q : K[X] => q.coeff 1) heq
      simpa [f, coeff_X_pow, coeff_X, (show 1 ≠ p by omega),
        (show 1 ≠ p * p by nlinarith)] using h
    have hdet : a * d - b * c = 0 := by
      dsimp [B] at hB
      exact (mul_eq_zero.mp (((div_eq_zero_iff).mp hB).resolve_right hb)).resolve_right
        (pow_ne_zero p hb)
    have ha : a ^ p = -(d * b ^ p / b) := by
      dsimp [A] at hA
      exact eq_neg_of_add_eq_zero_left hA
    have hc : c = a * d / b := by
      apply (eq_div_iff hb).mpr
      linear_combination -hdet
    rw [hc]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, div_pow, mul_pow, ha] <;>
      field_simp <;> ring

/-- Every fixed vector vanishes exactly when the inverse-Frobenius operator
has square zero. This statement holds for every two-by-two matrix. -/
theorem semilinear_fixed_trivial_iff_twisted_square_zero
    (M : Matrix (Fin 2) (Fin 2) K) :
    (∀ v : Fin 2 → K, semilinearAction (frobeniusEquiv K p) M v = v → v = 0) ↔
      M.map (fun c => c ^ p) * M = 0 := by
  constructor
  · intro h
    have hM : M = !![M 0 0, M 0 1; M 1 0, M 1 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [hM]
    apply twisted_square_zero_of_fixed_trivial p
    intro x y hx hy
    have hv : semilinearAction (frobeniusEquiv K p) M ![x, y] = ![x, y] := by
      apply (mem_fixedVectors_iff p M ![x, y]).mpr
      intro i
      fin_cases i
      · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hx
      · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hy
    exact ⟨congrFun (h _ hv) 0, congrFun (h _ hv) 1⟩
  · intro h v hv
    have hC := (semilinearAction_square_zero_iff (frobeniusEquiv K p) M).mpr h
    have hz := hC v
    rwa [hv, hv] at hz

/-- The same criterion for the actual additive subgroup of Cartier-fixed vectors. -/
theorem fixedVectors_trivial_iff_twisted_square_zero
    (M : Matrix (Fin 2) (Fin 2) K) :
    (∀ v : fixedVectors p M, v = 0) ↔ M.map (fun c => c ^ p) * M = 0 := by
  rw [← semilinear_fixed_trivial_iff_twisted_square_zero p M]
  constructor
  · intro h v hv
    exact congrArg Subtype.val (h ⟨v, hv⟩)
  · intro h v
    exact Subtype.ext (h v.val v.property)

end SupersingularCurves.IKO
