import SupersingularCurves.IKO.HypergeometricEquations

open Polynomial SupersingularCurves.IKO
open scoped Classical
noncomputable section

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

-- The characteristic-three boundary: h is constant and has no geometric roots.
example : (hPolynomial 3 : (ZMod 3)[X]).Separable :=
  hPolynomial_separable 3 (by decide)

example : (hPolynomial 3 : (AlgebraicClosure (ZMod 3))[X]).roots.toFinset.card = 0 := by
  classical
  simpa using card_roots_hPolynomial (K := AlgebraicClosure (ZMod 3)) 3 (by decide)

-- A concrete simple root, checked by evaluating both polynomial and derivative.
example : (gPolynomial 5 : (ZMod 5)[X]).eval 4 = 0 ∧
    (derivative (gPolynomial 5 : (ZMod 5)[X])).eval 4 = 2 := by
  rw [gPolynomial_five]
  norm_num [derivative_add, derivative_mul]
  decide

-- Distinct geometric roots, including primes in both congruence classes.
example : (gPolynomial 7 : (AlgebraicClosure (ZMod 7))[X]).roots.toFinset.card = 2 := by
  classical
  simpa using card_roots_gPolynomial (K := AlgebraicClosure (ZMod 7)) 7 (by decide)

example : (gPolynomial 11 : (AlgebraicClosure (ZMod 11))[X]).roots.toFinset.card = 3 := by
  classical
  simpa using card_roots_gPolynomial (K := AlgebraicClosure (ZMod 11)) 11 (by decide)

example : (hPolynomial 5 : (AlgebraicClosure (ZMod 5))[X]).roots.toFinset.card = 1 := by
  classical
  simpa using card_roots_hPolynomial (K := AlgebraicClosure (ZMod 5)) 5 (by decide)

example : (hPolynomial 7 : (AlgebraicClosure (ZMod 7))[X]).roots.toFinset.card = 1 := by
  classical
  simpa using card_roots_hPolynomial (K := AlgebraicClosure (ZMod 7)) 7 (by decide)

-- The strict degree bound in the general ODE theorem is necessary: in
-- characteristic five this degree-five polynomial has a common derivative
-- root at 2, despite having nonzero values at 0 and 1 and solving the ODE.
example : let f : (ZMod 5)[X] := X ^ 5 - C 2
    f.eval 0 ≠ 0 ∧ f.eval 1 ≠ 0 ∧ f.eval 2 = 0 ∧
      derivative f = 0 ∧ hypergeometricOp (K := ZMod 5) 0 0 1 0 f = 0 := by
  have h5 : (5 : ZMod 5) = 0 := by decide
  have h2 : (2 : ZMod 5) ≠ 0 := by decide
  dsimp
  norm_num [hypergeometricOp, derivative_sub, derivative_pow, h5, h2]
  constructor
  · exact h5
  · simp only [h5, map_zero, zero_mul, mul_zero, add_zero]
