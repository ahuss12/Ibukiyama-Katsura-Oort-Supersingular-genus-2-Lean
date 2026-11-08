import SupersingularCurves.IKO.TorsionCriteria

/- Concrete admissible parameters over algebraic closures test all four
matrix-congruence cases and both cardinality branches. The conclusions
refer to actual divisor-class torsion of the constructed fields. -/

open AlgebraicCurve SupersingularCurves.IKO
namespace TorsionExamples
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

abbrev K3 := AlgebraicClosure (ZMod 3)
abbrev K5 := AlgebraicClosure (ZMod 5)
abbrev K7 := AlgebraicClosure (ZMod 7)

private theorem lift_ne {p : ℕ} [Fact p.Prime] {a b : ℕ}
    (h : (a : ZMod p) ≠ (b : ZMod p)) :
    (a : AlgebraicClosure (ZMod p)) ≠ (b : AlgebraicClosure (ZMod p)) := by
  simpa only [map_natCast] using
    (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).injective.ne h

private theorem lift_eq {p : ℕ} [Fact p.Prime] {a b : ℕ}
    (h : (a : ZMod p) = (b : ZMod p)) :
    (a : AlgebraicClosure (ZMod p)) = (b : AlgebraicClosure (ZMod p)) := by
  simpa only [map_natCast] using
    congrArg (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) h

local instance : NeZero (2 : K3) := ⟨by simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using lift_ne (p := 3) (a := 2) (b := 0) (by decide)⟩
local instance : NeZero (2 : K5) := ⟨by simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using lift_ne (p := 5) (a := 2) (b := 0) (by decide)⟩
local instance : NeZero (2 : K7) := ⟨by simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using lift_ne (p := 7) (a := 2) (b := 0) (by decide)⟩
private theorem h35 : (3 : K5) ≠ 0 := by simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using lift_ne (p := 5) (a := 3) (b := 0) (by decide)
private theorem h37 : (3 : K7) ≠ 0 := by simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using lift_ne (p := 7) (a := 3) (b := 0) (by decide)
private theorem h40 : (4 : K5) ≠ 0 := by simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using lift_ne (p := 5) (a := 4) (b := 0) (by decide)
private theorem h41 : (4 : K5) ≠ 1 := by simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using lift_ne (p := 5) (a := 4) (b := 1) (by decide)
private theorem h215 : (2 : K5) ≠ 1 := by simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using lift_ne (p := 5) (a := 2) (b := 1) (by decide)
private theorem h217 : (2 : K7) ≠ 1 := by simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using lift_ne (p := 7) (a := 2) (b := 1) (by decide)
private theorem h213 : (2 : K3) ≠ 1 := by simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using lift_ne (p := 3) (a := 2) (b := 1) (by decide)

example : Nat.card (Pic0.torsion K5 (familyAModel (4 : K5) h35 h41).FunctionField 5) = 1 := by
  rw [card_familyA_torsion 5 (by decide) (4 : K5) h35 h40 h41]
  have hz : (10 : K5) = 0 := by simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using lift_eq (p := 5) (a := 10) (b := 0) (by decide)
  norm_num [gPolynomial_five]
  exact hz

example : Nat.card (Pic0.torsion K5 (familyAModel (2 : K5) h35 h215).FunctionField 5) = 25 := by
  rw [card_familyA_torsion 5 (by decide) (2 : K5) h35 (NeZero.ne _) h215]
  have hz : (6 : K5) ≠ 0 := by simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using lift_ne (p := 5) (a := 6) (b := 0) (by decide)
  norm_num [gPolynomial_five, hz]

example : Nat.card (Pic0.torsion K7 (familyAModel (2 : K7) h37 h217).FunctionField 7) = 49 := by
  rw [card_familyA_torsion 7 (by decide) (2 : K7) h37 (NeZero.ne _) h217]
  have hz : (33 : K7) ≠ 0 := by simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using lift_ne (p := 7) (a := 33) (b := 0) (by decide)
  norm_num [gPolynomial_seven, hz]

example : Nat.card (Pic0.torsion K5 (familyBModel (4 : K5) h40).FunctionField 5) = 1 := by
  rw [card_familyB_torsion 5 (by decide) (4 : K5) h40 h41]
  have hz : (10 : K5) = 0 := by simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using lift_eq (p := 5) (a := 10) (b := 0) (by decide)
  norm_num [hPolynomial_five]
  exact hz

example : Nat.card (Pic0.torsion K3 (familyBModel (2 : K3) (NeZero.ne _)).FunctionField 3) = 9 := by
  rw [card_familyB_torsion 3 (by decide) (2 : K3) (NeZero.ne _) h213]
  norm_num [hPolynomial_three]

example (q : Pic0.torsion K5 (familyAModel (4 : K5) h35 h41).FunctionField 5) : q = 0 := by
  apply (familyA_torsion_eq_zero_iff 5 (by decide) (4 : K5) h35 h40 h41).mpr _ q
  have hz : (10 : K5) = 0 := by simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using lift_eq (p := 5) (a := 10) (b := 0) (by decide)
  norm_num [gPolynomial_five]
  exact hz

end TorsionExamples
