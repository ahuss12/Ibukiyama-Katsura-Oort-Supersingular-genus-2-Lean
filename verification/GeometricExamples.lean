import SupersingularCurves.IKO.Jacobians
import SupersingularCurves.IKO.GlobalForms

/- Concrete root and nonroot parameters check the new statements on actual
Picard-representing Jacobians and on global sections of the curve models. -/

open AlgebraicCurve SupersingularCurves.IKO
namespace GeometricExamples
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

abbrev K3 := AlgebraicClosure (ZMod 3)
abbrev K5 := AlgebraicClosure (ZMod 5)

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
private theorem h35 : (3 : K5) ≠ 0 := by simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using lift_ne (p := 5) (a := 3) (b := 0) (by decide)
private theorem h40 : (4 : K5) ≠ 0 := by simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using lift_ne (p := 5) (a := 4) (b := 0) (by decide)
private theorem h41 : (4 : K5) ≠ 1 := by simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using lift_ne (p := 5) (a := 4) (b := 1) (by decide)
private theorem h215 : (2 : K5) ≠ 1 := by simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using lift_ne (p := 5) (a := 2) (b := 1) (by decide)
private theorem h213 : (2 : K3) ≠ 1 := by simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using lift_ne (p := 3) (a := 2) (b := 1) (by decide)

example : Nat.card ((familyAJacobian (4 : K5) h35 h40 h41).jacobian.abelianVariety.torsionPoints 5) = 1 := by
  rw [card_familyAJacobian_torsion 5 (by decide) (4 : K5) h35 h40 h41]
  have hz : (10 : K5) = 0 := by simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using lift_eq (p := 5) (a := 10) (b := 0) (by decide)
  norm_num [gPolynomial_five]
  exact hz

example : Nat.card ((familyAJacobian (2 : K5) h35 (NeZero.ne _) h215).jacobian.abelianVariety.torsionPoints 5) = 25 := by
  rw [card_familyAJacobian_torsion 5 (by decide) (2 : K5) h35 (NeZero.ne _) h215]
  have hz : (6 : K5) ≠ 0 := by simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using lift_ne (p := 5) (a := 6) (b := 0) (by decide)
  norm_num [gPolynomial_five, hz]

example : (familyBJacobian (2 : K3) (NeZero.ne _) h213).jacobian.abelianVariety.IsOrdinaryOver 3 := by
  rw [familyBJacobian_ordinary_iff 3 (by decide) (2 : K3) (NeZero.ne _) h213]
  simp [hPolynomial_three]

example (ω : familyAGlobalForms (4 : K5) h35 h40 h41) :
    familyAGlobalCartier 5 (4 : K5) h35 h40 h41 ω = 0 := by
  apply (familyA_all_globalCartier_zero_iff 5 (by decide) (4 : K5) h35 h40 h41).mpr _ ω
  have hz : (10 : K5) = 0 := by simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using lift_eq (p := 5) (a := 10) (b := 0) (by decide)
  norm_num [gPolynomial_five]
  exact hz

example : ¬ ∀ ω : familyBGlobalForms (2 : K3) (NeZero.ne _) h213,
    familyBGlobalCartier 3 (2 : K3) (NeZero.ne _) h213 ω = 0 := by
  rw [familyB_all_globalCartier_zero_iff 3 (by decide) (2 : K3) (NeZero.ne _) h213]
  simp [hPolynomial_three]

end GeometricExamples
