import SupersingularCurves.IKO.SuperspecialParameters

/- The first two checks exclude geometric superspeciality of actual curves.
The third tests p-rank for an arbitrary representing Jacobian at a root,
without claiming that p-rank zero implies superspeciality. -/

open CategoryTheory AlgebraicGeometry SupersingularCurves.IKO
open SupersingularCurves.Geometry NeronModelInfra GoodReductionJacobian

namespace SuperspecialExamples
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

local instance : NeZero (2 : K3) := ⟨by simpa only [Nat.cast_ofNat, Nat.cast_zero] using lift_ne (p := 3) (a := 2) (b := 0) (by decide)⟩
local instance : NeZero (2 : K5) := ⟨by simpa only [Nat.cast_ofNat, Nat.cast_zero] using lift_ne (p := 5) (a := 2) (b := 0) (by decide)⟩
local instance : NeZero (2 : K7) := ⟨by simpa only [Nat.cast_ofNat, Nat.cast_zero] using lift_ne (p := 7) (a := 2) (b := 0) (by decide)⟩

private theorem h35 : (3 : K5) ≠ 0 := by simpa only [Nat.cast_ofNat, Nat.cast_zero] using lift_ne (p := 5) (a := 3) (b := 0) (by decide)
private theorem h215 : (2 : K5) ≠ 1 := by simpa only [Nat.cast_ofNat, Nat.cast_one] using lift_ne (p := 5) (a := 2) (b := 1) (by decide)
private theorem h40 : (4 : K5) ≠ 0 := by simpa only [Nat.cast_ofNat, Nat.cast_zero] using lift_ne (p := 5) (a := 4) (b := 0) (by decide)
private theorem h41 : (4 : K5) ≠ 1 := by simpa only [Nat.cast_ofNat, Nat.cast_one] using lift_ne (p := 5) (a := 4) (b := 1) (by decide)

example (t : K3) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    ¬ CurveModel.IsSuperspecial 3 (familyBCurve t ht0 ht1) :=
  familyB_not_isSuperspecial_char_three t ht0 ht1

example : ¬ CurveModel.IsSuperspecial 5
    (familyACurve (2 : K5) h35 (NeZero.ne _) h215) := by
  apply familyA_not_isSuperspecial_of_nonroot 5 (by decide) _ h35 (NeZero.ne _) h215
  have hz : (6 : K5) ≠ 0 := by
    simpa only [Nat.cast_ofNat, Nat.cast_zero] using lift_ne (p := 5) (a := 6) (b := 0) (by decide)
  norm_num [gPolynomial_five, hz]

example {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K5)))
      (familyACurve (4 : K5) h35 h40 h41).toBase}
    (J : Jacobian (familyACurve (4 : K5) h35 h40 h41) s) :
    J.abelianVariety.HasPRankOver 5 0 := by
  rw [familyA_anyJacobian_pRank_zero_iff 5 (by decide) _ h35 h40 h41 J]
  have hz : (10 : K5) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (algebraMap (ZMod 5) K5) (show (10 : ZMod 5) = 0 by decide)
  norm_num [gPolynomial_five]
  exact hz

example : (familyASuperspecialParameters (K := K7) 7).ncard ≤ 2 ∧
    (familyBSuperspecialParameters (K := K7) 7).ncard ≤ 1 :=
  ⟨ncard_familyASuperspecialParameters_le 7 (by decide),
    ncard_familyBSuperspecialParameters_le 7 (by decide)⟩

end SuperspecialExamples
