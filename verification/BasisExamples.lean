import SupersingularCurves.IKO.RegularBasis

open AlgebraicCurve SupersingularCurves.IKO SupersingularCurves.Differentials

namespace BasisExamples
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

abbrev K5 := AlgebraicClosure (ZMod 5)
abbrev K3 := AlgebraicClosure (ZMod 3)

private theorem five_ne {a b : ZMod 5} (h : a ≠ b) :
    algebraMap (ZMod 5) K5 a ≠ algebraMap (ZMod 5) K5 b :=
  (algebraMap (ZMod 5) K5).injective.ne h
private theorem three_ne {a b : ZMod 3} (h : a ≠ b) :
    algebraMap (ZMod 3) K3 a ≠ algebraMap (ZMod 3) K3 b :=
  (algebraMap (ZMod 3) K3).injective.ne h

local instance : NeZero (2 : K5) := ⟨by simpa only [map_ofNat, map_zero, map_one] using five_ne (a := 2) (b := 0) (by decide)⟩
local instance : NeZero (2 : K3) := ⟨by simpa only [map_ofNat, map_zero, map_one] using three_ne (a := 2) (b := 0) (by decide)⟩
private theorem h3 : (3 : K5) ≠ 0 := by
  simpa only [map_ofNat, map_zero, map_one] using five_ne (a := 3) (b := 0) (by decide)
private theorem h40 : (4 : K5) ≠ 0 := by
  simpa only [map_ofNat, map_zero, map_one] using five_ne (a := 4) (b := 0) (by decide)
private theorem h41 : (4 : K5) ≠ 1 := by
  simpa only [map_ofNat, map_zero, map_one] using five_ne (a := 4) (b := 1) (by decide)
private theorem h20 : (2 : K3) ≠ 0 := NeZero.ne _
private theorem h21 : (2 : K3) ≠ 1 := by
  simpa only [map_ofNat, map_zero, map_one] using three_ne (a := 2) (b := 1) (by decide)

/-- Unlike checkpoint 4, this example quantifies over every regular form. -/
example (ω : regularDifferentials K5 (familyAModel (4 : K5) h3 h41).FunctionField) :
    regularCartier 5 (familyAModel (4 : K5) h3 h41).x ω = 0 := by
  apply (familyA_all_regularCartier_zero_iff 5 (by decide) (4 : K5) h3 h40 h41).mpr _ ω
  have hz : (10 : K5) = 0 := by
    simpa only [map_ofNat, map_zero, map_one] using congrArg (algebraMap (ZMod 5) K5) (show (10 : ZMod 5) = 0 by decide)
  norm_num [gPolynomial_five]
  exact hz

example : ¬ (∀ ω : regularDifferentials K3 (familyBModel (2 : K3) h20).FunctionField,
    regularCartier 3 (familyBModel (2 : K3) h20).x ω = 0) := by
  rw [familyB_all_regularCartier_zero_iff 3 (by decide) (2 : K3) h20 h21]
  simp [hPolynomial_three]

example : genusFF K5 (familyAModel (4 : K5) h3 h41).FunctionField = 2 :=
  familyA_genus (4 : K5) h3 h40 h41

example : Function.Bijective (familyBRegularCoordinates (2 : K3) (NeZero.ne _) h20 h21) :=
  familyBRegularCoordinates_bijective (2 : K3) h20 h21

end BasisExamples
