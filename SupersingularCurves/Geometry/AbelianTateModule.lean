/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.AbelianMultiplicationDegree
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero
import Theorems.Thm_TateModule_finite_free_finrank_eq_of_natCard_torsionBy_pow_eq

/-! # The Tate module of the actual points of an abelian variety -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SupersingularCurves.Geometry.AbelianVariety
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open scoped CategoryTheory.MonObj

variable {K : Type u} [Field K] {g : ℕ} (A : AbelianVariety K g)

/-- Additive notation for the genuine K-points of the scheme group. -/
abbrev AdditivePoints := Additive A.Points

/-- Torsion in the actual additive point group agrees with the scheme group law. -/
theorem mem_torsionBy_iff_schemeTorsion (n : ℕ) (x : A.AdditivePoints) :
    x ∈ Submodule.torsionBy ℤ A.AdditivePoints (n : ℤ) ↔
      (GroupScheme.law A.group).IsTorsionPoint (𝟙 _) n
        (overHomToSchemeHomOver x.toMul) := by
  rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
  change x.toMul ^ n = 1 ↔ _
  rw [RelativeGroupLaw.IsTorsionPoint, GroupScheme.nsmul_eq_pow]
  constructor
  · intro hx
    rw [hx]
    rfl
  · intro hx
    apply Over.OverMorphism.ext
    exact congrArg Subtype.val hx

/-- The actual prime-to-characteristic torsion has cardinal n^(2g). -/
theorem natCard_torsionBy [IsAlgClosed K] (n : ℕ) (hn : (n : K) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ A.AdditivePoints (n : ℤ)) = n ^ (2 * g) := by
  let e : (Submodule.torsionBy ℤ A.AdditivePoints (n : ℤ)) ≃
      {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) A.group.X.hom //
        (GroupScheme.law A.group).IsTorsionPoint (𝟙 _) n x} :=
    { toFun := fun x => ⟨overHomToSchemeHomOver x.1.toMul,
        (A.mem_torsionBy_iff_schemeTorsion n x.1).mp x.2⟩
      invFun := fun x => ⟨Additive.ofMul (schemeHomOverToOverHom x.1), by
        apply (A.mem_torsionBy_iff_schemeTorsion n _).mpr
        change (GroupScheme.law A.group).IsTorsionPoint (𝟙 _) n
          (overHomToSchemeHomOver (schemeHomOverToOverHom x.1))
        simpa only [overHomToSchemeHomOver_schemeHomOverToOverHom] using x.2⟩
      left_inv := fun x => by
        apply Subtype.ext
        exact congrArg Additive.ofMul (schemeHomOverToOverHom_overHomToSchemeHomOver _)
      right_inv := fun x => by
        apply Subtype.ext
        exact overHomToSchemeHomOver_schemeHomOverToOverHom _ }
  rw [Nat.card_congr e]
  exact RelativeGroupLaw.natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero K
    A.group.X.hom (GroupScheme.law A.group) A.groupScheme_law_commutative
    A.abelianSchemePropertyBundle g n hn

end SupersingularCurves.Geometry.AbelianVariety

namespace SupersingularCurves.Geometry.AbelianTate
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open scoped CategoryTheory.MonObj TensorProduct

variable {K : Type} [Field K] {g h : ℕ}

/-- The actual inverse limit of compatible ℓ-power torsion points. -/
abbrev Integral (ℓ : ℕ) (A : AbelianVariety K g) := TateModule ℓ A.AdditivePoints

/-- Scalar extension of that actual inverse limit to Q_ℓ. -/
abbrev Rational (ℓ : ℕ) [Fact ℓ.Prime] (A : AbelianVariety K g) :=
  ModularCurve.RationalTateModule ℓ A.AdditivePoints

/-- The actual Tate module is free of rank 2g, proved from genuine torsion
cardinality of the abelian variety; no representation is supplied. -/
theorem finite_free_finrank [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime]
    (A : AbelianVariety K g) (hℓ : (ℓ : K) ≠ 0) :
    Module.Finite ℤ_[ℓ] (Integral ℓ A) ∧ Module.Free ℤ_[ℓ] (Integral ℓ A) ∧
      Module.finrank ℤ_[ℓ] (Integral ℓ A) = 2 * g ∧
      Module.finrank ℚ_[ℓ] (Rational ℓ A) = 2 * g := by
  apply TateModule.finite_free_finrank_eq_of_natCard_torsionBy_pow_eq
  intro n
  exact A.natCard_torsionBy (ℓ ^ n) (by simpa only [Nat.cast_pow] using pow_ne_zero n hℓ)

/-- Every actual group-scheme morphism induces the actual map of point groups. -/
def pointsMap {A : AbelianVariety K g} {B : AbelianVariety K h} (f : A.group ⟶ B.group) :
    A.AdditivePoints →+ B.AdditivePoints where
  toFun x := Additive.ofMul (x.toMul ≫ f.hom.hom)
  map_zero' := by
    change (1 : A.Points) ≫ f.hom.hom = (1 : B.Points)
    exact MonObj.one_comp _
  map_add' x y := by
    change (x.toMul * y.toMul) ≫ f.hom.hom =
      (x.toMul ≫ f.hom.hom) * (y.toMul ≫ f.hom.hom)
    exact MonObj.mul_comp _ _ _

/-- The functorial map acts at every torsion level by the genuine point map. -/
def integralMap (ℓ : ℕ) [Fact ℓ.Prime]
    {A : AbelianVariety K g} {B : AbelianVariety K h} (f : A.group ⟶ B.group) :
    Integral ℓ A →ₗ[ℤ_[ℓ]] Integral ℓ B where
  toFun x := ⟨fun n => pointsMap f (x.1 n), fun n =>
    ⟨by rw [← map_zsmul, TateModule.torsion, map_zero],
      by rw [← map_zsmul, TateModule.compat]⟩⟩
  map_add' x y := Subtype.ext (funext fun n => (pointsMap f).map_add _ _)
  map_smul' a x := Subtype.ext (funext fun n => (pointsMap f).map_zsmul _ _)

/-- The rational map is scalar extension of the genuine integral Tate map. -/
def rationalMap (ℓ : ℕ) [Fact ℓ.Prime]
    {A : AbelianVariety K g} {B : AbelianVariety K h} (f : A.group ⟶ B.group) :
    Rational ℓ A →ₗ[ℚ_[ℓ]] Rational ℓ B := (integralMap ℓ f).baseChange ℚ_[ℓ]

end SupersingularCurves.Geometry.AbelianTate
