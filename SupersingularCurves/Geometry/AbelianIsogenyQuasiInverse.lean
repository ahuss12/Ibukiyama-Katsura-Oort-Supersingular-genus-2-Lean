/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.AbelianProductIsogeny

/-! # Genuine reverse isogenies from an annihilated scheme kernel

Faithfully flat descent constructs an actual morphism, and the group laws
descend by epimorphism cancellation. Both composites are actual multiplication.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
universe u
namespace SupersingularCurves.Geometry.AbelianVariety
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open FrobeniusFactorGroup ScalarFrobeniusTate
open scoped CategoryTheory.MonObj
variable {K : Type u} [Field K] [IsAlgClosed K] {g h : ℕ}

/-- Construct the actual reverse isogeny from a finite flat isogeny whose
scheme-theoretic kernel is annihilated by `n`. -/
theorem exists_quasiInverse_of_kernel_killed
    (A : AbelianVariety K g) (B : AbelianVariety K h)
    (f : A.group ⟶ B.group) (hf : IsIsogeny f) [Flat (underlyingScheme.map f)]
    (n : ℕ) (hn : n ≠ 0)
    (hk : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
      (x : SchemeHomOver t A.group.X.hom),
      pointMap (underlyingScheme.map f) f.hom.hom.w x = (GroupScheme.law B.group).one t →
      (GroupScheme.law A.group).nsmul t n x = (GroupScheme.law A.group).one t) :
    ∃ q : B.group ⟶ A.group,
      f ≫ q = multiplication A n ∧ q ≫ f = multiplication B n ∧ IsIsogeny q := by
  let φ := underlyingScheme.map f
  let m := underlyingScheme.map (multiplication A n)
  letI : IsFinite φ := hf.1
  letI : Surjective φ := hf.2
  have hrel : ∀ {T : Scheme.{u}} (u v : T ⟶ A.group.X.left),
      u ≫ φ = v ≫ φ → u ≫ m = v ≫ m := by
    intro T u v huv
    let t := u ≫ A.group.X.hom
    have hv : v ≫ A.group.X.hom = t := by
      change v ≫ A.group.X.hom = u ≫ A.group.X.hom
      rw [← f.hom.hom.w, ← Category.assoc, ← Category.assoc]
      exact congrArg (fun z => z ≫ B.group.X.hom) huv.symm
    let x : Over.mk t ⟶ A.group.X := Over.homMk u rfl
    let y : Over.mk t ⟶ A.group.X := Over.homMk v hv
    have hxy : x ≫ f.hom.hom = y ≫ f.hom.hom := Over.OverMorphism.ext huv
    have hz : (x * y⁻¹) ≫ f.hom.hom = 1 := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, hxy, mul_inv_cancel]
    have H := hk t (overHomToSchemeHomOver (x * y⁻¹))
      (congrArg overHomToSchemeHomOver hz)
    rw [GroupScheme.nsmul_eq_pow] at H
    have hp : (x * y⁻¹) ^ n = 1 := congrArg schemeHomOverToOverHom H
    rw [mul_pow, inv_pow, mul_inv_eq_one] at hp
    exact congrArg Over.Hom.left ((comp_multiplication A n t x).trans
      (hp.trans (comp_multiplication A n t y).symm))
  let r := EffectiveEpi.desc φ m hrel
  have hfac : φ ≫ r = m := EffectiveEpi.fac φ m hrel
  have hr : r ≫ A.group.X.hom = B.group.X.hom := by
    apply (cancel_epi φ).mp
    rw [← Category.assoc, hfac]
    exact (multiplication A n).hom.hom.w.trans f.hom.hom.w.symm
  let r₀ : B.group.X ⟶ A.group.X := Over.homMk r hr
  have hfac₀ : f.hom.hom ≫ r₀ = (multiplication A n).hom.hom :=
    Over.OverMorphism.ext hfac
  haveI : Epi (f.hom.hom ⊗ₘ f.hom.hom) := by
    haveI : Surjective (f.hom.hom ⊗ₘ f.hom.hom).left := by
      rw [Over.tensorHom_left]
      exact MorphismProperty.pullbackMap (P := @Surjective)
        (inferInstance : Surjective φ) (inferInstance : Surjective φ)
        f.hom.hom.w.symm f.hom.hom.w.symm
    haveI : Flat (f.hom.hom ⊗ₘ f.hom.hom).left := by
      rw [Over.tensorHom_left]
      exact MorphismProperty.pullbackMap (P := @Flat)
        (inferInstance : Flat φ) (inferInstance : Flat φ)
        f.hom.hom.w.symm f.hom.hom.w.symm
    haveI : QuasiCompact (f.hom.hom ⊗ₘ f.hom.hom).left := by
      rw [Over.tensorHom_left]
      exact MorphismProperty.pullbackMap (P := @QuasiCompact)
        (inferInstance : QuasiCompact φ) (inferInstance : QuasiCompact φ)
        f.hom.hom.w.symm f.hom.hom.w.symm
    exact Over.epi_of_epi_left _
  letI : IsMonHom r₀ := {
    one_hom := by
      rw [← IsMonHom.one_hom f.hom.hom, Category.assoc, hfac₀, IsMonHom.one_hom]
    mul_hom := by
      apply (cancel_epi (f.hom.hom ⊗ₘ f.hom.hom)).mp
      rw [← Category.assoc, ← IsMonHom.mul_hom, Category.assoc, hfac₀,
        IsMonHom.mul_hom, ← Category.assoc, tensorHom_comp_tensorHom, hfac₀] }
  let q : B.group ⟶ A.group := Grp.homMk r₀
  have hq : f ≫ q = multiplication A n := by
    apply Grp.hom_ext
    exact hfac₀
  have hqf : q ≫ f = multiplication B n := by
    apply Grp.hom_ext
    apply Over.OverMorphism.ext
    apply (cancel_epi φ).mp
    change φ ≫ (r ≫ φ) = φ ≫ (GroupScheme.law B.group).schemeNsmul n
    rw [← Category.assoc, hfac]
    exact GroupScheme.schemeNsmul_natural f n
  have hqi : IsIsogeny q := by
    haveI : IsProper (r ≫ A.group.X.hom) := hr.symm ▸ B.proper
    haveI : IsProper r := IsProper.of_comp r A.group.X.hom
    haveI : IsFinite (φ ≫ r) := hfac.symm ▸ (multiplication_isIsogeny A n hn).1
    haveI : Surjective (φ ≫ r) := hfac.symm ▸ (multiplication_isIsogeny A n hn).2
    exact ⟨FiniteFlatFactor.isFinite φ r, Surjective.of_comp φ r⟩
  exact ⟨q, hq, hqf, hqi⟩

end SupersingularCurves.Geometry.AbelianVariety
