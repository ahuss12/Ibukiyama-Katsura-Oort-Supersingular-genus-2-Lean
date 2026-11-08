/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.PadicLatticeOperators
import SupersingularCurves.Geometry.ScalarFrobeniusTateEndSpan

/-!
# Actual limiting Tate operators from recurring isogeny domains

A recurring geometric domain gives integral endomorphisms by composition
with one fixed reverse isogeny. Their nonzero limit lies in the scalar span
of genuine geometric endomorphisms. Finiteness of the geometric models is
an explicit input; it is not inferred from bounded numerical data alone.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SupersingularCurves.Geometry.ScalarFrobeniusTate
open CategoryTheory AlgebraicGeometry AbelianTate
open scoped TensorProduct
variable {K : Type} [Field K] [IsAlgClosed K] {g h : ℕ}
variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- A finite set of isomorphism classes supplies one domain along a strictly
increasing infinite sequence of indices. -/
theorem exists_recurring_model {C : Type*} [Category C]
    (B : ℕ → C) (s : Finset C)
    (hs : ∀ n, ∃ Y ∈ s, Nonempty (Y ≅ B n)) :
    ∃ Y ∈ s, ∃ a : ℕ → ℕ, StrictMono a ∧ ∀ n, Nonempty (Y ≅ B (a n)) := by
  classical
  choose Y hY e using hs
  let c : ℕ → s := fun n => ⟨Y n, hY n⟩
  obtain ⟨v, hv⟩ := Finite.exists_infinite_fiber c
  let := hv
  let a := Nat.orderEmbeddingOfSet (c ⁻¹' {v})
  refine ⟨v.1, v.2, a, a.strictMono, ?_⟩
  intro n
  have han : c (a n) = v := (Nat.Subtype.ofNat (c ⁻¹' {v}) n).2
  have heq : Y (a n) = v.1 := congrArg Subtype.val han
  exact heq ▸ e (a n)

/-- The compactness step for genuine isogeny domains. One fixed composite
equal to nonzero multiplication provides all integral preimages needed to
keep the limiting operator nonzero. -/
theorem exists_actualEndSpan_operator_of_recurring_lattices
    (A : AbelianVariety K g) (B : AbelianVariety K h) (hℓ : (ℓ : K) ≠ 0)
    (U : Submodule ℤ_[ℓ] (Integral ℓ A))
    (W : Submodule ℚ_[ℓ] (Rational ℓ A))
    (hUW : ∀ w ∈ U, (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] w ∈ W)
    (w : Integral ℓ A) (hwU : w ∈ U)
    (hw : (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] w ≠ 0)
    (f : ℕ → (B.group ⟶ A.group)) (a : ℕ → ℕ) (ha : StrictMono a)
    (f₀ : B.group ⟶ A.group) (q : A.group ⟶ B.group)
    (m : ℕ) (hm : m ≠ 0) (hq : f₀ ≫ q = multiplication B m)
    (hrange : ∀ n, LinearMap.range (integralMap ℓ (f n)) =
      U ⊔ (IsLocalRing.maximalIdeal ℤ_[ℓ] ^ a n) •
        (⊤ : Submodule ℤ_[ℓ] (Integral ℓ A))) :
    ∃ u ∈ actualEndSpan ℓ A, u ≠ 0 ∧ LinearMap.range u ≤ W := by
  classical
  obtain ⟨hfinite, hfree, _, _⟩ := finite_free_finrank ℓ A hℓ
  let := hfinite
  let := hfree
  have hpre : ∀ n, ∃ z : Integral ℓ B, integralMap ℓ (f n) z = w := by
    intro n
    change w ∈ LinearMap.range (integralMap ℓ (f n))
    rw [hrange n]
    exact Submodule.mem_sup_left hwU
  choose z hz using hpre
  let F := fun n => integralMap ℓ (q ≫ f n)
  let y := fun n => integralMap ℓ f₀ (z n)
  apply PadicLattice.exists_nonzero_mem_range_le_of_integral_errors ℓ
    (Module.Free.chooseBasis ℤ_[ℓ] (Integral ℓ A)) (actualEndSpan ℓ A) W
    F a ha ((m : ℚ_[ℓ]) • ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] w))
    (smul_ne_zero (Nat.cast_ne_zero.mpr hm) hw) y
  · intro n
    exact rationalMap_mem_actualEndSpan ℓ A (q ≫ f n)
  · intro n
    have hcalc : F n (y n) = (m : ℤ_[ℓ]) • w := by
      change integralMap ℓ (q ≫ f n) (integralMap ℓ f₀ (z n)) = _
      rw [integralMap_comp, LinearMap.comp_apply]
      have hqz := LinearMap.congr_fun
        ((integralMap_comp ℓ f₀ q).symm.trans
          ((congrArg (integralMap ℓ) hq).trans (integralMap_multiplication ℓ B m))) (z n)
      change integralMap ℓ q (integralMap ℓ f₀ (z n)) = (m : ℤ_[ℓ]) • z n at hqz
      rw [hqz, map_smul, hz n]
    rw [hcalc, TensorProduct.tmul_smul]
    simpa only [map_natCast] using
      (IsScalarTower.algebraMap_smul ℚ_[ℓ] (m : ℤ_[ℓ])
        ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] w)).symm
  · intro n x
    apply PadicLattice.exists_integral_error_of_mem_lattice ℓ U W hUW (a n)
    rw [← hrange n]
    exact ⟨integralMap ℓ q x, rfl⟩

/-- Finitely many actual quotient domains suffice to construct the nonzero
operator. Quotient maps and their actual multiplication factors supply the
reverse isogeny and the prescribed integral images. -/
theorem exists_actualEndSpan_operator_of_finite_quotient_models
    (A : AbelianVariety K g) (hℓ : (ℓ : K) ≠ 0)
    (U : Submodule ℤ_[ℓ] (Integral ℓ A))
    (W : Submodule ℚ_[ℓ] (Rational ℓ A))
    (hUW : ∀ w ∈ U, (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] w ∈ W)
    (w : Integral ℓ A) (hwU : w ∈ U)
    (hw : (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] w ≠ 0)
    (H : ℕ → FiniteSubgroup A) (D : ∀ n, Quotient A (H n))
    (hk : ∀ n, (H n).inclusion ≫ (GroupScheme.law A.group).schemeNsmul (ℓ ^ n) =
      ((H n).inclusion ≫ A.group.X.hom) ≫ ((GroupScheme.law A.group).one (𝟙 _)).1)
    (hrange : ∀ n, LinearMap.range
      (integralMap ℓ ((D n).multiplicationFactor (ℓ ^ n) (hk n))) =
      U ⊔ (IsLocalRing.maximalIdeal ℤ_[ℓ] ^ n) •
        (⊤ : Submodule ℤ_[ℓ] (Integral ℓ A)))
    (s : Finset (AbelianVariety K g))
    (hs : ∀ n, ∃ B ∈ s, Nonempty (B.group ≅ (D n).variety.group)) :
    ∃ u ∈ actualEndSpan ℓ A, u ≠ 0 ∧ LinearMap.range u ≤ W := by
  classical
  obtain ⟨G, hG, a, ha, he⟩ := exists_recurring_model
    (fun n => (D n).variety.group) (s.image AbelianVariety.group) (fun n => by
      obtain ⟨B, hB, e⟩ := hs n
      exact ⟨B.group, Finset.mem_image.mpr ⟨B, hB, rfl⟩, e⟩)
  obtain ⟨B, _, rfl⟩ := Finset.mem_image.mp hG
  let e := fun n => (he n).some
  let f := fun n => (e n).hom ≫ (D (a n)).multiplicationFactor (ℓ ^ a n) (hk (a n))
  let q := (D (a 0)).map ≫ (e 0).inv
  apply exists_actualEndSpan_operator_of_recurring_lattices ℓ A B hℓ U W hUW w hwU hw
    f a ha (f 0) q (ℓ ^ a 0) (pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero)
  · dsimp [f, q]
    rw [Category.assoc, ← Category.assoc
      ((D (a 0)).multiplicationFactor _ _) (D (a 0)).map,
      (D (a 0)).multiplicationFactor_map]
    have hnat : (e 0).hom ≫ multiplication (D (a 0)).variety (ℓ ^ a 0) =
        multiplication B (ℓ ^ a 0) ≫ (e 0).hom := by
      apply Grp.hom_ext
      apply Over.OverMorphism.ext
      exact (GroupScheme.schemeNsmul_natural (e 0).hom (ℓ ^ a 0)).symm
    rw [← Category.assoc, hnat, Category.assoc, (e 0).hom_inv_id, Category.comp_id]
  · intro n
    dsimp [f]
    rw [integralMap_comp, LinearMap.range_comp_of_range_eq_top]
    · exact hrange (a n)
    · exact LinearMap.range_eq_top.mpr (integralEquivOfIso ℓ B (D (a n)).variety (e n)).surjective

end SupersingularCurves.Geometry.ScalarFrobeniusTate
