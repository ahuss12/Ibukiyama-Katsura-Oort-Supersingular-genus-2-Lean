/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusFiniteFieldDescent
import SupersingularCurves.Geometry.FrobeniusInvariantIdeal

/-! # Descent of the genuine identity to the Frobenius fixed field -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SupersingularCurves.Geometry.FrobeniusFiniteFieldGroupDescent
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GoodReductionJacobian NeronModelInfra SchemeFrobenius PerfectFieldVerschiebung
open FrobeniusDescent

variable {K : Type u} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]

/-- A scheme-valued point invariant under coefficient Frobenius descends to
its actual fixed subfield; no algebraicity of the ambient field is needed. -/
theorem exists_fixedField_point (s : ℕ) {Y : Scheme.{u}}
    (x : Spec (CommRingCat.of K) ⟶ Y)
    (hx : Spec.map (CommRingCat.ofHom (iterateFrobenius K p s)) ≫ x = x) :
    ∃ y : Spec (CommRingCat.of (fixedField K p s)) ⟶ Y,
      Spec.map (CommRingCat.ofHom (algebraMap (fixedField K p s) K)) ≫ y = x := by
  let pt : Y := x.base (IsLocalRing.closedPoint K)
  obtain ⟨_, ⟨U', hU, rfl⟩, hpt, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ pt) isOpen_univ
  let U : Y.Opens := U'
  have hU : IsAffineOpen U := hU
  have hpt : pt ∈ U := hpt
  have hrange : Set.range x.base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨q, rfl⟩
    have : q = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    rw [this]
    exact hpt
  let x' : Spec (CommRingCat.of K) ⟶ U := IsOpenImmersion.lift U.ι x hrange
  have hx' : x' ≫ U.ι = x := IsOpenImmersion.lift_fac _ _ _
  let φ : Γ(Y, U) ⟶ CommRingCat.of K := Spec.preimage (x' ≫ hU.isoSpec.hom)
  have hφ : Spec.map φ = x' ≫ hU.isoSpec.hom := Spec.map_preimage _
  have hfix : ∀ r : Γ(Y, U), φ.hom r ∈ fixedField K p s := by
    intro r
    have h1 : Spec.map (CommRingCat.ofHom (iterateFrobenius K p s)) ≫ x' = x' := by
      rw [← cancel_mono U.ι, Category.assoc, hx', hx]
    have h2 : Spec.map (φ ≫ CommRingCat.ofHom (iterateFrobenius K p s)) =
        Spec.map φ := by
      rw [Spec.map_comp, hφ, reassoc_of% h1]
    have h3 := Spec.map_inj.1 h2
    exact congrArg (fun ψ : Γ(Y, U) ⟶ CommRingCat.of K => ψ.hom r) h3
  let ψ : Γ(Y, U) →+* fixedField K p s :=
    φ.hom.codRestrict (fixedField K p s).toSubring.toSubsemiring hfix
  have hψ : (algebraMap (fixedField K p s) K).comp ψ = φ.hom :=
    RingHom.ext fun _ => rfl
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ hU.isoSpec.inv ≫ U.ι, ?_⟩
  rw [← Spec.map_comp_assoc]
  have : CommRingCat.ofHom ψ ≫
      CommRingCat.ofHom (algebraMap (fixedField K p s) K) = φ := by
    rw [← CommRingCat.ofHom_comp, hψ]
    rfl
  rw [this, hφ, Category.assoc, Iso.hom_inv_id_assoc, hx']

/-- Multiplication by a natural number preserves the actual identity section. -/
theorem one_comp_schemeNsmul {X : Scheme.{u}} {c : X ⟶ Spec (CommRingCat.of K)}
    (L : RelativeGroupLaw K c) (n : ℕ) :
    (L.one (𝟙 _)).1 ≫ L.schemeNsmul n = (L.one (𝟙 _)).1 := by
  have h := L.nsmul_natural c (𝟙 _) (L.one (𝟙 _)).1
    (L.one (𝟙 _)).2 n RelativeGroupLaw.idPoint
  have hh : schemeHomOverComp (L.one (𝟙 _)).1 (L.one (𝟙 _)).2
      RelativeGroupLaw.idPoint = L.one (𝟙 _) := by
    apply Subtype.ext
    exact Category.comp_id _
  rw [hh, L.nsmul_unit] at h
  exact congrArg Subtype.val h

/-- The semilinear Frobenius-square automorphism preserves the actual zero,
with the required Frobenius action on the base. -/
theorem one_comp_automorphism {X : Scheme.{u}} {c : X ⟶ Spec (CommRingCat.of K)}
    (L : RelativeGroupLaw K c) (τ : X ⟶ X)
    (hτ : L.schemeNsmul p ≫ τ = absolute p c ≫ absolute p c) :
    (L.one (𝟙 _)).1 ≫ τ = baseMap p K ≫ baseMap p K ≫ (L.one (𝟙 _)).1 := by
  calc
    _ = ((L.one (𝟙 _)).1 ≫ L.schemeNsmul p) ≫ τ := by
      rw [one_comp_schemeNsmul]
    _ = (L.one (𝟙 _)).1 ≫ (absolute p c ≫ absolute p c) := by
      rw [Category.assoc, hτ]
    _ = (absolute p (𝟙 _) ≫ absolute p (𝟙 _)) ≫ (L.one (𝟙 _)).1 :=
      (absolute_square_natural p (𝟙 _) c (L.one (𝟙 _)).1).symm
    _ = _ := by simp only [absolute, baseMap_eq_absolute, Category.assoc]

/-- The image of the genuine identity in an invariant scheme model is a
point over the actual field with p² elements. -/
theorem exists_descended_one {X Y : Scheme.{u}}
    {c : X ⟶ Spec (CommRingCat.of K)} (L : RelativeGroupLaw K c)
    (τ : X ⟶ X) (d : X ⟶ Y)
    (hτ : L.schemeNsmul p ≫ τ = absolute p c ≫ absolute p c)
    (hd : τ ≫ d = d) :
    ∃ e : Spec (CommRingCat.of (fixedField K p 2)) ⟶ Y,
      Spec.map (CommRingCat.ofHom (algebraMap (fixedField K p 2) K)) ≫ e =
        (L.one (𝟙 _)).1 ≫ d := by
  apply exists_fixedField_point p 2
  have hb : Spec.map (CommRingCat.ofHom (iterateFrobenius K p 2)) =
      baseMap p K ≫ baseMap p K := by
    unfold baseMap
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    ext a
    change a ^ (p ^ 2) = (a ^ p) ^ p
    rw [pow_two, pow_mul]
  rw [hb]
  calc
    _ = ((baseMap p K ≫ baseMap p K) ≫ (L.one (𝟙 _)).1) ≫ d := by
      simp only [Category.assoc]
    _ = ((L.one (𝟙 _)).1 ≫ τ) ≫ d := by
      exact congrArg (fun z => z ≫ d) (by
        simpa only [Category.assoc] using (one_comp_automorphism p L τ hτ).symm)
    _ = _ := by rw [Category.assoc, hd]

end SupersingularCurves.Geometry.FrobeniusFiniteFieldGroupDescent
