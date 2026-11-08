/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusFiniteFieldGroupDescentPoint
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_of_closedImmersionBySections_lfp

/-! # Effective descent of Frobenius-invariant abelian homomorphisms -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SupersingularCurves.Geometry.FrobeniusFiniteFieldHomDescent
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open FrobeniusDescent FrobeniusFiniteFieldGroupDescent

variable {S : Type} [CommRing S] {A B : Scheme.{0}}
variable {f : A ⟶ Spec (CommRingCat.of S)} {g : B ⟶ Spec (CommRingCat.of S)}

/-- The actual multiplication comparison on every test scheme, after changing base. -/
def RespectsMul (LA : RelativeGroupLaw S f) (LB : RelativeGroupLaw S g)
    {S' : Type} [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    (φ : pullback f s ⟶ B) (hφ : φ ≫ g = pullback.snd f s ≫ s) : Prop :=
  ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
    pullback.lift (LA.mul (t' ≫ s) P Q).1 t' (LA.mul (t' ≫ s) P Q).2 ≫ φ =
      (LB.mul (t' ≫ s)
        ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
        ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1

/-- Change the coefficient ring in an actual morphism out of a fibre product. -/
def changeBase {S' S'' : Type} [CommRing S'] [CommRing S'']
    (ψ : S' →+* S'')
    (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
    (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
    (φ : pullback f s ⟶ B) : pullback f s'' ⟶ B :=
  pullback.lift (pullback.fst f s'')
    (pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ))
    (by rw [Category.assoc, hs]; exact pullback.condition) ≫ φ

theorem changeBase_over {S' S'' : Type} [CommRing S'] [CommRing S'']
    (ψ : S' →+* S'')
    (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
    (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
    (φ : pullback f s ⟶ B) (hφ : φ ≫ g = pullback.snd f s ≫ s) :
    changeBase ψ s s'' hs φ ≫ g = pullback.snd f s'' ≫ s'' := by
  rw [changeBase, Category.assoc, hφ, ← Category.assoc, pullback.lift_snd, Category.assoc, hs]

private theorem mul_base_eq {R : Type} [CommRing R] {X T : Scheme.{0}}
    {c : X ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R c)
    {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t')
    (P Q : SchemeHomOver t c) :
    (L.mul t' ⟨P.1, P.2.trans h⟩ ⟨Q.1, Q.2.trans h⟩).1 = (L.mul t P Q).1 := by
  subst t'
  rfl

theorem changeBase_respectsMul (LA : RelativeGroupLaw S f) (LB : RelativeGroupLaw S g)
    {S' S'' : Type} [CommRing S'] [CommRing S'']
    (ψ : S' →+* S'')
    (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
    (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
    (φ : pullback f s ⟶ B) (hφ : φ ≫ g = pullback.snd f s ≫ s)
    (hmul : RespectsMul LA LB s φ hφ) :
    RespectsMul LA LB s'' (changeBase ψ s s'' hs φ)
      (changeBase_over ψ s s'' hs φ hφ) := by
  intro T t P Q
  let a := Spec.map (CommRingCat.ofHom ψ)
  have he : (t ≫ a) ≫ s = t ≫ s'' := by rw [Category.assoc, hs]
  let P' : SchemeHomOver ((t ≫ a) ≫ s) f := ⟨P.1, P.2.trans he.symm⟩
  let Q' : SchemeHomOver ((t ≫ a) ≫ s) f := ⟨Q.1, Q.2.trans he.symm⟩
  have h := hmul T (t ≫ a) P' Q'
  have hp : ∀ (R : SchemeHomOver (t ≫ s'') f),
      pullback.lift R.1 t R.2 ≫
        pullback.lift (pullback.fst f s'') (pullback.snd f s'' ≫ a)
          (by rw [Category.assoc, hs]; exact pullback.condition) =
      pullback.lift R.1 (t ≫ a) (R.2.trans he.symm) := by
    intro R
    apply pullback.hom_ext <;> simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  have hR : ∀ (R : SchemeHomOver (t ≫ s'') f),
      pullback.lift R.1 t R.2 ≫ changeBase ψ s s'' hs φ =
        pullback.lift R.1 (t ≫ a) (R.2.trans he.symm) ≫ φ := by
    intro R
    rw [changeBase, ← Category.assoc]
    exact congrArg (fun z => z ≫ φ) (hp R)
  simp only [hR]
  have hmulA := mul_base_eq LA he.symm P Q
  have hmulB := mul_base_eq LB he.symm
    (⟨pullback.lift P.1 (t ≫ a) (P.2.trans he.symm) ≫ φ, by
      rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]
      exact he⟩ : SchemeHomOver (t ≫ s'') g)
    (⟨pullback.lift Q.1 (t ≫ a) (Q.2.trans he.symm) ≫ φ, by
      rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]
      exact he⟩ : SchemeHomOver (t ≫ s'') g)
  dsimp only [P', Q'] at h
  simpa only [hmulA, hmulB] using h


section FixedField
variable {K : Type} [Field K] (p r : ℕ) [Fact p.Prime] [CharP K p]

/-- The coefficient Frobenius is the identity on the actual fixed subfield. -/
theorem frobenius_fixedBase :
    Spec.map (CommRingCat.ofHom (iterateFrobenius K p r)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (fixedField K p r) K)) =
      Spec.map (CommRingCat.ofHom (algebraMap (fixedField K p r) K)) := by
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext a
  exact a.2

/-- Effective descent of an actual invariant abelian homomorphism. The
conclusion constructs a morphism over the fixed field, with the original
multiplication law and an exact scalar-extension comparison. -/
theorem exists_fixedField_hom
    {A B : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of (fixedField K p r))}
    {g : B ⟶ Spec (CommRingCat.of (fixedField K p r))}
    (LA : RelativeGroupLaw (fixedField K p r) f)
    (LB : RelativeGroupLaw (fixedField K p r) g)
    (hAc : LA.IsCommutative) (hBc : LB.IsCommutative)
    (hA : AbelianSchemePropertyBundle (fixedField K p r) f)
    (hB : AbelianSchemePropertyBundle (fixedField K p r) g)
    (𝓛A : A.Modules) (hA₁ : Scheme.Modules.IsInvertible 𝓛A)
    (hA₂ : Scheme.Modules.ClosedImmersionBySections 𝓛A f)
    (𝓛B : B.Modules) (hB₁ : Scheme.Modules.IsInvertible 𝓛B)
    (hB₂ : Scheme.Modules.ClosedImmersionBySections 𝓛B g)
    (φ : pullback f (Spec.map (CommRingCat.ofHom (algebraMap (fixedField K p r) K))) ⟶ B)
    (hφ : φ ≫ g = pullback.snd f _ ≫
      Spec.map (CommRingCat.ofHom (algebraMap (fixedField K p r) K)))
    (hmul : RespectsMul LA LB _ φ hφ)
    (hfix : changeBase (iterateFrobenius K p r) _ _ (frobenius_fixedBase p r) φ = φ) :
    ∃ φ₀ : pullback f (𝟙 _) ⟶ B,
      ∃ hφ₀ : φ₀ ≫ g = pullback.snd f (𝟙 _) ≫ 𝟙 _,
        RespectsMul LA LB (𝟙 _) φ₀ hφ₀ ∧
        changeBase (algebraMap (fixedField K p r) K) (𝟙 _) _
          (Category.comp_id _) φ₀ = φ := by
  let k := fixedField K p r
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  obtain ⟨H, πH, pt, hnat, honto, hinj, -⟩ :=
    RelativeGroupLaw.exists_homScheme_represents_of_closedImmersionBySections_lfp k f g LA LB hAc hBc
      hA hB 𝓛A hA₁ hA₂ 𝓛B hB₁ hB₂
  let x := pt K b φ hφ
  have hx : Spec.map (CommRingCat.ofHom (iterateFrobenius K p r)) ≫ x.1 = x.1 := by
    have hn := hnat K K (iterateFrobenius K p r) b b (frobenius_fixedBase p r) φ hφ
    change (pt K b (changeBase (iterateFrobenius K p r) b b (frobenius_fixedBase p r) φ) _).1 =
      Spec.map (CommRingCat.ofHom (iterateFrobenius K p r)) ≫ x.1 at hn
    have hh : pt K b (changeBase (iterateFrobenius K p r) b b (frobenius_fixedBase p r) φ)
        (changeBase_over (iterateFrobenius K p r) b b (frobenius_fixedBase p r) φ hφ) = x := by
      exact congrArg (fun z : SchemeHomOver (pullback.snd f b ≫ b) g => pt K b z.1 z.2)
        (show (⟨changeBase (iterateFrobenius K p r) b b (frobenius_fixedBase p r) φ,
            changeBase_over (iterateFrobenius K p r) b b (frobenius_fixedBase p r) φ hφ⟩ :
              SchemeHomOver (pullback.snd f b ≫ b) g) = ⟨φ, hφ⟩ from Subtype.ext hfix)
    exact hn.symm.trans (congrArg Subtype.val hh)
  obtain ⟨x₀, hx₀⟩ := exists_fixedField_point p r x.1 hx
  have hb : Flat b ∧ Surjective b :=
    (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap k K))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  letI : Flat b := hb.1
  letI : Surjective b := hb.2
  have hbase : x₀ ≫ πH = 𝟙 _ := by
    apply (cancel_epi b).mp
    rw [← Category.assoc, hx₀, Category.comp_id]
    exact x.2
  let y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) πH := ⟨x₀, hbase⟩
  obtain ⟨φ₀, hφ₀, hmul₀, hpt₀⟩ := honto k (𝟙 _) y
  refine ⟨φ₀, hφ₀, hmul₀, ?_⟩
  apply hinj K b _ φ (changeBase_over (algebraMap k K) (𝟙 _) b (Category.comp_id b) φ₀ hφ₀)
    hφ (changeBase_respectsMul LA LB (algebraMap k K) (𝟙 _) b (Category.comp_id b) φ₀ hφ₀ hmul₀)
    hmul
  apply Subtype.ext
  calc
    _ = b ≫ (pt k (𝟙 _) φ₀ hφ₀).1 :=
      hnat k K (algebraMap k K) (𝟙 _) b (Category.comp_id b) φ₀ hφ₀
    _ = b ≫ x₀ := by rw [hpt₀]
    _ = x.1 := hx₀
end FixedField

end SupersingularCurves.Geometry.FrobeniusFiniteFieldHomDescent
