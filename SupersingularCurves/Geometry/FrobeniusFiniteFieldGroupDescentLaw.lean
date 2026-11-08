/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusFiniteFieldGroupDescentPoint
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_one_eq_of_abelianSchemePropertyBundle_of_isPullback_of_faithfullyFlat
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_forall_mul_comp_eq_of_isPullback
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_coe_nsmul_eq_comp_schemeNsmul
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_isCommutative
import Theorems.Thm_AlgebraicGeometry_IsProper_descendsAlong_surjective_inf_flat_inf_quasiCompact
import Theorems.Thm_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_of_isPullback_of_flat_of_surjective

/-! # Effective descent of the abelian group law from its genuine identity -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SupersingularCurves.Geometry.FrobeniusFiniteFieldGroupDescent
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GoodReductionJacobian NeronModelInfra SchemeFrobenius PerfectFieldVerschiebung
open FrobeniusDescent

/-- A descended identity identifies the descended law after scalar extension,
in arbitrary universes, by the rigidity of abelian group laws. -/
theorem mul_comp_eq_of_one_comp_eq
    {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
    {X X' : Scheme.{u}} {c : X ⟶ Spec (CommRingCat.of R)}
    {c' : X' ⟶ Spec (CommRingCat.of R')}
    (d : X' ⟶ X) (hd : IsPullback d c' c (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (L : RelativeGroupLaw R c) (L' : RelativeGroupLaw R' c')
    (hA' : AbelianSchemePropertyBundle R' c')
    (hone : (L'.one (𝟙 _)).1 ≫ d =
      Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ (L.one (𝟙 _)).1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (x y : SchemeHomOver t c') :
    (L'.mul t x y).1 ≫ d =
      (L.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
        ⟨x.1 ≫ d, by rw [Category.assoc, hd.w, ← Category.assoc, x.2]⟩
        ⟨y.1 ≫ d, by rw [Category.assoc, hd.w, ← Category.assoc, y.2]⟩).1 := by
  obtain ⟨L₁, hmul, hone₁, -⟩ :=
    RelativeGroupLaw.exists_forall_mul_comp_eq_of_isPullback c c' d hd L
  have hunit : L₁.one (𝟙 _) = L'.one (𝟙 _) := by
    apply Subtype.ext
    apply hd.hom_ext
    · rw [hone₁, hone]
      have hn := congrArg Subtype.val (L.one_natural (𝟙 _)
        (Spec.map (CommRingCat.ofHom (algebraMap R R')))
        (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Category.comp_id _))
      rw [GoodReductionJacobian.schemeHomOverComp_coe] at hn
      rw [hn]
      congr 2
    · rw [(L₁.one _).2, (L'.one _).2]
  have hL : L₁ = L' :=
    RelativeGroupLaw.eq_of_one_eq_of_abelianSchemePropertyBundle hA' L₁ L' hunit
  subst hL
  exact hmul t x y

/-- The equality of identities extends to all test schemes. -/
theorem one_comp_eq
    {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
    {X X' : Scheme.{u}} {c : X ⟶ Spec (CommRingCat.of R)}
    {c' : X' ⟶ Spec (CommRingCat.of R')}
    (d : X' ⟶ X) (L : RelativeGroupLaw R c) (L' : RelativeGroupLaw R' c')
    (hone : (L'.one (𝟙 _)).1 ≫ d =
      Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ (L.one (𝟙 _)).1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) :
    (L'.one t).1 ≫ d =
      (L.one (t ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))).1 := by
  have h' := congrArg Subtype.val (L'.one_natural (𝟙 _) t t (Category.comp_id _))
  have h := congrArg Subtype.val (L.one_natural (𝟙 _) _
    (t ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Category.comp_id _))
  change t ≫ (L'.one (𝟙 _)).1 = (L'.one t).1 at h'
  change (t ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))) ≫
    (L.one (𝟙 _)).1 = (L.one _).1 at h
  rw [← h', Category.assoc, hone, ← Category.assoc, h]

/-- Every multiplication-by-n map descends with the abelian law. -/
theorem schemeNsmul_comp_eq
    {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
    {X X' : Scheme.{u}} {c : X ⟶ Spec (CommRingCat.of R)}
    {c' : X' ⟶ Spec (CommRingCat.of R')}
    (d : X' ⟶ X) (hd : IsPullback d c' c (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (L : RelativeGroupLaw R c) (L' : RelativeGroupLaw R' c')
    (hA' : AbelianSchemePropertyBundle R' c')
    (hone : (L'.one (𝟙 _)).1 ≫ d =
      Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ (L.one (𝟙 _)).1)
    (n : ℕ) : L'.schemeNsmul n ≫ d = d ≫ L.schemeNsmul n := by
  have hn : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R'))
      (x : SchemeHomOver t c') (n : ℕ),
      (L'.nsmul t n x).1 ≫ d =
        (L.nsmul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))) n
          ⟨x.1 ≫ d, by rw [Category.assoc, hd.w, ← Category.assoc, x.2]⟩).1 := by
    intro T t x n
    induction n with
    | zero => exact one_comp_eq d L L' hone t
    | succ n ih =>
      simp only [RelativeGroupLaw.nsmul_succ]
      rw [mul_comp_eq_of_one_comp_eq d hd L L' hA' hone]
      congr 2
      exact Subtype.ext ih
  have h := hn c' RelativeGroupLaw.idPoint n
  rw [L.coe_nsmul_eq_comp_schemeNsmul] at h
  simpa only [RelativeGroupLaw.schemeNsmul, RelativeGroupLaw.idPoint, Category.id_comp] using h

variable {K : Type u} [Field K] [IsAlgClosed K] {g : ℕ}
variable (p : ℕ) [Fact p.Prime] [CharP K p] (A : AbelianVariety K g)

/-- The actual abelian-variety properties descend through any field pullback. -/
theorem descended_properties {k : Type u} [Field k] [Algebra k K]
    {X₀ : Scheme.{u}} (c₀ : X₀ ⟶ Spec (CommRingCat.of k))
    (d : A.group.X.left ⟶ X₀)
    (hd : IsPullback d A.group.X.hom c₀
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    SmoothOfRelativeDimension g c₀ ∧ IsProper c₀ ∧ GeometricallyConnected c₀ := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hb : Surjective b :=
    ((flat_and_surjective_SpecMap_iff
      (CommRingCat.ofHom (algebraMap k K))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)).2
  have : Flat b := by infer_instance
  have : QuasiCompact b := by infer_instance
  refine ⟨SmoothOfRelativeDimension.of_isPullback_of_flat_of_surjective g hd.flip, ?_, ?_⟩
  · letI := IsProper.descendsAlong_surjective_inf_flat_inf_quasiCompact
    exact MorphismProperty.of_isPullback_of_descendsAlong hd.flip
      (show ((@Surjective ⊓ @Flat ⊓ @QuasiCompact) : MorphismProperty Scheme.{u}) b from
        ⟨⟨hb, inferInstance⟩, inferInstance⟩) A.proper
  · letI := GeometricallyConnected.descendsAlong_surjective
    exact MorphismProperty.of_isPullback_of_descendsAlong hd.flip hb A.connected

/-- An invariant scheme model automatically acquires the genuine descended
abelian law and its zero section; neither is supplied by the caller. -/
theorem exists_descended_law {X₀ : Scheme.{u}}
    (c₀ : X₀ ⟶ Spec (CommRingCat.of (fixedField K p 2)))
    (d : A.group.X.left ⟶ X₀)
    (hd : IsPullback d A.group.X.hom c₀
      (Spec.map (CommRingCat.ofHom (algebraMap (fixedField K p 2) K))))
    (τ : A.group.X.left ⟶ A.group.X.left)
    (hτ : (GroupScheme.law A.group).schemeNsmul p ≫ τ =
      absolute p A.group.X.hom ≫ absolute p A.group.X.hom)
    (hτd : τ ≫ d = d) :
    ∃ L₀ : RelativeGroupLaw (fixedField K p 2) c₀,
      AbelianSchemePropertyBundle (fixedField K p 2) c₀ ∧
      ((GroupScheme.law A.group).one (𝟙 _)).1 ≫ d =
        Spec.map (CommRingCat.ofHom (algebraMap (fixedField K p 2) K)) ≫
          (L₀.one (𝟙 _)).1 := by
  obtain ⟨e, he⟩ := exists_descended_one p (GroupScheme.law A.group) τ d hτ hτd
  have hec : e ≫ c₀ = 𝟙 _ := by
    apply P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_one_eq_of_abelianSchemePropertyBundle_of_isPullback_of_faithfullyFlat.P2mWs49LawDescent.eq_of_ιb_comp_eq
      (fixedField K p 2) K
    rw [← Category.assoc, he, Category.assoc, hd.w,
      ← Category.assoc, ((GroupScheme.law A.group).one (𝟙 _)).2,
      Category.id_comp, Category.comp_id]
  obtain ⟨L₀, hL₀⟩ :=
    RelativeGroupLaw.exists_one_eq_of_abelianSchemePropertyBundle_of_isPullback_of_faithfullyFlat
      K c₀ ⟨e, hec⟩ A.group.X.hom d hd A.abelianSchemePropertyBundle
      (GroupScheme.law A.group) he.symm
  obtain ⟨hs, hp, hc⟩ := descended_properties A c₀ d hd
  letI := hs
  letI := hp
  letI := hc
  refine ⟨L₀, ⟨SmoothOfRelativeDimension.smooth g c₀, hp,
    c₀.isConnected_preimage_singleton, ⟨L₀⟩⟩, ?_⟩
  rw [hL₀]
  exact he.symm

end SupersingularCurves.Geometry.FrobeniusFiniteFieldGroupDescent
