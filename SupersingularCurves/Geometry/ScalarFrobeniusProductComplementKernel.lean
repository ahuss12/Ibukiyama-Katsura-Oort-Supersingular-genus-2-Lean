/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.ScalarFrobeniusProductComplement

/-!
# Poincare complements with their actual annihilating morphism

This strengthens the pinned FLT Rosenlicht decomposition proof by retaining
its constructed kernel equation in the conclusion. The proof is adapted from
`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_surjective_mul_of_isProper_of_isCommutative`,
commit `aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`; the discarded local `hNker`
is precisely what controls the scheme-theoretic kernel of the addition map.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
universe u
namespace SupersingularCurves.Geometry.ScalarFrobeniusTate.Poincare
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_surjective_mul_of_isProper_of_isCommutative
open P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_surjective_mul_of_isProper_of_isCommutative.GoodReductionJacobian.RelativeGroupLaw.RosenlichtDecomp
variable (k : Type u) [Field k] [IsAlgClosed k]

theorem exists_complement_with_kernel {G : Scheme.{u}}
    (f : G ⟶ Spec (CommRingCat.of k)) [IsSeparated f] [QuasiCompact f] [ConnectedSpace G]
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (g : ℕ) [SmoothOfRelativeDimension g f]
    {A : Scheme.{u}} (j : A ⟶ G) [IsClosedImmersion j] [ConnectedSpace A] [IsProper (j ≫ f)]
    (LA : RelativeGroupLaw k (j ≫ f)) (a : ℕ) [SmoothOfRelativeDimension a (j ≫ f)]
    (hj : IsHom LA L ⟨j, rfl⟩) (n : ℕ) (hn : 0 < n) (π : SchemeHomOver f (j ≫ f)) (hπ : IsHom L LA π)
    (hπj : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t (j ≫ f)),
      NeronModelInfra.schemeHomOverComp
        (NeronModelInfra.schemeHomOverComp x (⟨j, rfl⟩ : SchemeHomOver (j ≫ f) f)) π = LA.nsmul t n x) :
    ∃ (N : Scheme.{u}) (i : N ⟶ G) (LN : RelativeGroupLaw k (i ≫ f)),
      IsClosedImmersion i ∧ ConnectedSpace N ∧ SmoothOfRelativeDimension (g - a) (i ≫ f) ∧
      a ≤ g ∧ IsHom LN L ⟨i, rfl⟩ ∧
      Surjective
        (L.mul (pullback.fst (j ≫ f) (i ≫ f) ≫ j ≫ f)
          ⟨pullback.fst (j ≫ f) (i ≫ f) ≫ j, Category.assoc _ _ _⟩
          ⟨pullback.snd (j ≫ f) (i ≫ f) ≫ i,
            (Category.assoc _ _ _).trans pullback.condition.symm⟩).1 ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
        (y : SchemeHomOver t (i ≫ f)),
        NeronModelInfra.schemeHomOverComp
          (NeronModelInfra.schemeHomOverComp y ⟨i, rfl⟩) π = LA.one t) := by
  classical
  haveI : Smooth f := SmoothOfRelativeDimension.smooth g f
  haveI : Smooth (j ≫ f) := SmoothOfRelativeDimension.smooth a (j ≫ f)
  have hAc : LA.IsCommutative := isCommutative_of_isHom_mono hc ⟨j, rfl⟩ hj
  set jG : SchemeHomOver (j ≫ f) f := ⟨j, rfl⟩ with hjG

  obtain ⟨L₀, h0hom, h0comm, h0ker, h0lift⟩ := exists_kerLaw L LA π hπ
  set ι₀ : SchemeHomOver (kerStr LA π) f := kerIncl LA π with hι₀
  have hf₀ : ι₀.1 ≫ f = kerStr LA π := ι₀.2
  haveI : LocallyOfFiniteType (kerStr LA π) := by rw [← hf₀]; infer_instance
  haveI : QuasiCompact (kerStr LA π) := by rw [← hf₀]; infer_instance
  obtain ⟨N, i₁, L₁, h, hci₁, hirr, hsm₁, -, -, -, -, hhom₁, -, S, hSfin, hcov⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_isClosedImmersion_smoothOfRelativeDimension_range_eq_connectedComponent_of_perfectField
      k L₀
  haveI := hci₁
  haveI := hirr

  set i : N ⟶ G := i₁ ≫ ι₀.1 with hi
  have ei : i₁ ≫ kerStr LA π = i ≫ f := by rw [hi, Category.assoc, hf₀]
  set LN : RelativeGroupLaw k (i ≫ f) := castLaw ei L₁ with hLN
  have h1hom : IsHom L₁ L₀ ⟨i₁, rfl⟩ := hhom₁
  have hLNhom : IsHom LN L ⟨i, rfl⟩ :=
    castLaw_isHom ei L₁ L (NeronModelInfra.schemeHomOverComp ⟨i₁, rfl⟩ ι₀) (h1hom.comp h0hom)
  haveI : IsClosedImmersion i := by rw [hi]; infer_instance
  haveI hsmN : SmoothOfRelativeDimension h (i ≫ f) := by rw [← ei]; exact hsm₁

  have hNker : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp y ⟨i, rfl⟩) π =
        LA.one t := by
    intro T t y
    have : NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        NeronModelInfra.schemeHomOverComp
          (NeronModelInfra.schemeHomOverComp (⟨y.1, by rw [ei]; exact y.2⟩ : SchemeHomOver t (i₁ ≫ kerStr LA π))
            (⟨i₁, rfl⟩ : SchemeHomOver (i₁ ≫ kerStr LA π) (kerStr LA π))) ι₀ := by
      apply Subtype.ext
      simp only [NeronModelInfra.schemeHomOverComp_coe, Category.assoc, hi]
    rw [this, h0ker]

  have hnormal : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f)
      (m : SchemeHomOver t (i ≫ f)), ∃ m' : SchemeHomOver t (i ≫ f),
        NeronModelInfra.schemeHomOverComp m' (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
          L.mul t (L.mul t x (NeronModelInfra.schemeHomOverComp m (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
            (L.inv t x) := by
    intro T t x m
    refine ⟨m, ?_⟩
    letI := pointCommGroup L hc t
    show _ = x * _ * x⁻¹
    rw [mul_right_comm, _root_.mul_inv_cancel, _root_.one_mul]
  obtain ⟨Q, fQ, LQ, q, hQsep, hQqc, hQsm, hhg, hqsm, hqsurj, hqhom, hQcomm, hqker⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_quotient_smoothOfRelativeDimension_sub_of_isClosedImmersion_of_isAlgClosed
      k f L g i LN h hLNhom hnormal
  haveI := hQsep
  haveI := hQqc
  haveI := hQsm
  haveI := hqsurj
  haveI : Smooth fQ := SmoothOfRelativeDimension.smooth (g - h) fQ
  haveI : Smooth q.1 := SmoothOfRelativeDimension.smooth h q.1
  have hqH : IsHom L LQ q := hqhom

  set u : A ⟶ Q := j ≫ q.1 with hu_def
  have hu : u ≫ fQ = j ≫ f := by rw [hu_def, Category.assoc, q.2]
  haveI : IsProper (u ≫ fQ) := by rw [hu]; infer_instance
  haveI : IsProper u := IsProper.of_comp u fQ
  have hCA : IsClosed (Set.range u.base) := u.isClosedMap.isClosed_range

  have hAab : AbelianSchemePropertyBundle k (j ≫ f) :=
    ⟨inferInstance, inferInstance, fun s => by
      have : (j ≫ f).base ⁻¹' {s} = Set.univ :=
        Set.eq_univ_of_forall fun w => Subsingleton.elim _ _
      rw [this]; exact isConnected_univ, ⟨LA⟩⟩
  have hnsurj : Function.Surjective (LA.schemeNsmul n) :=
    (GoodReductionJacobian.RelativeGroupLaw.isFinite_schemeKerStr_and_finrank_eq_pow_and_finrank_schemeNsmul_eq_pow
      k (j ≫ f) LA hAc hAab a n hn.ne').2.2.2.2.1
  haveI : Surjective (LA.schemeNsmul n) := ⟨hnsurj⟩
  haveI : LocallyOfFiniteType (LA.schemeNsmul n) := by
    have e : LA.schemeNsmul n ≫ (j ≫ f) = j ≫ f := LA.schemeNsmul_over n
    haveI : LocallyOfFiniteType (LA.schemeNsmul n ≫ j ≫ f) := by rw [e]; infer_instance
    exact locallyOfFiniteType_of_comp _ (j ≫ f)

  have hdec₀ : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
      ∃ s ∈ S, ∃ (a' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (j ≫ f))
        (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (i ≫ f)),
        letI := pointCommGroup L hc (𝟙 (Spec (CommRingCat.of k)))
        x * (NeronModelInfra.schemeHomOverComp s ι₀)⁻¹ =
          NeronModelInfra.schemeHomOverComp a' jG * NeronModelInfra.schemeHomOverComp y ⟨i, rfl⟩ := by
    intro x
    letI := pointCommGroup L hc (𝟙 (Spec (CommRingCat.of k)))
    letI := pointCommGroup LA hAc (𝟙 (Spec (CommRingCat.of k)))

    obtain ⟨a₀, ha₀⟩ :=
      AlgebraicGeometry.exists_comp_eq_of_surjective_of_locallyOfFiniteType_of_isAlgClosed
        (LA.schemeNsmul n) (NeronModelInfra.schemeHomOverComp x π).1
    let a' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (j ≫ f) :=
      ⟨a₀, by rw [← LA.schemeNsmul_over n, ← Category.assoc, ha₀]; exact (NeronModelInfra.schemeHomOverComp x π).2⟩
    have ha' : LA.nsmul _ n a' = NeronModelInfra.schemeHomOverComp x π := by
      have := comp_lawNsmul LA a' n (idPt (j ≫ f))
      rw [comp_idPt] at this
      rw [← this]
      exact Subtype.ext ha₀

    have hk : NeronModelInfra.schemeHomOverComp (x * (NeronModelInfra.schemeHomOverComp a' jG)⁻¹) π =
        LA.one _ := by
      show NeronModelInfra.schemeHomOverComp
        (L.mul _ x (L.inv _ (NeronModelInfra.schemeHomOverComp a' jG))) π = _
      rw [hπ, hπ.inv]
      show NeronModelInfra.schemeHomOverComp x π *
        (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp a' jG) π)⁻¹ = 1
      rw [hπj, ha', _root_.mul_inv_cancel]
    obtain ⟨y₁, hy₁⟩ := h0lift _ _ hk
    obtain ⟨s, hs, y, hy⟩ := hcov y₁
    refine ⟨s, hs, a', ⟨y.1, by rw [← ei]; exact y.2⟩, ?_⟩
    have hy' : NeronModelInfra.schemeHomOverComp y₁ ι₀ =
        NeronModelInfra.schemeHomOverComp s ι₀ *
          NeronModelInfra.schemeHomOverComp ⟨y.1, by rw [← ei]; exact y.2⟩ ⟨i, rfl⟩ := by
      rw [hy, h0hom]
      congr 1
    rw [hy₁] at hy'

    set Y := NeronModelInfra.schemeHomOverComp
      (⟨y.1, by rw [← ei]; exact y.2⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (i ≫ f))
      (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) with hY
    set Aa := NeronModelInfra.schemeHomOverComp a' jG with hAa
    set s' := NeronModelInfra.schemeHomOverComp s ι₀ with hs'
    calc x * s'⁻¹ = x * Aa⁻¹ * Aa * s'⁻¹ := by rw [inv_mul_cancel_right]
      _ = Aa * Y := by
          rw [hy', mul_inv_eq_iff_eq_mul, mul_comm s' Y, _root_.mul_assoc Y s' Aa, mul_comm s' Aa,
            ← _root_.mul_assoc, mul_comm Y Aa]

  let Z : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (kerStr LA π) → Set G := fun s =>
    (translate L (L.inv _ (NeronModelInfra.schemeHomOverComp s ι₀))).1.base ⁻¹'
      (q.1.base ⁻¹' Set.range u.base)
  have hZcl : ∀ s, IsClosed (Z s) := fun s =>
    (hCA.preimage q.1.continuous).preimage (Scheme.Hom.continuous _)
  have hZmem : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f, ∃ s ∈ S, pt x ∈ Z s := by
    intro x
    obtain ⟨s, hs, a', y, hxy⟩ := hdec₀ x
    refine ⟨s, hs, ?_⟩
    letI := pointCommGroup L hc (𝟙 (Spec (CommRingCat.of k)))
    letI := pointCommGroup LQ (hQcomm hc) (𝟙 (Spec (CommRingCat.of k)))
    show (translate L _).1.base (pt x) ∈ q.1.base ⁻¹' Set.range u.base
    have e1 : (translate L (L.inv _ (NeronModelInfra.schemeHomOverComp s ι₀))).1.base (pt x) =
        pt (x * (NeronModelInfra.schemeHomOverComp s ι₀)⁻¹) := by
      rw [← pt_comp x (translate L _),
        P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_surjective_mul_of_isProper_of_isCommutative.GoodReductionJacobian.RelativeGroupLaw.RosenlichtDecomp.comp_translate,
        constPt_id]
      rfl
    rw [e1, Set.mem_preimage, ← pt_comp _ q, hxy]
    show pt (NeronModelInfra.schemeHomOverComp (L.mul _ (NeronModelInfra.schemeHomOverComp a' jG)
      (NeronModelInfra.schemeHomOverComp y ⟨i, rfl⟩)) q) ∈ _
    rw [hqH, (hqker _ (NeronModelInfra.schemeHomOverComp y ⟨i, rfl⟩)).mpr ⟨y, rfl⟩, LQ.mul_one]
    refine ⟨pt a', ?_⟩
    rw [pt_comp, pt_comp, hu_def, Scheme.Hom.comp_apply]
  haveI : JacobsonSpace G := LocallyOfFiniteType.jacobsonSpace f
  haveI : JacobsonSpace A := LocallyOfFiniteType.jacobsonSpace (j ≫ f)
  have hUnion : (⋃ s ∈ S, Z s) = Set.univ := by
    have hcl : IsClosed (⋃ s ∈ S, Z s) := hSfin.isClosed_biUnion fun s _ => hZcl s
    apply Set.eq_univ_of_univ_subset
    rw [← closure_closedPoints (X := G)]
    refine closure_minimal ?_ hcl
    intro z hz
    obtain ⟨x, rfl⟩ := exists_pt_eq (f := f) hz
    obtain ⟨s, hs, hmem⟩ := hZmem x
    exact Set.mem_biUnion hs hmem

  haveI : IrreducibleSpace G := by
    obtain ⟨G₀, i₀', -, hoi, -, hirr', hrange', -⟩ :=
      GoodReductionJacobian.RelativeGroupLaw.exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex
        k L
    rw [PreconnectedSpace.connectedComponent_eq_univ, Set.range_eq_univ] at hrange'
    rw [irreducibleSpace_def, Set.top_eq_univ, ← Set.image_univ_of_surjective hrange']
    exact IsIrreducible.image (IrreducibleSpace.isIrreducible_univ G₀) _ i₀'.continuous.continuousOn
  obtain ⟨s₀, -, hZs₀⟩ : ∃ s ∈ S, Z s = Set.univ := by
    have hirrG := (IrreducibleSpace.isIrreducible_univ G)
    rw [isIrreducible_iff_sUnion_isClosed] at hirrG
    obtain ⟨z, hz, hz'⟩ := hirrG (hSfin.toFinset.image Z)
      (fun z hz => by
        obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hz
        exact hZcl s)
      (by
        intro w _
        have hw : w ∈ ⋃ s ∈ S, Z s := hUnion.symm ▸ Set.mem_univ w
        obtain ⟨s, hs, hws⟩ := Set.mem_iUnion₂.mp hw
        exact Set.mem_sUnion.mpr ⟨Z s, Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨s, hSfin.mem_toFinset.mpr hs, rfl⟩), hws⟩)
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨s, hSfin.mem_toFinset.mp hs, Set.eq_univ_of_univ_subset hz'⟩
  have hall : ∀ z : G, q.1.base z ∈ Set.range u.base := by
    intro z
    have h2 : (translate L (L.inv _ (NeronModelInfra.schemeHomOverComp s₀ ι₀))).1.base
        ((translate L (NeronModelInfra.schemeHomOverComp s₀ ι₀)).1.base z) = z := by
      rw [← Scheme.Hom.comp_apply, translate_comp_translate_inv]
      rfl
    have h1 : (translate L (NeronModelInfra.schemeHomOverComp s₀ ι₀)).1.base z ∈ Z s₀ :=
      hZs₀.symm ▸ Set.mem_univ _
    change (translate L (L.inv _ (NeronModelInfra.schemeHomOverComp s₀ ι₀))).1.base
        ((translate L (NeronModelInfra.schemeHomOverComp s₀ ι₀)).1.base z) ∈
      q.1.base ⁻¹' Set.range u.base at h1
    rw [h2] at h1
    exact h1

  have hdec : ∀ z : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
      ∃ (a' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (j ≫ f))
        (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (i ≫ f)),
        z = L.mul _ (NeronModelInfra.schemeHomOverComp a' jG) (NeronModelInfra.schemeHomOverComp y ⟨i, rfl⟩) := by
    intro z
    obtain ⟨p, hp⟩ := hall (pt z)
    have hqz : IsClosed ({q.1.base (pt z)} : Set Q) := by
      rw [← pt_comp z q]; exact isClosed_pt (f := fQ) _
    have hF : IsClosed (u.base ⁻¹' {q.1.base (pt z)}) := hqz.preimage u.continuous
    have hFne : (u.base ⁻¹' {q.1.base (pt z)} ∩ closedPoints A).Nonempty := by
      by_contra hcon
      rw [Set.not_nonempty_iff_eq_empty] at hcon
      have := closure_inter_closedPoints hF
      rw [hcon, closure_empty] at this
      have hpF : p ∈ u.base ⁻¹' {q.1.base (pt z)} := hp
      rw [← this] at hpF
      exact hpF
    obtain ⟨p₀, hp₀F, hp₀cl⟩ := hFne
    obtain ⟨a', ha'⟩ := exists_pt_eq (f := j ≫ f) (mem_closedPoints_iff.mp hp₀cl)
    have hQpt : NeronModelInfra.schemeHomOverComp z q =
        NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp a' jG) q := by
      apply eq_of_pt_eq (f := fQ)
      rw [pt_comp, pt_comp, pt_comp, hjG, ha']
      show _ = q.1.base (j.base p₀)
      rw [← Scheme.Hom.comp_apply]
      exact hp₀F.symm
    letI := pointCommGroup L hc (𝟙 (Spec (CommRingCat.of k)))
    letI := pointCommGroup LQ (hQcomm hc) (𝟙 (Spec (CommRingCat.of k)))
    have hk : NeronModelInfra.schemeHomOverComp (z * (NeronModelInfra.schemeHomOverComp a' jG)⁻¹) q =
        LQ.one _ := by
      show NeronModelInfra.schemeHomOverComp
        (L.mul _ z (L.inv _ (NeronModelInfra.schemeHomOverComp a' jG))) q = _
      rw [hqH, hqH.inv, hQpt]
      exact _root_.mul_inv_cancel _
    obtain ⟨y, hy⟩ := (hqker _ _).mp hk
    refine ⟨a', y, ?_⟩
    show z = NeronModelInfra.schemeHomOverComp a' jG * NeronModelInfra.schemeHomOverComp y ⟨i, rfl⟩
    rw [hy, mul_comm, inv_mul_cancel_right]

  set tT : pullback (j ≫ f) (i ≫ f) ⟶ Spec (CommRingCat.of k) := pullback.fst (j ≫ f) (i ≫ f) ≫ j ≫ f
    with htT
  set xA : SchemeHomOver tT f := ⟨pullback.fst (j ≫ f) (i ≫ f) ≫ j, Category.assoc _ _ _⟩ with hxA
  set xN : SchemeHomOver tT f := ⟨pullback.snd (j ≫ f) (i ≫ f) ≫ i,
    (Category.assoc _ _ _).trans pullback.condition.symm⟩ with hxN
  set m := L.mul tT xA xN with hm
  haveI : LocallyOfFiniteType tT := by rw [htT]; infer_instance
  haveI : LocallyOfFiniteType (m.1 ≫ f) := by rw [m.2]; infer_instance
  haveI : LocallyOfFiniteType m.1 := locallyOfFiniteType_of_comp _ f
  haveI : QuasiCompact tT := by rw [htT]; infer_instance
  haveI : QuasiCompact (m.1 ≫ f) := by rw [m.2]; infer_instance
  haveI : QuasiCompact m.1 := MorphismProperty.of_postcomp (W := @QuasiCompact) (W' := @QuasiSeparated)
    m.1 f inferInstance inferInstance
  have hsurjm : Surjective m.1 := by
    apply AlgebraicGeometry.surjective_of_forall_exists_comp_eq_of_isAlgClosed m.1 f
    intro zpt hz
    obtain ⟨a', y, hzy⟩ := hdec ⟨zpt, hz⟩
    refine ⟨pullback.lift a'.1 y.1 (by rw [a'.2, y.2]), ?_⟩
    set x' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) tT :=
      ⟨pullback.lift a'.1 y.1 (by rw [a'.2, y.2]), by rw [htT, pullback.lift_fst_assoc, a'.2]⟩ with hx'
    have e := congrArg Subtype.val (comp_lawMul L x' xA xN)
    have eA : NeronModelInfra.schemeHomOverComp x' xA = NeronModelInfra.schemeHomOverComp a' jG :=
      Subtype.ext (by simp only [NeronModelInfra.schemeHomOverComp_coe, hxA, hjG, hx', pullback.lift_fst_assoc])
    have eN : NeronModelInfra.schemeHomOverComp x' xN =
        NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) :=
      Subtype.ext (by simp only [NeronModelInfra.schemeHomOverComp_coe, hxN, hx', pullback.lift_snd_assoc])
    rw [eA, eN, ← hzy] at e
    simpa only [NeronModelInfra.schemeHomOverComp_coe, hm] using e

  haveI : Surjective u := ⟨by
    rw [← Set.range_eq_univ, Set.eq_univ_iff_forall]
    intro w
    obtain ⟨z, rfl⟩ := q.1.surjective w
    exact hall z⟩
  haveI : UniversallyClosed fQ := by
    haveI : UniversallyClosed (u ≫ fQ) := by rw [hu]; infer_instance
    exact UniversallyClosed.of_comp_surjective u fQ
  haveI : IsProper fQ := ⟨⟩
  haveI : ConnectedSpace Q := Function.Surjective.connectedSpace q.1.surjective q.1.continuous
  have hQab : AbelianSchemePropertyBundle k fQ :=
    ⟨inferInstance, inferInstance, fun s => by
      have : fQ.base ⁻¹' {s} = Set.univ := Set.eq_univ_of_forall fun w => Subsingleton.elim _ _
      rw [this]; exact isConnected_univ, ⟨LQ⟩⟩
  obtain ⟨ℓ, h2ℓ, hcop, hℓk⟩ := RosenlichtDecompAux.exists_two_le_coprime_cast_ne_zero k n hn
  have hcardA :=
    GoodReductionJacobian.RelativeGroupLaw.natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero
      k (j ≫ f) LA hAc hAab a ℓ hℓk
  have hcardQ :=
    GoodReductionJacobian.RelativeGroupLaw.natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero
      k fQ LQ (hQcomm hc) hQab (g - h) ℓ hℓk
  letI instA := pointCommGroup LA hAc (𝟙 (Spec (CommRingCat.of k)))
  letI instQ := pointCommGroup LQ (hQcomm hc) (𝟙 (Spec (CommRingCat.of k)))
  letI instG := pointCommGroup L hc (𝟙 (Spec (CommRingCat.of k)))
  have huH : IsHom LA LQ (NeronModelInfra.schemeHomOverComp jG q) := hj.comp hqH
  let φ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (j ≫ f) →*
      SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) fQ :=
    { toFun := fun a' => NeronModelInfra.schemeHomOverComp a' (NeronModelInfra.schemeHomOverComp jG q)
      map_one' := huH.one _
      map_mul' := fun x y => huH _ x y }
  have hφ : ∀ a', φ a' = NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp a' jG) q :=
    fun a' => (NeronModelInfra.schemeHomOverComp_assoc _ _ _).symm
  have hφsurj : Function.Surjective φ := by
    intro w
    haveI : LocallyOfFiniteType q.1 := inferInstance
    obtain ⟨zpt, hz⟩ :=
      AlgebraicGeometry.exists_comp_eq_of_surjective_of_locallyOfFiniteType_of_isAlgClosed q.1 w.1
    let z : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f :=
      ⟨zpt, by rw [← q.2, ← Category.assoc, hz]; exact w.2⟩
    obtain ⟨a', y, hzy⟩ := hdec z
    refine ⟨a', ?_⟩
    rw [hφ]
    have : NeronModelInfra.schemeHomOverComp z q = w := Subtype.ext hz
    rw [← this, hzy, hqH, (hqker _ (NeronModelInfra.schemeHomOverComp y ⟨i, rfl⟩)).mpr ⟨y, rfl⟩,
      LQ.mul_one]
  have hφker : ∀ a', φ a' = 1 → a' ^ n = 1 := by
    intro a' h1
    rw [hφ] at h1
    obtain ⟨y, hy⟩ := (hqker _ _).mp h1
    have := hNker _ y
    rw [hy, hjG, hπj] at this
    rw [← nsmul_eq_pow LA hAc]
    exact this
  have hcard := RosenlichtDecompAux.natCard_torsion_eq_of_surjective φ hφsurj n ℓ hcop hφker
  have eA : Nat.card {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (j ≫ f) //
      LA.IsTorsionPoint (𝟙 (Spec (CommRingCat.of k))) ℓ x} =
      Nat.card {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (j ≫ f) // x ^ ℓ = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => by
      rw [GoodReductionJacobian.RelativeGroupLaw.isTorsionPoint_def, nsmul_eq_pow LA hAc]; rfl)
  have eQ : Nat.card {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) fQ //
      LQ.IsTorsionPoint (𝟙 (Spec (CommRingCat.of k))) ℓ x} =
      Nat.card {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) fQ // x ^ ℓ = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => by
      rw [GoodReductionJacobian.RelativeGroupLaw.isTorsionPoint_def, nsmul_eq_pow LQ (hQcomm hc)]; rfl)
  have hpow : ℓ ^ (2 * a) = ℓ ^ (2 * (g - h)) := by rw [← hcardA, ← hcardQ, eA, eQ, hcard]
  have hag : 2 * a = 2 * (g - h) := Nat.pow_right_injective h2ℓ hpow
  have hh : h = g - a := by omega
  subst hh
  exact ⟨N, i, LN, inferInstance, inferInstance, hsmN, by omega, hLNhom, hsurjm, hNker⟩


end SupersingularCurves.Geometry.ScalarFrobeniusTate.Poincare
