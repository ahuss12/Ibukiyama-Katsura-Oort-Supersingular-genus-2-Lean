/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.EllipticSubgroupFromMap
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_of_surjective_of_isFinite_pullback_snd
import Theorems.Thm_IsIrreducible_topologicalKrullDim_add_one_le_of_isClosed_of_ne

/-! # Elliptic subgroups from maps out of an abelian surface

The subgroup is the reduced identity component of the actual kernel. Its
dimension is proved to be one; a zero-dimensional kernel would make a
surface finite over a curve, contradicting preservation of dimension.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
universe u
namespace SupersingularCurves.Geometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open FrobeniusFactorGroup
open P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_surjective_mul_of_isProper_of_isCommutative
open P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_surjective_mul_of_isProper_of_isCommutative.GoodReductionJacobian.RelativeGroupLaw.RosenlichtDecomp

/-- Over an algebraically closed field, finiteness of all rational points of
a proper scheme implies finiteness of its structure morphism. -/
theorem isFinite_of_finite_rationalPoints
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]
    (hfin : (Set.univ : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f)).Finite) :
    IsFinite f := by
  letI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  let Z : Set X := pt '' (Set.univ : Set (SchemeHomOver (𝟙 _) f))
  have hZfin : Z.Finite := hfin.image _
  have hZclosed : IsClosed Z := by
    have h := hfin.isClosed_biUnion (fun x _ => isClosed_pt x)
    simpa only [Z, Set.biUnion_univ, Set.iUnion_singleton_eq_range, Set.image_univ] using h
  have hZall : Set.univ ⊆ Z := by
    rw [← closure_closedPoints (X := X)]
    apply closure_minimal _ hZclosed
    intro x hx
    obtain ⟨a, ha⟩ := exists_pt_eq (f := f) (mem_closedPoints_iff.mp hx)
    exact ⟨a, Set.mem_univ _, ha⟩
  have hXfin : (Set.univ : Set X).Finite := hZfin.subset hZall
  letI : LocallyQuasiFinite f := LocallyQuasiFinite.of_finite_preimage_singleton f
    (fun _ => hXfin.subset (Set.subset_univ _))
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

namespace AbelianVariety
variable {K : Type} [Field K] [IsAlgClosed K] {g : ℕ}

theorem surjective_of_to_elliptic_rationalMap_ne_zero
    (ℓ : ℕ) [Fact ℓ.Prime] (A : AbelianVariety K g) (E : AbelianVariety K 1)
    (f : A.group ⟶ E.group) (hf : AbelianTate.rationalMap ℓ f ≠ 0) :
    Surjective (underlyingScheme.map f) := by
  letI : IsIntegral A.group.X.left :=
    AbelianSchemePropertyBundle.isIntegral_of_field A.abelianSchemePropertyBundle
  letI : IsIntegral E.group.X.left :=
    AbelianSchemePropertyBundle.isIntegral_of_field E.abelianSchemePropertyBundle
  letI : GeometricallyIntegral E.group.X.hom :=
    geometricallyIntegral_of_isAlgClosed E.group.X.hom
  exact surjective_of_target_proper_curve_of_not_constant A.group.X.hom E.group.X.hom
    (underlyingScheme.map f) f.hom.hom.w
    (AbelianTate.not_constant_of_rationalMap_ne_zero ℓ f hf)

/-- A nonzero map from a surface to an elliptic curve constructs an actual
closed elliptic subgroup, without assuming a splitting or a kernel dimension. -/
theorem exists_closed_elliptic_subgroup_of_to_elliptic_rationalMap_ne_zero
    (ℓ : ℕ) [Fact ℓ.Prime] (A : AbelianVariety K 2) (E : AbelianVariety K 1)
    (f : A.group ⟶ E.group) (hf : AbelianTate.rationalMap ℓ f ≠ 0) :
    ∃ (X : Scheme) (j : X ⟶ A.group.X.left)
      (L : RelativeGroupLaw K (j ≫ A.group.X.hom)),
      IsClosedImmersion j ∧ ConnectedSpace X ∧
      SmoothOfRelativeDimension 1 (j ≫ A.group.X.hom) ∧
      (∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of K))
        (x y : SchemeHomOver t (j ≫ A.group.X.hom)),
        pointMap j rfl (L.mul t x y) =
          (GroupScheme.law A.group).mul t (pointMap j rfl x) (pointMap j rfl y)) := by
  classical
  let LA := GroupScheme.law A.group
  let LE := GroupScheme.law E.group
  let φ : A.group.X.left ⟶ E.group.X.left := f.hom.hom.left
  let π : SchemeHomOver A.group.X.hom E.group.X.hom := ⟨φ, f.hom.hom.w⟩
  have hπ : IsHom LA LE π := A.hom_preserves_law E f
  have hfs := A.surjective_of_to_elliptic_rationalMap_ne_zero ℓ E f hf
  letI : Surjective φ := hfs
  letI : IsProper (φ ≫ E.group.X.hom) := by rw [f.hom.hom.w]; infer_instance
  letI : IsProper φ := IsProper.of_comp φ E.group.X.hom
  letI : IsProper (kerStr LE π) := inferInstance
  obtain ⟨LH, hHhom, -, hHker, -⟩ := exists_kerLaw LA LE π hπ
  obtain ⟨X, i, LX, n, hi, hirr, hsm, -, -, hrange, hdim, hihom, -, S, hSfin, hcover⟩ :=
    RelativeGroupLaw.exists_isClosedImmersion_smoothOfRelativeDimension_range_eq_connectedComponent_of_perfectField
      K LH
  letI := hi
  letI := hirr
  letI := hsm
  have hnpos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (i ≫ kerStr LE π)
    letI : IsLocallyArtinian X := IsLocallyArtinian.of_topologicalKrullDim_le_zero
      (by rw [hdim, hn0]; exact le_rfl)
    letI : Subsingleton X := subsingleton_of_preconnected_totallyDisconnected
    have hpoints : (Set.univ : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (kerStr LE π))).Finite := by
      apply hSfin.subset
      intro x _
      obtain ⟨s, hs, a, ha⟩ := hcover x
      have haone : a = LX.one (𝟙 _) := eq_of_pt_eq (Subsingleton.elim _ _)
      have hione : NeronModelInfra.schemeHomOverComp (LX.one (𝟙 _))
          (⟨i, rfl⟩ : SchemeHomOver (i ≫ kerStr LE π) (kerStr LE π)) = LH.one (𝟙 _) :=
        IsHom.one (show IsHom LX LH ⟨i, rfl⟩ from hihom) (𝟙 _)
      rw [haone, hione, LH.mul_one] at ha
      rw [ha]
      exact hs
    letI : IsFinite (kerStr LE π) := isFinite_of_finite_rationalPoints _ hpoints
    obtain ⟨hfinite, -⟩ :=
      RelativeGroupLaw.isFinite_and_flat_of_surjective_of_isFinite_pullback_snd
        LA A.groupScheme_law_commutative A.abelianSchemePropertyBundle
        LE E.groupScheme_law_commutative E.abelianSchemePropertyBundle
        π hπ hfs inferInstance
    letI : IsFinite φ := hfinite
    letI : Smooth E.group.X.hom := SmoothOfRelativeDimension.smooth 1 E.group.X.hom
    letI : SmoothOfRelativeDimension 2 E.group.X.hom :=
      FiniteQuotientGeometry.smoothOfRelativeDimension_of_finite_surjective
        A.group.X.hom E.group.X.hom φ f.hom.hom.w 2 LE
    letI : Nonempty E.group.X.left := ⟨pt (LE.one (𝟙 _))⟩
    have hbad : (2 : WithBot ℕ∞) ≤ 1 :=
      (SmoothOfRelativeDimension.le_topologicalKrullDim E.group.X.hom 2).trans
        (SmoothOfRelativeDimension.topologicalKrullDim_le E.group.X.hom 1)
    norm_num at hbad
  let j : X ⟶ A.group.X.left := i ≫ (kerIncl LE π).1
  have ej : i ≫ kerStr LE π = j ≫ A.group.X.hom := by
    change i ≫ kerStr LE π = (i ≫ (kerIncl LE π).1) ≫ A.group.X.hom
    rw [Category.assoc, (kerIncl LE π).2]
  let L : RelativeGroupLaw K (j ≫ A.group.X.hom) := castLaw ej LX
  have hjhom : IsHom L LA ⟨j, rfl⟩ :=
    castLaw_isHom ej LX LA
      (NeronModelInfra.schemeHomOverComp ⟨i, rfl⟩ (kerIncl LE π))
      (IsHom.comp (show IsHom LX LH ⟨i, rfl⟩ from hihom) hHhom)
  letI : IsClosedImmersion j := inferInstance
  have hne : Set.range j ≠ Set.univ := by
    intro h
    apply AbelianTate.not_constant_of_rationalMap_ne_zero ℓ f hf
    refine ⟨pt (LE.one (𝟙 _)), fun x => ?_⟩
    obtain ⟨z, rfl⟩ := Set.range_eq_univ.mp h x
    have heq : j ≫ φ = (i ≫ kerStr LE π) ≫ (LE.one (𝟙 _)).1 := by
      change (i ≫ pullback.fst π.1 (LE.one (𝟙 _)).1) ≫ π.1 =
        (i ≫ pullback.snd π.1 (LE.one (𝟙 _)).1) ≫ (LE.one (𝟙 _)).1
      rw [Category.assoc, pullback.condition, ← Category.assoc]
    change φ (j z) = _
    rw [← Scheme.Hom.comp_apply, heq, Scheme.Hom.comp_apply]
    exact congrArg (LE.one (𝟙 _)).1 (Subsingleton.elim _ _)
  letI : IsIntegral A.group.X.left :=
    AbelianSchemePropertyBundle.isIntegral_of_field A.abelianSchemePropertyBundle
  have hjdim : topologicalKrullDim ↥(Set.range j) = n := by
    rw [← IsHomeomorph.topologicalKrullDim_eq _ j.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph]
    exact hdim
  have hlt : n < 2 := by
    have h1 := IsIrreducible.topologicalKrullDim_add_one_le_of_isClosed_of_ne
      (IrreducibleSpace.isIrreducible_univ A.group.X.left)
      j.isClosedEmbedding.isClosed_range (Set.subset_univ _) hne
    have h2 : topologicalKrullDim ↥(Set.univ : Set A.group.X.left) ≤ 2 :=
      (topologicalKrullDim_subspace_le _ _).trans
        (SmoothOfRelativeDimension.topologicalKrullDim_le A.group.X.hom 2)
    rw [hjdim] at h1
    have h3 : (n : WithBot ℕ∞) + 1 ≤ 2 := h1.trans h2
    have h4 : (n : ℕ∞) + 1 ≤ 2 := by exact_mod_cast h3
    have h5 : n + 1 ≤ 2 := by exact_mod_cast h4
    omega
  have hn : n = 1 := by omega
  have hs : SmoothOfRelativeDimension 1 (j ≫ A.group.X.hom) := by
    rw [← ej]
    exact hn ▸ hsm
  exact ⟨X, j, L, inferInstance, inferInstance, hs, hjhom⟩


end AbelianVariety
end SupersingularCurves.Geometry
