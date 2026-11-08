/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentEquivariance
import SupersingularCurves.Geometry.FrobeniusInvariantIdeal
import Theorems.Thm_AlgebraicGeometry_ProjSpace_restrictFun_app_app_awayToSection_eq_app_awayToSection_map
import Theorems.Thm_AlgebraicGeometry_ProjSpace_map_preimage_basicOpen_X
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_idealSheafData_ideal_basicOpen_eq_span
import Theorems.Thm_AlgebraicGeometry_ProjSpace_eq_ker_of_ideal_basicOpen_eq_span_of_isClosedImmersion
import Theorems.Thm_AlgebraicGeometry_ProjSpace_eq_comap_map_of_ideal_basicOpen_eq_span
import Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map

/-! # Descent of an actual Frobenius-equivariant closed projective image -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SupersingularCurves.Geometry.FrobeniusFiniteFieldDescent
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial FrobeniusDescent
attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {n : ℕ}

/-- The standard degree-zero chart section represented by a homogeneous equation. -/
def equationChart (d : ℕ) (F : MvPolynomial (Fin (n + 1)) A)
    (hF : F.IsHomogeneous d) (i : Fin (n + 1)) :
    Γ(Proj (homogeneousSubmodule (Fin (n + 1)) A),
      Proj.basicOpen (homogeneousSubmodule (Fin (n + 1)) A) (X i)) :=
  Proj.awayToSection (homogeneousSubmodule (Fin (n + 1)) A) (X i)
    (HomogeneousLocalization.mk {
      deg := d
      num := ⟨F, (mem_homogeneousSubmodule d F).mpr hF⟩
      den := ⟨X i ^ d, (mem_homogeneousSubmodule d _).mpr (isHomogeneous_X_pow i d)⟩
      den_mem := ⟨d, rfl⟩ })

/-- The literal ideal of homogeneous equations vanishing on a projective map. -/
def projectiveImageIdeal {Z : Scheme.{u}}
    (ι : Z ⟶ Proj (homogeneousSubmodule (Fin (n + 1)) A)) :
    Ideal (MvPolynomial (Fin (n + 1)) A) :=
  Ideal.span {F | ∃ (d : ℕ) (hF : F.IsHomogeneous d), 0 ≤ d ∧
    ∀ i, ι.app (Proj.basicOpen (homogeneousSubmodule (Fin (n + 1)) A) (X i))
      (equationChart d F hF i) = 0}

/-- Its homogeneous components still vanish; this follows from the construction. -/
theorem projectiveImageIdeal_homogeneous {Z : Scheme.{u}}
    (ι : Z ⟶ Proj (homogeneousSubmodule (Fin (n + 1)) A))
    (F : MvPolynomial (Fin (n + 1)) A) (hF : F ∈ projectiveImageIdeal ι) (d : ℕ) :
    homogeneousComponent d F ∈ projectiveImageIdeal ι := by
  have hI : (projectiveImageIdeal ι).IsHomogeneous
      (homogeneousSubmodule (Fin (n + 1)) A) := by
    apply Ideal.homogeneous_span
    rintro G ⟨e, he, _, _⟩
    exact ⟨e, (mem_homogeneousSubmodule e G).mpr he⟩
  have h := hI d hF
  rw [show (DirectSum.decompose (homogeneousSubmodule (Fin (n + 1)) A) F d :
      MvPolynomial (Fin (n + 1)) A) = homogeneousComponent d F from
      MvPolynomial.decomposition.decompose'_apply F d] at h
  exact h

variable {K : Type u} [Field K] {Z : Scheme.{u}}

/-- Actual semilinear equivariance forces stability of the equations of the image. -/
theorem projectiveImageIdeal_map_mem (ι : Z ⟶ Proj (homogeneousSubmodule (Fin (n + 1)) K))
    (σ : K →+* K) (τ : Z ⟶ Z)
    (hτ : τ ≫ ι = ι ≫ coefficientMap σ n)
    (F : MvPolynomial (Fin (n + 1)) K) (hF : F ∈ projectiveImageIdeal ι) :
    MvPolynomial.map σ F ∈ projectiveImageIdeal ι := by
  suffices hle : projectiveImageIdeal ι ≤
      Ideal.comap (MvPolynomial.map σ) (projectiveImageIdeal ι) from hle hF
  apply Ideal.span_le.mpr
  rintro G ⟨d, hG, hd, hv⟩
  apply Ideal.subset_span
  refine ⟨d, hG.map σ, hd, ?_⟩
  letI : Algebra K K := σ.toAlgebra
  have hτ' : τ ≫ ι = ι ≫ ProjSpace.map K K n := hτ
  intro i
  have hopen : ι ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin (n + 1)) K) (X i) ≤
      τ ⁻¹ᵁ (ι ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin (n + 1)) K) (X i)) := by
    rw [← Scheme.Hom.comp_preimage, hτ', Scheme.Hom.comp_preimage,
      ProjSpace.map_preimage_basicOpen_X]
  have h := ProjSpace.restrictFun_app_app_awayToSection_eq_app_awayToSection_map
    ι K ι τ hτ' d G hG i hopen
  change ProjSpace.restrictFun hopen (τ.app _ (ι.app _ (equationChart d G hG i))) =
    ι.app _ (equationChart d (MvPolynomial.map σ G) (hG.map σ) i) at h
  rw [hv i, map_zero] at h
  exact h.symm.trans (by simp [ProjSpace.restrictFun])

variable (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ) [IsAlgClosed K]

/-- The actual equations of an equivariant projective image descend to the literal
finite Frobenius-fixed coefficient field. -/
theorem projectiveImageIdeal_descends
    (ι : Z ⟶ Proj (homogeneousSubmodule (Fin (n + 1)) K)) (τ : Z ⟶ Z)
    (hτ : τ ≫ ι = ι ≫ coefficientMap (iterateFrobenius K p s) n) (hs : s ≠ 0) :
    Ideal.map (MvPolynomial.map (fixedField K p s).subtype)
      (Ideal.comap (MvPolynomial.map (fixedField K p s).subtype)
        (projectiveImageIdeal ι)) = projectiveImageIdeal ι := by
  apply ideal_map_comap_eq p s hs
  exact projectiveImageIdeal_map_mem ι (iterateFrobenius K p s) τ hτ

/-- Coefficient extension commutes with each actual homogeneous component. -/
theorem map_homogeneousComponent {B : Type u} [CommRing B] (f : A →+* B)
    (d : ℕ) (F : MvPolynomial (Fin (n + 1)) A) :
    MvPolynomial.map f (homogeneousComponent d F) =
      homogeneousComponent d (MvPolynomial.map f F) := by
  ext m
  simp only [coeff_map, coeff_homogeneousComponent]
  split_ifs <;> simp

section Small
variable {K₀ : Type} [Field K₀] [IsAlgClosed K₀]
  (q : ℕ) [Fact q.Prime] [CharP K₀ q] (r : ℕ)
  {Y : Scheme.{0}} {N : ℕ}

/-- The actual kernel ideal sheaf of a Frobenius-equivariant closed immersion
is pulled back from an ideal sheaf over the finite fixed field. -/
theorem exists_projectiveImage_idealSheaf
    (ι : Y ⟶ Proj (homogeneousSubmodule (Fin (N + 1)) K₀))
    [IsClosedImmersion ι] (τ : Y ⟶ Y)
    (hτ : τ ≫ ι = ι ≫ coefficientMap (iterateFrobenius K₀ q r) N) (hr : r ≠ 0) :
    ∃ I₀ : (Proj (homogeneousSubmodule (Fin (N + 1)) (fixedField K₀ q r))).IdealSheafData,
      I₀.comap (ProjSpace.map (fixedField K₀ q r) K₀ N) = ι.ker := by
  let k := fixedField K₀ q r
  let I : Ideal (MvPolynomial (Fin (N + 1)) K₀) := projectiveImageIdeal ι
  let I₀ : Ideal (MvPolynomial (Fin (N + 1)) k) :=
    I.comap (MvPolynomial.map (algebraMap k K₀))
  have hI : I₀.map (MvPolynomial.map (algebraMap k K₀)) = I :=
    projectiveImageIdeal_descends q r ι τ hτ hr
  have hI₀ (F : MvPolynomial (Fin (N + 1)) k) (hF : F ∈ I₀) (d : ℕ) :
      homogeneousComponent d F ∈ I₀ := by
    change MvPolynomial.map (algebraMap k K₀) (homogeneousComponent d F) ∈ I
    rw [map_homogeneousComponent]
    exact projectiveImageIdeal_homogeneous ι _ hF d
  obtain ⟨𝓘₀, h𝓘₀⟩ := ProjSpace.exists_idealSheafData_ideal_basicOpen_eq_span N k I₀
  obtain ⟨𝓘, h𝓘⟩ := ProjSpace.exists_idealSheafData_ideal_basicOpen_eq_span N K₀ I
  have hker : 𝓘 = ι.ker :=
    ProjSpace.eq_ker_of_ideal_basicOpen_eq_span_of_isClosedImmersion N K₀ Y ι
      inferInstance 0 𝓘 h𝓘
  refine ⟨𝓘₀, ?_⟩
  rw [← hker]
  symm
  apply ProjSpace.eq_comap_map_of_ideal_basicOpen_eq_span N k K₀ I₀ hI₀ 𝓘₀ h𝓘₀ 𝓘
  simpa only [hI] using h𝓘

/-- A closed projective embedding descends, retaining the actual base-change
square, the embedding, and invariance under the original semilinear action. -/
theorem exists_fixedField_closed_projective_model
    (ι : Y ⟶ Proj (homogeneousSubmodule (Fin (N + 1)) K₀))
    [IsClosedImmersion ι] (τ : Y ⟶ Y)
    (hτ : τ ≫ ι = ι ≫ coefficientMap (iterateFrobenius K₀ q r) N) (hr : r ≠ 0) :
    ∃ (Y₀ : Scheme.{0})
      (ι₀ : Y₀ ⟶ Proj (homogeneousSubmodule (Fin (N + 1)) (fixedField K₀ q r)))
      (d : Y ⟶ Y₀),
      IsClosedImmersion ι₀ ∧
      d ≫ ι₀ = ι ≫ ProjSpace.map (fixedField K₀ q r) K₀ N ∧
      IsPullback d (ι ≫ ProjSpace.π K₀ N) (ι₀ ≫ ProjSpace.π (fixedField K₀ q r) N)
        (Spec.map (CommRingCat.ofHom (algebraMap (fixedField K₀ q r) K₀))) ∧
      τ ≫ d = d := by
  let k := fixedField K₀ q r
  let φ := ProjSpace.map k K₀ N
  obtain ⟨I₀, hI₀⟩ := exists_projectiveImage_idealSheaf q r ι τ hτ hr
  have hle : I₀.subschemeι.ker ≤ (ι ≫ φ).ker := by
    rw [I₀.ker_subschemeι]
    have h := (Scheme.IdealSheafData.le_map_iff_comap_le
      (I := ι.ker) (f := φ) (J := I₀)).mpr hI₀.le
    simpa only [Scheme.IdealSheafData.map_ker] using h
  let d := IsClosedImmersion.lift I₀.subschemeι (ι ≫ φ) hle
  have hd : d ≫ I₀.subschemeι = ι ≫ φ := IsClosedImmersion.lift_fac _ _ _
  have hpb : IsPullback ι d φ I₀.subschemeι := by
    apply isPullback_of_isClosedImmersion ι I₀.subschemeι d φ hd.symm
    simpa only [I₀.ker_subschemeι] using hI₀
  have hbase := hpb.flip.paste_vert (ProjSpace.isPullback_map k K₀ N)
  refine ⟨I₀.subscheme, I₀.subschemeι, d, inferInstance, hd, hbase, ?_⟩
  apply (cancel_mono I₀.subschemeι).mp
  rw [Category.assoc, hd, ← Category.assoc, hτ, Category.assoc]
  congr 1
  let σ := iterateFrobenius K₀ q r
  let θ : homogeneousSubmodule (Fin (N + 1)) K₀ →+*ᵍ
      homogeneousSubmodule (Fin (N + 1)) K₀ :=
    @ProjSpace.mvMapGraded K₀ _ K₀ _ σ.toAlgebra N
  let γ := ProjSpace.mvMapGraded k K₀ N
  have hcomp : θ.comp γ = γ := by
    ext F m
    change coeff m (MvPolynomial.map σ (MvPolynomial.map (algebraMap k K₀) F)) =
      coeff m (MvPolynomial.map (algebraMap k K₀) F)
    simp only [coeff_map]
    exact (coeff m F).property
  change Proj.map θ _ ≫ Proj.map γ _ = Proj.map γ _
  rw [← Proj.map_comp]
  congr 1
end Small

end SupersingularCurves.Geometry.FrobeniusFiniteFieldDescent
