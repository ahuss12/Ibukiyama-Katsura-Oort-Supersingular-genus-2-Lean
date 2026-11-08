/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.PicardCech
import SupersingularCurves.Geometry.PointedCotangent

/-!
# The actual Picard cotangent space and dual Cech cohomology

For a given Picard representation and a fixed two-affine cover, the comparison
uses the Poincare bundle, the local-ring square-zero-point construction, and
the normalized transition cocycle. Linearity follows from naturality for all
coefficient modules. The argument for linearity generalizes the pinned
`P2mTJ.nonempty_dual_linearEquiv` proof, while retaining the particular map and
its representative formulas.

The resulting cotangent/dual-H1 equivalence is therefore tied to actual
deformations. Naturality with respect to a curve morphism, and the residue
comparison with regular differentials, are not conclusions of this file.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.PicardCohomology
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian InfinitesimalPicard
open scoped TensorProduct
open P2MW.S_AlgebraicGeometry_RelPicard_exists_trivialModDeformations_map_H1_tensor_natural
open P2MW.S_AlgebraicCurve_CurveModel_finrank_cotangentSpace_zeroSection_eq_genusFF_of_representsRelSubPic

variable {K : Type u} [Field K] {C : Scheme.{u}}
variable {c : C ⟶ Spec (CommRingCat.of K)}
variable {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c}
variable {D : RelativePic0Designation K c}
variable (h : RepresentsRelSubPic c s (algEquivZeroCut c s) D)
variable (𝒱 : C.TwoAffineOpenCover)

/-- The actual local cotangent space at the designated zero point. -/
abbrev Cotangent (D : RelativePic0Designation K c) :=
  PointedCotangent.Cotangent D.toBase ⟨D.zeroSection, D.zeroSection_toBase⟩

instance cotangentStalkAlgebra :
    Algebra K (PointedCotangent.Stalk D.toBase ⟨D.zeroSection, D.zeroSection_toBase⟩) :=
  PointedCotangent.stalkAlgebra D.toBase ⟨D.zeroSection, D.zeroSection_toBase⟩

variable (V : Type u) [AddCommGroup V] [Module K V]
  [Module Kᵐᵒᵖ V] [IsCentralScalar K V]

/-- Pull back the universal Poincare bundle at the actual square-zero point,
then take its normalized Cech cocycle. -/
def pointToCech (t : TangentPoints D.toBase D.zeroSection V) : CechH1 c 𝒱 ⊗[K] V :=
  P2mTJ2.βfun 𝒱 c s V (P2mTJ.defOf h t)

theorem pointToCech_bijective : Function.Bijective (pointToCech h 𝒱 V) := by
  constructor
  · intro t t' heq
    apply P2mTJ.defOf_injective h
    exact Quotient.sound ((P2mTJ2.βfun_eq_iff 𝒱 c s V _ _).mp heq)
  · intro z
    obtain ⟨L, rfl⟩ := P2mTJ2.βfun_surjective 𝒱 c s V z
    obtain ⟨t, ht⟩ := P2mTJ.exists_defOf_iso h L
    exact ⟨t, (P2mTJ2.βfun_eq_iff 𝒱 c s V _ _).mpr ht⟩

/-- Cotangent functionals classified by actual Poincare transition cocycles. -/
def cotangentCechEquiv : (Cotangent D →ₗ[K] V) ≃ CechH1 c 𝒱 ⊗[K] V :=
  (PointedCotangent.pointsEquiv D.toBase ⟨D.zeroSection, D.zeroSection_toBase⟩ V).trans
    (Equiv.ofBijective (pointToCech h 𝒱 V) (pointToCech_bijective h 𝒱 V))

variable {V}
variable {W : Type u} [AddCommGroup W] [Module K W]
  [Module Kᵐᵒᵖ W] [IsCentralScalar K W]

theorem pointToCech_map (φ : V →ₗ[K] W) (t : TangentPoints D.toBase D.zeroSection V) :
    pointToCech h 𝒱 W (t.map φ) =
      LinearMap.lTensor (CechH1 c 𝒱) φ (pointToCech h 𝒱 V t) := by
  change P2mTJ2.βfun 𝒱 c s W (P2mTJ.defOf h (t.map φ)) =
    LinearMap.lTensor (CechH1 c 𝒱) φ (P2mTJ2.βfun 𝒱 c s V (P2mTJ.defOf h t))
  rw [← P2mTJ2.βfun_map]
  exact (P2mTJ2.βfun_eq_iff 𝒱 c s W _ _).mpr (P2mTJ.nonempty_iso_defOf_map h φ t)

/-- Naturality in every square-zero coefficient module. -/
theorem cotangentCechEquiv_map (φ : V →ₗ[K] W) (l : Cotangent D →ₗ[K] V) :
    cotangentCechEquiv h 𝒱 W (φ ∘ₗ l) =
      LinearMap.lTensor (CechH1 c 𝒱) φ (cotangentCechEquiv h 𝒱 V l) := by
  change pointToCech h 𝒱 W
    (PointedCotangent.pointsEquiv D.toBase _ W (φ ∘ₗ l)) = _
  rw [PointedCotangent.pointsEquiv_map, pointToCech_map]
  rfl

variable (V)

/-- Additivity is forced by naturality on the product coefficient module. -/
theorem cotangentCechEquiv_add (f g : Cotangent D →ₗ[K] V) :
    cotangentCechEquiv h 𝒱 V (f + g) =
      cotangentCechEquiv h 𝒱 V f + cotangentCechEquiv h 𝒱 V g := by
  have h1 : LinearMap.fst K V V ∘ₗ f.prod g = f := LinearMap.fst_prod f g
  have h2 : LinearMap.snd K V V ∘ₗ f.prod g = g := LinearMap.snd_prod f g
  have h3 : (LinearMap.fst K V V + LinearMap.snd K V V) ∘ₗ f.prod g = f + g := by
    rw [LinearMap.add_comp, h1, h2]
  calc
    cotangentCechEquiv h 𝒱 V (f + g) =
        cotangentCechEquiv h 𝒱 V
          ((LinearMap.fst K V V + LinearMap.snd K V V) ∘ₗ f.prod g) := by rw [h3]
    _ = LinearMap.lTensor (CechH1 c 𝒱) (LinearMap.fst K V V + LinearMap.snd K V V)
        (cotangentCechEquiv h 𝒱 (V × V) (f.prod g)) := cotangentCechEquiv_map h 𝒱 _ _
    _ = LinearMap.lTensor (CechH1 c 𝒱) (LinearMap.fst K V V)
          (cotangentCechEquiv h 𝒱 (V × V) (f.prod g)) +
        LinearMap.lTensor (CechH1 c 𝒱) (LinearMap.snd K V V)
          (cotangentCechEquiv h 𝒱 (V × V) (f.prod g)) := by
      rw [LinearMap.lTensor_add, LinearMap.add_apply]
    _ = cotangentCechEquiv h 𝒱 V f + cotangentCechEquiv h 𝒱 V g := by
      rw [← cotangentCechEquiv_map, ← cotangentCechEquiv_map, h1, h2]

theorem cotangentCechEquiv_smul (a : K) (f : Cotangent D →ₗ[K] V) :
    cotangentCechEquiv h 𝒱 V (a • f) = a • cotangentCechEquiv h 𝒱 V f := by
  have hf : (a • LinearMap.id : V →ₗ[K] V) ∘ₗ f = a • f := by
    rw [LinearMap.smul_comp, LinearMap.id_comp]
  rw [← hf, cotangentCechEquiv_map, LinearMap.lTensor_smul,
    LinearMap.lTensor_id, LinearMap.smul_apply, LinearMap.id_apply]

/-- The same cocycle classification, with its proved linear structure. -/
def cotangentCechLinearEquiv : (Cotangent D →ₗ[K] V) ≃ₗ[K] CechH1 c 𝒱 ⊗[K] V where
  toEquiv := cotangentCechEquiv h 𝒱 V
  map_add' := cotangentCechEquiv_add h 𝒱 V
  map_smul' := cotangentCechEquiv_smul h 𝒱 V

/-- The tangent space of the representing Picard scheme is actual Cech H1. -/
def tangentCechEquiv : Module.Dual K (Cotangent D) ≃ₗ[K] CechH1 c 𝒱 :=
  cotangentCechLinearEquiv h 𝒱 K ≪≫ₗ TensorProduct.rid K (CechH1 c 𝒱)

/-- The map retains its actual Poincare/cocycle description. -/
theorem tangentCechEquiv_apply (l : Module.Dual K (Cotangent D)) :
    tangentCechEquiv h 𝒱 l = TensorProduct.rid K (CechH1 c 𝒱)
      (P2mTJ2.βfun 𝒱 c s K (P2mTJ.defOf h
        (PointedCotangent.pointsEquiv D.toBase ⟨D.zeroSection, D.zeroSection_toBase⟩ K l))) := rfl

/-- At a rational point on a locally finite-type scheme, the actual local
cotangent space is finite dimensional over the original base field. -/
theorem cotangent_finite [LocallyOfFiniteType D.toBase] : Module.Finite K (Cotangent D) := by
  let : IsLocallyNoetherian D.P := LocallyOfFiniteType.isLocallyNoetherian D.toBase
  let S := PointedCotangent.Stalk D.toBase ⟨D.zeroSection, D.zeroSection_toBase⟩
  have hK := P2mTJ.bijective_algebraMap_residueField D.toBase
    D.zeroSection D.zeroSection_toBase
  let e : K ≃+* IsLocalRing.ResidueField S := RingEquiv.ofBijective _ hK
  let f : Cotangent D →ₛₗ[e.symm.toRingHom] Cotangent D :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun a m => by
        change a • m = e.symm a • m
        rw [← e.apply_symm_apply a]
        change (algebraMap K (IsLocalRing.ResidueField S) (e.symm a)) • m = _
        rw [IsScalarTower.algebraMap_apply K S (IsLocalRing.ResidueField S),
          IsScalarTower.algebraMap_smul, IsScalarTower.algebraMap_smul,
          e.symm_apply_apply] }
  exact Module.Finite.of_surjective f Function.surjective_id

/-- The actual cotangent space is dual Cech H1, using evaluation into the
double dual and the Poincare/cocycle comparison above. -/
def cotangentDualCechEquiv [LocallyOfFiniteType D.toBase] :
    Cotangent D ≃ₗ[K] Module.Dual K (CechH1 c 𝒱) := by
  letI := cotangent_finite (D := D)
  exact Module.evalEquiv K (Cotangent D) ≪≫ₗ (tangentCechEquiv h 𝒱).symm.dualMap

theorem cotangentDualCechEquiv_apply [LocallyOfFiniteType D.toBase]
    (x : Cotangent D) (z : CechH1 c 𝒱) :
    cotangentDualCechEquiv h 𝒱 x z = (tangentCechEquiv h 𝒱).symm z x := rfl

/-- Evaluation agrees with the tangent vector obtained from the very same
Poincare deformation; this fixes the normalization of the dual comparison. -/
theorem cotangentDualCechEquiv_tangent [LocallyOfFiniteType D.toBase]
    (x : Cotangent D) (l : Module.Dual K (Cotangent D)) :
    cotangentDualCechEquiv h 𝒱 x (tangentCechEquiv h 𝒱 l) = l x := by
  rw [cotangentDualCechEquiv_apply, LinearEquiv.symm_apply_apply]

/-- Its value on the actual Poincare deformation classes uniquely determines
the cotangent/dual-cohomology comparison. -/
theorem cotangentDualCechEquiv_unique [LocallyOfFiniteType D.toBase]
    (e : Cotangent D →ₗ[K] Module.Dual K (CechH1 c 𝒱))
    (he : ∀ (x : Cotangent D) (l : Module.Dual K (Cotangent D)),
      e x (tangentCechEquiv h 𝒱 l) = l x) :
    e = (cotangentDualCechEquiv h 𝒱).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro z
  obtain ⟨l, rfl⟩ := (tangentCechEquiv h 𝒱).surjective z
  exact (he x l).trans (cotangentDualCechEquiv_tangent h 𝒱 x l).symm

variable {C' : Scheme.{u}} {c' : C' ⟶ Spec (CommRingCat.of K)}
  {s' : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c'}
variable {D' : RelativePic0Designation K c'}
variable (h' : RepresentsRelSubPic c' s' (algEquivZeroCut c' s') D')
variable (𝒱' : C'.TwoAffineOpenCover)
variable (f : C' ⟶ C) (hf : f ≫ c = c') (hs : s'.1 ≫ f = s.1)

/-- The actual differential of the Picard morphism induced by curve pullback. -/
def pullbackCotangent : Cotangent D' →ₗ[K] Cotangent D :=
  PointedCotangent.differential D.toBase ⟨D.zeroSection, D.zeroSection_toBase⟩
    (z := ⟨D'.zeroSection, D'.zeroSection_toBase⟩)
    (RepresentsRelSubPic.pullbackHom f hf hs h h').1
    (RepresentsRelSubPic.pullbackHom f hf hs h h').2
    (RepresentsRelSubPic.zeroSection_pullbackHom f hf hs h h')

variable {V}

/-- The Poincare deformation at the image point is the actual curve pullback
of the original Poincare deformation. -/
theorem poincareDeformation_pullback (t : TangentPoints D.toBase D.zeroSection V) :
    Nonempty ((P2mTJ.defOf h'
      (PointedCotangent.mapPoint D.toBase ⟨D.zeroSection, D.zeroSection_toBase⟩
        (z := ⟨D'.zeroSection, D'.zeroSection_toBase⟩)
        (RepresentsRelSubPic.pullbackHom f hf hs h h').1
        (RepresentsRelSubPic.pullbackHom f hf hs h h').2
        (RepresentsRelSubPic.zeroSection_pullbackHom f hf hs h h') t)).1.L ≅
      (pullbackDeformation f hf hs (P2mTJ.defOf h t)).1.L) := by
  change Nonempty ((h'.poincare.pullbackAlong
    (postComp (RepresentsRelSubPic.pullbackHom f hf hs h h') (P2mTJ.toOver t))).L ≅
    ((h.poincare.pullbackAlong (P2mTJ.toOver t)).pullbackCurve f hf hs).L)
  exact ⟨(h'.poincare.pullbackAlongPullbackAlongIso' _ _).symm ≪≫
    (Scheme.Modules.pullback _).mapIso (h'.classify_spec _ _ _).some ≪≫
    h.poincare.pullbackCurvePullbackAlongIso f hf hs (P2mTJ.toOver t)⟩

/-- The cotangent comparison is compatible with actual curve pullback,
expressed as the normalized cocycle of the pulled-back line bundle. This does
not yet identify that cocycle with a separately constructed Cech cochain map. -/
theorem cotangentCechEquiv_pullback (l : Cotangent D →ₗ[K] V) :
    cotangentCechEquiv h' 𝒱' V (l ∘ₗ pullbackCotangent h h' f hf hs) =
      P2mTJ2.βfun 𝒱' c' s' V
        (pullbackDeformation f hf hs (P2mTJ.defOf h
          (PointedCotangent.pointsEquiv D.toBase
            ⟨D.zeroSection, D.zeroSection_toBase⟩ V l))) := by
  change pointToCech h' 𝒱' V
    (PointedCotangent.pointsEquiv D'.toBase _ V (l ∘ₗ pullbackCotangent h h' f hf hs)) = _
  rw [pullbackCotangent, PointedCotangent.differential_action]
  exact (P2mTJ2.βfun_eq_iff 𝒱' c' s' V _ _).mpr
    (poincareDeformation_pullback h h' f hf hs _)

end SupersingularCurves.Geometry.PicardCohomology
