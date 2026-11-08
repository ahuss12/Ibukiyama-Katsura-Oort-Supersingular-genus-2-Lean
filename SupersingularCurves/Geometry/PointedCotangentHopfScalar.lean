/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.PointedCotangentHopfAffine
import SupersingularCurves.Geometry.EllipticTorsionLiftingCotangent

/-! # Scalar coordinate differentials agree with actual local cotangent differentials -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SupersingularCurves.Geometry.PointedCotangent
open CategoryTheory AlgebraicGeometry NeronModelInfra

variable {K : Type u} [Field K]

/-- A scalar local differential acts by that scalar on every actual square-zero point. -/
theorem mapPoint_eq_map_smul_of_differential_eq_smul
    {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of K))
    (s : SchemeHomOver (𝟙 _) c) (f : X ⟶ X) (hf : f ≫ c = c)
    (hs : s.1 ≫ f = s.1) (a : K)
    (hd : differential c s f hf hs = a • LinearMap.id)
    {V : Type u} [AddCommGroup V] [Module K V]
    [Module Kᵐᵒᵖ V] [IsCentralScalar K V] (t : TangentPoints c s.1 V) :
    mapPoint c s f hf hs t = t.map (a • LinearMap.id) := by
  obtain ⟨l, rfl⟩ := (pointsEquiv c s V).surjective t
  rw [← differential_action, hd, ← pointsEquiv_map]
  congr 1
  ext x
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, map_smul]

/-- A genuine pointed scheme isomorphism preserves the scalar value of an
endomorphism on the local cotangent space. -/
theorem differential_eq_smul_iff_of_iso_conj
    {X Y : Scheme.{u}} {c : X ⟶ Spec (CommRingCat.of K)}
    {d : Y ⟶ Spec (CommRingCat.of K)}
    {s : SchemeHomOver (𝟙 _) c} {z : SchemeHomOver (𝟙 _) d}
    (f : X ⟶ X) (hf : f ≫ c = c) (hs : s.1 ≫ f = s.1)
    (g : Y ⟶ Y) (hg : g ≫ d = d) (hz : z.1 ≫ g = z.1)
    (e : X ≅ Y) (he : e.hom ≫ d = c) (hes : s.1 ≫ e.hom = z.1)
    (hcomm : e.hom ≫ g = f ≫ e.hom) (a : K) :
    differential c s f hf hs = a • LinearMap.id ↔
      differential d z g hg hz = a • LinearMap.id := by
  have H := differential_square f hf hs g hg hz e.hom he hes e.hom he hes hcomm
  constructor
  · intro hd
    apply LinearMap.ext
    intro ω
    apply (isoEquiv e he hes).injective
    change differential c s e.hom he hes (differential d z g hg hz ω) =
      differential c s e.hom he hes ((a • LinearMap.id) ω)
    have hh := LinearMap.congr_fun H ω
    simpa only [hd, LinearMap.comp_apply, LinearMap.smul_apply,
      LinearMap.id_apply, map_smul] using hh
  · intro hd
    apply LinearMap.ext
    intro ω
    obtain ⟨ω', rfl⟩ := (isoEquiv e he hes).surjective ω
    change differential c s f hf hs (differential c s e.hom he hes ω') =
      (a • LinearMap.id) (differential c s e.hom he hes ω')
    have hh := LinearMap.congr_fun H ω'
    simpa only [hd, LinearMap.comp_apply, LinearMap.smul_apply,
      LinearMap.id_apply, map_smul] using hh.symm

namespace AffineAugmentation
variable {H : Type u} [CommRing H] [Algebra K H] (π : H →ₐ[K] K)
variable (φ : H →ₐ[K] H) (hφ : ∀ x, π (φ x) = π x)

/-- The actual scheme endomorphism associated to the coordinate map. -/
abbrev schemeMap := Spec.map (CommRingCat.ofHom φ.toRingHom)

theorem schemeMap_over : schemeMap φ ≫ structureMap (K := K) (H := H) = structureMap (K := K) (H := H) :=
  (AffineInvariantDerivation.point K φ).2

include hφ in
theorem schemeMap_point : (sectionPoint π).1 ≫ schemeMap φ = (sectionPoint π).1 := by
  change Spec.map (CommRingCat.ofHom π.toRingHom) ≫
    Spec.map (CommRingCat.ofHom φ.toRingHom) = Spec.map (CommRingCat.ofHom π.toRingHom)
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext x
  exact hφ x

/-- The genuine augmentation-ideal quotient map induced by the coordinate map. -/
def coordinateMap : CoordinateCotangent π →ₗ[K] CoordinateCotangent π :=
  Ideal.mapCotangent _ _ φ (fun x hx => (hφ x).trans hx)

variable {V : Type u} [AddCommGroup V] [Module K V]
  [Module Kᵐᵒᵖ V] [IsCentralScalar K V]

theorem lift_comp (l : CoordinateCotangent π →ₗ[K] V) :
    (lift π l).comp φ = lift π (l ∘ₗ coordinateMap π φ hφ) := by
  apply lift_unique
  · intro x
    rw [AlgHom.comp_apply, fst_lift]
    exact hφ x
  · intro x
    change (lift π l (φ x)).snd = _
    have hx : φ x ∈ RingHom.ker π := (hφ x).trans x.2
    rw [snd_lift π l ⟨φ x, hx⟩]
    rfl

theorem coordinatePoint_end_action (l : CoordinateCotangent π →ₗ[K] V) :
    mapPoint (structureMap (H := H)) (sectionPoint π) (schemeMap φ)
      (schemeMap_over φ) (schemeMap_point π φ hφ) (coordinatePoint π l) =
        coordinatePoint π (l ∘ₗ coordinateMap π φ hφ) := by
  apply TangentPoints.ext
  change Spec.map (CommRingCat.ofHom (lift π l).toRingHom) ≫
    Spec.map (CommRingCat.ofHom φ.toRingHom) =
      Spec.map (CommRingCat.ofHom (lift π (l ∘ₗ coordinateMap π φ hφ)).toRingHom)
  rw [← Spec.map_comp, ← lift_comp]
  rfl

local instance coordinateOppositeModule : Module Kᵐᵒᵖ (CoordinateCotangent π) :=
  Module.compHom _ (RingEquiv.toOpposite K).symm.toRingHom
local instance coordinateCentralScalar : IsCentralScalar K (CoordinateCotangent π) :=
  ⟨fun _ _ => rfl⟩
local instance localOppositeModule :
    Module Kᵐᵒᵖ (Cotangent (structureMap (H := H)) (sectionPoint π)) :=
  Module.compHom _ (RingEquiv.toOpposite K).symm.toRingHom
local instance localCentralScalar :
    IsCentralScalar K (Cotangent (structureMap (H := H)) (sectionPoint π)) :=
  ⟨fun _ _ => rfl⟩

/-- Scalar action agrees in the independently defined global augmentation
quotient and the genuine local stalk cotangent space. -/
theorem differential_spec_eq_smul_iff (a : K) :
    differential (structureMap (H := H)) (sectionPoint π) (schemeMap φ)
      (schemeMap_over φ) (schemeMap_point π φ hφ) = a • LinearMap.id ↔
        coordinateMap π φ hφ = a • LinearMap.id := by
  constructor
  · intro hd
    have ht := mapPoint_eq_map_smul_of_differential_eq_smul
      (structureMap (H := H)) (sectionPoint π) (schemeMap φ)
      (schemeMap_over φ) (schemeMap_point π φ hφ) a hd
      (coordinatePoint π (LinearMap.id : CoordinateCotangent π →ₗ[K] CoordinateCotangent π))
    rw [coordinatePoint_end_action π φ hφ, ← coordinatePoint_map] at ht
    apply coordinatePoint_injective π
    simpa only [LinearMap.id_comp, LinearMap.comp_id] using ht
  · intro hd
    let C := Cotangent (structureMap (H := H)) (sectionPoint π)
    let t := pointsEquiv (structureMap (H := H)) (sectionPoint π) C LinearMap.id
    obtain ⟨l, hl⟩ := coordinatePoint_surjective π t
    apply (pointsEquiv (structureMap (H := H)) (sectionPoint π) C).injective
    rw [differential, Equiv.apply_symm_apply]
    change mapPoint (structureMap (H := H)) (sectionPoint π) (schemeMap φ)
      (schemeMap_over φ) (schemeMap_point π φ hφ) t = _
    rw [← hl, coordinatePoint_end_action π φ hφ, hd]
    have he : l ∘ₗ (a • LinearMap.id) = (a • LinearMap.id : C →ₗ[K] C) ∘ₗ l := by
      ext x
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, map_smul]
    rw [he, coordinatePoint_map, hl]
    simpa only [LinearMap.comp_id] using
      (pointsEquiv_map (structureMap (H := H)) (sectionPoint π)
        (a • LinearMap.id : C →ₗ[K] C) (LinearMap.id : C →ₗ[K] C)).symm

end AffineAugmentation

/-- For actual Hopf endomorphisms, the coordinate Hopf cotangent and the genuine
local differential have exactly the same scalar action. -/
theorem hopf_differential_spec_eq_smul_iff
    {H : Type u} [CommRing H] [HopfAlgebra K H] [Module.Finite K H]
    (φ : H →ₐc[K] H) (a : K) :
    differential (AffineAugmentation.structureMap (H := H))
      (AffineAugmentation.sectionPoint (Bialgebra.counitAlgHom K H))
      (AffineAugmentation.schemeMap φ.toAlgHom)
      (AffineAugmentation.schemeMap_over φ.toAlgHom)
      (AffineAugmentation.schemeMap_point (Bialgebra.counitAlgHom K H) φ.toAlgHom
        (fun x => CoalgHomClass.counit_comp_apply φ x)) = a • LinearMap.id ↔
      HeightOneHopf.cotangentMap φ = a • LinearMap.id :=
  AffineAugmentation.differential_spec_eq_smul_iff (Bialgebra.counitAlgHom K H)
    φ.toAlgHom (fun x => CoalgHomClass.counit_comp_apply φ x) a

end SupersingularCurves.Geometry.PointedCotangent

namespace SupersingularCurves.Geometry.EllipticTorsionRealization.FrobeniusKernelHopf
open CategoryTheory AlgebraicGeometry NeronModelInfra PointedCotangent
variable {K : Type u} [Field K] [IsAlgClosed K]
  {p : ℕ} [Fact p.Prime] [CharP K p] {E : AbelianVariety K 1}
  (HF : FrobeniusKernelHopf p E)

/-- On the actual Frobenius kernel, the local geometric derivative and the
coordinate Hopf cotangent map have exactly the same scalar. -/
theorem differential_eq_smul_iff_coordinate
    (φ : HF.Coord →ₐc[K] HF.Coord)
    (f : frobeniusKernel p E ⟶ frobeniusKernel p E)
    (hf : f ≫ frobeniusKernelBase p E = frobeniusKernelBase p E)
    (hs : (frobeniusKernelZero p E).1 ≫ f = (frobeniusKernelZero p E).1)
    (hcomm : HF.specIso.hom ≫ f =
      AffineAugmentation.schemeMap φ.toAlgHom ≫ HF.specIso.hom) (a : K) :
    differential (frobeniusKernelBase p E) (frobeniusKernelZero p E) f hf hs =
      a • LinearMap.id ↔ HeightOneHopf.cotangentMap φ = a • LinearMap.id := by
  have hover : HF.specIso.hom ≫ frobeniusKernelBase p E =
      AffineAugmentation.structureMap (H := HF.Coord) := by
    rw [← frobeniusKernelInclusion_over]
    exact HF.specIso_over
  have H := differential_eq_smul_iff_of_iso_conj
    (AffineAugmentation.schemeMap φ.toAlgHom)
    (AffineAugmentation.schemeMap_over φ.toAlgHom)
    (AffineAugmentation.schemeMap_point (Bialgebra.counitAlgHom K HF.Coord) φ.toAlgHom
      (fun x => CoalgHomClass.counit_comp_apply φ x))
    f hf hs HF.specIso hover HF.counit_spec hcomm a
  exact H.symm.trans (hopf_differential_spec_eq_smul_iff φ a)

end SupersingularCurves.Geometry.EllipticTorsionRealization.FrobeniusKernelHopf
