/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.PointedCotangentHopfScalar
import SupersingularCurves.Geometry.PointedCotangentKernel

/-! # Restricting actual cotangent scalars to the Frobenius-kernel Hopf algebra -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SupersingularCurves.Geometry.PointedCotangent
open CategoryTheory AlgebraicGeometry NeronModelInfra
variable {K : Type u} [Field K]

/-- The scalar differential of an ambient endomorphism restricts to every
stable pointed subscheme. Cotangent surjectivity follows from its monomorphism. -/
theorem differential_eq_smul_of_mono_square
    {X Y : Scheme.{u}} {c : X ⟶ Spec (CommRingCat.of K)}
    {d : Y ⟶ Spec (CommRingCat.of K)}
    {s : SchemeHomOver (𝟙 _) c} {z : SchemeHomOver (𝟙 _) d}
    (f : X ⟶ X) (hf : f ≫ c = c) (hs : s.1 ≫ f = s.1)
    (g : Y ⟶ Y) (hg : g ≫ d = d) (hz : z.1 ≫ g = z.1)
    (i : X ⟶ Y) [Mono i] (hi : i ≫ d = c) (his : s.1 ≫ i = z.1)
    (hcomm : i ≫ g = f ≫ i) (a : K)
    (hd : differential d z g hg hz = a • LinearMap.id) :
    differential c s f hf hs = a • LinearMap.id := by
  have H := differential_square f hf hs g hg hz i hi his i hi his hcomm
  apply LinearMap.ext
  intro ω
  obtain ⟨ω', rfl⟩ := differential_surjective_of_mono c s i hi his ω
  have hh := LinearMap.congr_fun H ω'
  simpa only [hd, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.id_apply, map_smul] using hh.symm

end SupersingularCurves.Geometry.PointedCotangent

namespace SupersingularCurves.Geometry.EllipticTorsionRealization.FrobeniusKernelHopf
open CategoryTheory AlgebraicGeometry NeronModelInfra PointedCotangent
variable {K : Type u} [Field K] [IsAlgClosed K]
  {p : ℕ} [Fact p.Prime] [CharP K p] {E : AbelianVariety K 1}
  (HF : FrobeniusKernelHopf p E)

/-- The scalar of the actual ambient elliptic endomorphism is the scalar of
the actual restricted Hopf-coordinate cotangent map. -/
theorem coordinate_eq_smul_of_ambient_differential
    (φ : HF.Coord →ₐc[K] HF.Coord)
    (f : frobeniusKernel p E ⟶ frobeniusKernel p E)
    (hf : f ≫ frobeniusKernelBase p E = frobeniusKernelBase p E)
    (hs : (frobeniusKernelZero p E).1 ≫ f = (frobeniusKernelZero p E).1)
    (hφ : HF.specIso.hom ≫ f =
      AffineAugmentation.schemeMap φ.toAlgHom ≫ HF.specIso.hom)
    (g : E.group.X.left ⟶ E.group.X.left) (hg : g ≫ E.group.X.hom = E.group.X.hom)
    (hz : (GroupScheme.zero E.group).1 ≫ g = (GroupScheme.zero E.group).1)
    (hres : frobeniusKernelInclusion p E ≫ g = f ≫ frobeniusKernelInclusion p E)
    (a : K)
    (hd : differential E.group.X.hom (GroupScheme.zero E.group) g hg hz = a • LinearMap.id) :
    HeightOneHopf.cotangentMap φ = a • LinearMap.id := by
  apply (HF.differential_eq_smul_iff_coordinate φ f hf hs hφ a).mp
  exact differential_eq_smul_of_mono_square f hf hs g hg hz
    (frobeniusKernelInclusion p E) (frobeniusKernelInclusion_over p E)
    (frobeniusKernelZero_inclusion p E) hres a hd

end SupersingularCurves.Geometry.EllipticTorsionRealization.FrobeniusKernelHopf
