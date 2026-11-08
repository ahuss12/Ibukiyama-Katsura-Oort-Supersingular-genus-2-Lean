/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.EllipticTorsionLiftingResidualCoordinates
import SupersingularCurves.Geometry.PointedCotangentHopfRestriction

/-! # Actual global endomorphisms on the Frobenius-kernel Hopf algebra

Every actual elliptic group homomorphism induces a genuine Hopf map on the
actual Frobenius kernel. Its scheme square and its cotangent comparison are
proved from its action on all test algebras.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SupersingularCurves.Geometry.EllipticTorsionRealization.FrobeniusKernelHopf
open CategoryTheory AlgebraicGeometry NeronModelInfra PointedCotangent
variable {K : Type u} [Field K] [IsAlgClosed K]
  {p : ℕ} [Fact p.Prime] [CharP K p] {E E' : AbelianVariety K 1}
  (HF : FrobeniusKernelHopf p E) (HF' : FrobeniusKernelHopf p E')

/-- Postcomposition on actual kernel points. -/
def groupHomPoints (f : E.group ⟶ E'.group) (T : Type u) [CommRing T] [Algebra K T]
    (x : WithConv (HF.Coord →ₐ[K] T)) : WithConv (HF'.Coord →ₐ[K] T) :=
  (HF'.points T).symm ⟨schemeHomOverComp (HF.points T x).val
      ⟨f.hom.hom.left, f.hom.hom.w⟩, by
    obtain ⟨q, hq⟩ := (HF.points T x).property
    refine ⟨q ≫ onFrobeniusKernel p f, ?_⟩
    change (q ≫ onFrobeniusKernel p f) ≫ frobeniusKernelInclusion p E' =
      (HF.points T x).val.1 ≫ f.hom.hom.left
    rw [Category.assoc, onFrobeniusKernel_inclusion, ← Category.assoc, hq]⟩

theorem groupHomPoints_comparison (f : E.group ⟶ E'.group)
    (T : Type u) [CommRing T] [Algebra K T] (x : WithConv (HF.Coord →ₐ[K] T)) :
    (HF'.points T (HF.groupHomPoints HF' f T x)).val =
      schemeHomOverComp (HF.points T x).val ⟨f.hom.hom.left, f.hom.hom.w⟩ :=
  congrArg Subtype.val ((HF'.points T).apply_symm_apply _)

theorem groupHomPoints_natural (f : E.group ⟶ E'.group)
    (T T' : Type u) [CommRing T] [Algebra K T] [CommRing T'] [Algebra K T']
    (a : T →ₐ[K] T') (x : WithConv (HF.Coord →ₐ[K] T)) :
    (HF.groupHomPoints HF' f T' (.toConv (a.comp x.ofConv))).ofConv =
      a.comp (HF.groupHomPoints HF' f T x).ofConv := by
  have hh : HF.groupHomPoints HF' f T' (.toConv (a.comp x.ofConv)) =
      .toConv (a.comp (HF.groupHomPoints HF' f T x).ofConv) := by
    apply (HF'.points T').injective
    apply Subtype.ext
    apply Subtype.ext
    rw [HF'.points_natural, groupHomPoints_comparison, groupHomPoints_comparison]
    change (HF.points T' (.toConv (a.comp x.ofConv))).val.1 ≫ f.hom.hom.left =
      Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (HF.points T x).val.1 ≫ f.hom.hom.left
    rw [HF.points_natural, Category.assoc]
  exact congrArg WithConv.ofConv hh

theorem groupHomPoints_mul (f : E.group ⟶ E'.group)
    (T : Type u) [CommRing T] [Algebra K T] (x y : WithConv (HF.Coord →ₐ[K] T)) :
    HF.groupHomPoints HF' f T (x * y) =
      HF.groupHomPoints HF' f T x * HF.groupHomPoints HF' f T y := by
  apply (HF'.points T).injective
  apply Subtype.ext
  rw [HF'.points_mul, groupHomPoints_comparison, groupHomPoints_comparison,
    groupHomPoints_comparison, HF.points_mul]
  exact GroupScheme.torsionRealization_map_mul f _ _ _

theorem groupHomPoints_one (f : E.group ⟶ E'.group)
    (T : Type u) [CommRing T] [Algebra K T] : HF.groupHomPoints HF' f T 1 = 1 := by
  have h := HF.groupHomPoints_mul HF' f T 1 1
  rw [one_mul] at h
  exact mul_left_cancel (h.symm.trans (mul_one _).symm)

/-- A genuine Hopf pullback induced by the actual group map. -/
theorem exists_ofGroupHom (f : E.group ⟶ E'.group) :
    ∃ r : HF'.Coord →ₐc[K] HF.Coord,
      ∀ (T : Type u) [CommRing T] [Algebra K T] (x : WithConv (HF.Coord →ₐ[K] T)),
        (HF.groupHomPoints HF' f T x).ofConv = x.ofConv.comp r.toAlgHom :=
  BialgHom.exists_comp_eq_of_natural_of_map_mul (HF.groupHomPoints HF' f)
    (HF.groupHomPoints_natural HF' f) (HF.groupHomPoints_mul HF' f)
    (HF.groupHomPoints_one HF' f)

def ofGroupHom (f : E.group ⟶ E'.group) : HF'.Coord →ₐc[K] HF.Coord :=
  Classical.choose (HF.exists_ofGroupHom HF' f)

theorem ofGroupHom_points (f : E.group ⟶ E'.group)
    (T : Type u) [CommRing T] [Algebra K T] (x : WithConv (HF.Coord →ₐ[K] T)) :
    (HF'.points T (.toConv (x.ofConv.comp (HF.ofGroupHom HF' f).toAlgHom))).val =
      schemeHomOverComp (HF.points T x).val ⟨f.hom.hom.left, f.hom.hom.w⟩ := by
  have h := Classical.choose_spec (HF.exists_ofGroupHom HF' f) T x
  rw [ofGroupHom, ← h]
  exact HF.groupHomPoints_comparison HF' f T x

@[reassoc]
theorem ofGroupHom_spec (f : E.group ⟶ E'.group) :
    Spec.map (CommRingCat.ofHom (HF.ofGroupHom HF' f).toAlgHom.toRingHom) ≫ HF'.specIso.hom =
      HF.specIso.hom ≫ onFrobeniusKernel p f := by
  apply (cancel_mono (frobeniusKernelInclusion p E')).mp
  have h := congrArg Subtype.val (HF.ofGroupHom_points HF' f HF.Coord
    (.toConv (AlgHom.id K HF.Coord)))
  rw [HF'.points_scheme] at h
  change Spec.map (CommRingCat.ofHom (HF.ofGroupHom HF' f).toAlgHom.toRingHom) ≫
      HF'.specIso.hom ≫ frobeniusKernelInclusion p E' =
    (HF.points HF.Coord (.toConv (AlgHom.id K HF.Coord))).val.1 ≫ f.hom.hom.left at h
  rw [HF.points_scheme] at h
  have hid : Spec.map (CommRingCat.ofHom (AlgHom.id K HF.Coord).toRingHom) =
      𝟙 (Spec (CommRingCat.of HF.Coord)) := by
    change Spec.map (𝟙 (CommRingCat.of HF.Coord)) = _
    exact Spec.map_id _
  rw [hid] at h
  simpa only [AlgHom.id_toRingHom, CommRingCat.ofHom_id, Spec.map_id,
    Category.id_comp, Category.assoc, onFrobeniusKernel_inclusion] using h

variable {HF'}

theorem endScheme_ofGroupHom (f : E.group ⟶ E.group) :
    HF.endScheme (HF.ofGroupHom HF f) = onFrobeniusKernel p f := by
  rw [endScheme, HF.ofGroupHom_spec]
  simp only [Iso.inv_hom_id_assoc]

@[reassoc]
theorem ofGroupHom_over (f : E.group ⟶ E.group) :
    HF.endScheme (HF.ofGroupHom HF f) ≫ frobeniusKernelBase p E =
      frobeniusKernelBase p E := by
  rw [HF.endScheme_ofGroupHom]
  exact restrictFrobeniusKernel_over p _ _ _

@[reassoc]
theorem ofGroupHom_inclusion (f : E.group ⟶ E.group) :
    HF.endScheme (HF.ofGroupHom HF f) ≫ frobeniusKernelInclusion p E =
      frobeniusKernelInclusion p E ≫ f.hom.hom.left := by
  rw [HF.endScheme_ofGroupHom, onFrobeniusKernel_inclusion]

@[reassoc]
theorem ofGroupHom_zero (f : E.group ⟶ E.group) :
    (frobeniusKernelZero p E).1 ≫ HF.endScheme (HF.ofGroupHom HF f) =
      (frobeniusKernelZero p E).1 := by
  apply (cancel_mono (frobeniusKernelInclusion p E)).mp
  rw [Category.assoc, HF.ofGroupHom_inclusion, ← Category.assoc,
    frobeniusKernelZero_inclusion, GroupScheme.zero_natural]

/-- The actual restriction has precisely the ambient differential scalar. -/
theorem ofGroupHom_cotangentMap (f : E.group ⟶ E.group)
    (hs : (GroupScheme.zero E.group).1 ≫ f.hom.hom.left = (GroupScheme.zero E.group).1)
    (a : K)
    (hd : differential E.group.X.hom (GroupScheme.zero E.group)
      f.hom.hom.left f.hom.hom.w hs = a • LinearMap.id) :
    HeightOneHopf.cotangentMap (HF.ofGroupHom HF f) = a • LinearMap.id := by
  apply HF.coordinate_eq_smul_of_ambient_differential (HF.ofGroupHom HF f)
    (HF.endScheme (HF.ofGroupHom HF f)) (HF.ofGroupHom_over f) (HF.ofGroupHom_zero f)
    ?_ f.hom.hom.left f.hom.hom.w hs (HF.ofGroupHom_inclusion f).symm a hd
  simp only [endScheme, Category.assoc, Iso.hom_inv_id_assoc]

end SupersingularCurves.Geometry.EllipticTorsionRealization.FrobeniusKernelHopf
