/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.PicardCech

/-!
# The actual structure-sheaf Cech map of a curve morphism

The cochain map is defined by the morphism's maps on sections on compatible
two-affine covers. Restriction compatibility proves that it descends to H1.
Its representative formula specifies the map independently of Picard data.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.CechCurvePullback
open CategoryTheory AlgebraicGeometry Opposite
open InfinitesimalPicard

variable {K : Type u} [CommRing K] {X Y : Scheme.{u}}
variable {cX : X ⟶ Spec (CommRingCat.of K)} {cY : Y ⟶ Spec (CommRingCat.of K)}
variable (f : X ⟶ Y) (hf : f ≫ cY = cX)

/-- Pullback of sections, with the algebra structures induced by the actual
structural morphisms. The commutation proof adapts upstream StageTransport. -/
def appAlgHom (U : Y.Opens) (W : X.Opens) (h : W ≤ f ⁻¹ᵁ U) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom cY U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom cX W
    Γ(Y, U) →ₐ[K] Γ(X, W) :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom cY U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom cX W
  { (f.appLE U W h).hom with
    commutes' := fun k => by
      change (f.appLE U W h).hom
        (((Scheme.ΓSpecIso (.of K)).inv ≫ cY.appLE ⊤ U le_top).hom k) =
        ((Scheme.ΓSpecIso (.of K)).inv ≫ cX.appLE ⊤ W le_top).hom k
      subst hf
      rw [← CommRingCat.comp_apply, Category.assoc, Scheme.Hom.appLE_comp_appLE] }

theorem appAlgHom_apply (U : Y.Opens) (W : X.Opens) (h : W ≤ f ⁻¹ᵁ U)
    (a : Γ(Y, U)) : appAlgHom f hf U W h a = (f.appLE U W h).hom a := rfl

/-- Section pullback commutes with restriction to smaller opens. -/
theorem app_restrict {U U' : Y.Opens} {W W' : X.Opens}
    (hU : U' ≤ U) (hW : W' ≤ W) (h : W ≤ f ⁻¹ᵁ U) (h' : W' ≤ f ⁻¹ᵁ U')
    (a : Γ(Y, U)) :
    (X.presheaf.map (homOfLE hW).op).hom ((f.appLE U W h).hom a) =
      (f.appLE U' W' h').hom ((Y.presheaf.map (homOfLE hU).op).hom a) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

variable (𝒰 : X.TwoAffineOpenCover) (𝒱 : Y.TwoAffineOpenCover)
variable (h0 : 𝒰.U0 ≤ f ⁻¹ᵁ 𝒱.U0) (h1 : 𝒰.U1 ≤ f ⁻¹ᵁ 𝒱.U1)

include h0 h1 in
theorem overlap_le : 𝒰.U0 ⊓ 𝒰.U1 ≤ f ⁻¹ᵁ (𝒱.U0 ⊓ 𝒱.U1) :=
  fun _ hx => ⟨h0 hx.1, h1 hx.2⟩

/-- Pullback on degree-zero cochains, using the two actual section maps. -/
def degreeZero :
    ((𝒱.structureSheafSections cY).M0 × (𝒱.structureSheafSections cY).M1) →ₗ[K]
      ((𝒰.structureSheafSections cX).M0 × (𝒰.structureSheafSections cX).M1) :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom cY 𝒱.U0
  letI := Scheme.TwoAffineOpenCover.algebraOfHom cY 𝒱.U1
  letI := Scheme.TwoAffineOpenCover.algebraOfHom cX 𝒰.U0
  letI := Scheme.TwoAffineOpenCover.algebraOfHom cX 𝒰.U1
  (appAlgHom f hf 𝒱.U0 𝒰.U0 h0).toLinearMap.prodMap
    (appAlgHom f hf 𝒱.U1 𝒰.U1 h1).toLinearMap

/-- Pullback on overlap sections. -/
def overlap : (𝒱.structureSheafSections cY).M01 →ₗ[K]
    (𝒰.structureSheafSections cX).M01 :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom cY (𝒱.U0 ⊓ 𝒱.U1)
  letI := Scheme.TwoAffineOpenCover.algebraOfHom cX (𝒰.U0 ⊓ 𝒰.U1)
  (appAlgHom f hf (𝒱.U0 ⊓ 𝒱.U1) (𝒰.U0 ⊓ 𝒰.U1)
    (overlap_le f 𝒰 𝒱 h0 h1)).toLinearMap

theorem overlap_apply (a : (𝒱.structureSheafSections cY).M01) :
    overlap f hf 𝒰 𝒱 h0 h1 a =
      (f.appLE (𝒱.U0 ⊓ 𝒱.U1) (𝒰.U0 ⊓ 𝒰.U1)
        (overlap_le f 𝒰 𝒱 h0 h1)).hom a := rfl

/-- The actual cochain differential commutes with the morphism's pullback. -/
theorem cechDiff_comm :
    (𝒰.structureSheafSections cX).cechDiff ∘ₗ degreeZero f hf 𝒰 𝒱 h0 h1 =
      overlap f hf 𝒰 𝒱 h0 h1 ∘ₗ (𝒱.structureSheafSections cY).cechDiff := by
  apply LinearMap.ext
  intro z
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    (𝒰.structureSheafSections cX).cechDiff_apply,
    (𝒱.structureSheafSections cY).cechDiff_apply]
  change (1 : Γ(X, 𝒰.U0 ⊓ 𝒰.U1)) •
      (X.presheaf.map (homOfLE inf_le_right).op).hom ((f.appLE _ _ h1).hom z.2) -
      (X.presheaf.map (homOfLE inf_le_left).op).hom ((f.appLE _ _ h0).hom z.1) =
    (f.appLE _ _ (overlap_le f 𝒰 𝒱 h0 h1)).hom
      ((1 : Γ(Y, 𝒱.U0 ⊓ 𝒱.U1)) •
        (Y.presheaf.map (homOfLE inf_le_right).op).hom z.2 -
        (Y.presheaf.map (homOfLE inf_le_left).op).hom z.1)
  simp only [one_smul, map_sub]
  exact congrArg₂ (· - ·)
    (app_restrict f inf_le_right inf_le_right h1 (overlap_le f 𝒰 𝒱 h0 h1) z.2)
    (app_restrict f inf_le_left inf_le_left h0 (overlap_le f 𝒰 𝒱 h0 h1) z.1)

/-- H1 pullback induced by the actual maps on structure-sheaf sections. -/
def onH1 : (𝒱.structureSheafSections cY).H1 →ₗ[K] (𝒰.structureSheafSections cX).H1 :=
  TwoChartCech.cokerMap (𝒱.structureSheafSections cY).cechDiff
    (𝒰.structureSheafSections cX).cechDiff (degreeZero f hf 𝒰 𝒱 h0 h1)
    (overlap f hf 𝒰 𝒱 h0 h1) (cechDiff_comm f hf 𝒰 𝒱 h0 h1)

/-- Formula on every actual overlap representative. -/
theorem onH1_mk (a : (𝒱.structureSheafSections cY).M01) :
    onH1 f hf 𝒰 𝒱 h0 h1 (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (overlap f hf 𝒰 𝒱 h0 h1 a) := rfl

/-- The section formula determines the cohomology map uniquely. -/
theorem onH1_unique
    (e : (𝒱.structureSheafSections cY).H1 →ₗ[K] (𝒰.structureSheafSections cX).H1)
    (he : ∀ a : (𝒱.structureSheafSections cY).M01,
      e (Submodule.Quotient.mk a) =
        Submodule.Quotient.mk (overlap f hf 𝒰 𝒱 h0 h1 a)) :
    e = onH1 f hf 𝒰 𝒱 h0 h1 := by
  apply LinearMap.ext
  intro q
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact he a

end SupersingularCurves.Geometry.CechCurvePullback
