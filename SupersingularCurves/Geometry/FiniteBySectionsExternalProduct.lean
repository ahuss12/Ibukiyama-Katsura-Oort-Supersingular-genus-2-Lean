/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_FiniteBySections_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_projPresentation_pullback_sigma_eq_toProj_eq
import Theorems.Thm_AlgebraicGeometry_isAffineOpen_pullback_fst_preimage_inf_snd_preimage_and_closure_eq_top

/-!
# Finite projective presentations on a product

The exterior tensor product of two bundles finite by sections is again finite
by sections. The proof uses the pinned FLT Segre-chart construction, but the
affine charts are products of affine charts on the two different schemes.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SupersingularCurves.Geometry
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_tensor.P2mSegre

/-- An actual finite projective presentation on each factor constructs one for
the exterior tensor product over an affine base. -/
theorem finiteBySections_externalProduct
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) (g : Y ⟶ Spec (.of R))
    (L : X.Modules) (M : Y.Modules)
    (hL : L.FiniteBySections f) (hM : M.FiniteBySections g) :
    ((Scheme.Modules.pullback (pullback.fst f g)).obj L ⊗
      (Scheme.Modules.pullback (pullback.snd f g)).obj M).FiniteBySections
        (pullback.fst f g ≫ f) := by
  obtain ⟨N, P, hP⟩ := hL
  obtain ⟨N', Q, hQ⟩ := hM
  obtain ⟨P', _, heP⟩ := P.exists_projPresentation_pullback_sigma_eq_toProj_eq (pullback.fst f g)
  obtain ⟨Q₀, _, heQ⟩ := Q.exists_projPresentation_pullback_sigma_eq_toProj_eq (pullback.snd f g)
  let Q' : ((Scheme.Modules.pullback (pullback.snd f g)).obj M).ProjPresentation
      (pullback.fst f g ≫ f) N' :=
    { Q₀ with toProj_π := Q₀.toProj_π.trans pullback.condition.symm }
  obtain ⟨S, hσ, hW⟩ := exists_segre P' Q'
  refine ⟨_, S, ?_⟩
  rw [IsFinite.iff_isProper_and_isAffineHom]
  constructor
  · letI : IsProper f := isProper_of_isFinite P hP
    letI : IsProper g := isProper_of_isFinite Q hQ
    haveI : IsProper (S.toProj ≫ ProjSpace.π R (KK N N')) := by
      rw [S.toProj_π]
      infer_instance
    exact IsProper.of_comp S.toProj (ProjSpace.π R (KK N N'))
  · rw [HasAffineProperty.iff_of_iSup_eq_top (P := @IsAffineHom)
      (fun k => (⟨DD R (KK N N') k, isAffineOpen_DD R (KK N N') k⟩ :
        (PP R (KK N N')).affineOpens))
      (iSup_DD (R := R) (N := KK N N'))]
    intro k
    change IsAffineOpen (chart S k)
    rw [le_antisymm (chart_segre_le S hσ hW k) (hW k)]
    have hcharts : WW P' Q' k =
        pullback.fst f g ⁻¹ᵁ chart P (idx N N' k).1 ⊓
          pullback.snd f g ⁻¹ᵁ chart Q (idx N N' k).2 := by
      change P'.toProj ⁻¹ᵁ DD R N (idx N N' k).1 ⊓
        Q₀.toProj ⁻¹ᵁ DD R N' (idx N N' k).2 = _
      rw [heP, heQ]
      rfl
    rw [hcharts]
    exact (isAffineOpen_pullback_fst_preimage_inf_snd_preimage_and_closure_eq_top f g
      (isAffineOpen_chart P hP _) (isAffineOpen_chart Q hQ _)).1

end SupersingularCurves.Geometry
