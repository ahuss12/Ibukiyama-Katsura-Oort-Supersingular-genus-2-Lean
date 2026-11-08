/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.AbelianTateRiemannForm
import Theorems.Thm_AlgebraicGeometry_RiemannForm_isLevelPairingValue_of_isLevelPairingValue_pushPt_of_iso_pullback

/-! # Pullback of the actual Riemann level pairing across varieties -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SupersingularCurves.Geometry.AbelianTate
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open RelativeGroupLaw AlgebraicGeometry.RiemannForm
open P2MW.S_AlgebraicGeometry_RiemannForm_isLevelPairingValue_of_isLevelPairingValue_pushPt_of_iso_pullback
open RFFunct29.Mod LevelAdjoint29
open scoped CategoryTheory.MonObj

variable {K : Type} [Field K]

/-- Pulling back an actual line bundle pulls back its level pairing along the
actual map of group-scheme points. The varieties may be different. -/
theorem isLevelPairingValue_pullback
    {A B : Scheme} {f : A ⟶ Spec (CommRingCat.of K)}
    {g : B ⟶ Spec (CommRingCat.of K)}
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (LB : RelativeGroupLaw K g)
    (φ : A ⟶ B) (hφ : φ ≫ g = f)
    (hφhom : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of K))
      (P Q : SchemeHomOver t f),
      CerednikDrinfeld.QM.mapPt φ hφ (L.mul t P Q) =
        LB.mul t (CerednikDrinfeld.QM.mapPt φ hφ P)
          (CerednikDrinfeld.QM.mapPt φ hφ Q))
    (M : B.Modules) (n : ℕ) (P Q : L.AlgPoints hc K) (hP : n • P = 0)
    (c : K)
    (h : IsLevelPairingValue g LB M n
      (CerednikDrinfeld.QM.mapPt φ hφ (AlgPoints.toPoint P))
      (CerednikDrinfeld.QM.mapPt φ hφ (AlgPoints.toPoint Q)) c) :
    IsLevelPairingValue f L ((Scheme.Modules.pullback φ).obj M) n
      (AlgPoints.toPoint P) (AlgPoints.toPoint Q) c := by
  have hxA := RFFunct29.Geom.hxA L hc n P hP
  have sN := RFFunct29.Geom.nsmul_comm L LB φ hφ hφhom n
  have sP := RFFunct29.Geom.translation_comm L hc LB φ hφ hφhom P
  have sQ := RFFunct29.Geom.translation_comm L hc LB φ hφ hφhom Q
  obtain ⟨hxB, βB, hσB⟩ := h
  change IsConstScalar g (sig hxB βB).hom c at hσB
  have hpull : IsConstScalar f
      (sig hxA ((sq sN).app _ ≪≫ (Scheme.Modules.pullback φ).mapIso βB ≪≫
        ((sq sN).app M).symm)).hom c := by
    rw [sig_pullback_hom φ hxA hxB sN sP βB]
    exact isConstScalar_conj f ((sq sN).app M)
      (isConstScalar_pullback f g φ hφ hσB)
  have hconj := isConstScalar_sig_conj f hxA _ ((sq sQ).app M)
    (Iso.refl ((Scheme.Modules.pullback φ).obj M)) hpull
  exact ⟨hxA, _, hconj⟩

@[simp] theorem pointsGeometricEquiv_map {g h : ℕ}
    {A : AbelianVariety K g} {B : AbelianVariety K h} (φ : A.group ⟶ B.group)
    (x : A.AdditivePoints) :
    AlgPoints.toPoint (pointsGeometricEquiv B (pointsMap φ x)) =
      CerednikDrinfeld.QM.mapPt φ.hom.hom.left φ.hom.hom.w
        (AlgPoints.toPoint (pointsGeometricEquiv A x)) := by
  apply Subtype.ext
  rfl

private theorem integralGeometricEquiv_symm_level {g : ℕ}
    (ℓ : ℕ) [Fact ℓ.Prime] (A : AbelianVariety K g)
    (x : GeometricIntegral ℓ A K) (n : ℕ) :
    pointsGeometricEquiv A (((integralGeometricEquiv ℓ A).symm x).1 n) = x.1 n := by
  rw [← integralGeometricEquiv_apply, LinearEquiv.apply_symm_apply]

/-- The Riemann form of a pullback line bundle is the pullback of its Riemann
form along the actual integral Tate map. -/
theorem IsRiemannPairing.pullback {g h : ℕ}
    {A : AbelianVariety K g} {B : AbelianVariety K h} (φ : A.group ⟶ B.group)
    {M : B.group.X.left.Modules} {ℓ : ℕ} [Fact ℓ.Prime] {ζ : ℕ → K}
    {e : Pairing ℓ B} (he : IsRiemannPairing B M ℓ ζ e) :
    IsRiemannPairing A ((Scheme.Modules.pullback φ.hom.hom.left).obj M) ℓ ζ
      (e.compl₁₂ (integralMap ℓ φ) (integralMap ℓ φ)) := by
  intro n a b
  have hmul : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of K))
      (P Q : SchemeHomOver t A.group.X.hom),
      CerednikDrinfeld.QM.mapPt φ.hom.hom.left φ.hom.hom.w
          ((GroupScheme.law A.group).mul t P Q) =
        (GroupScheme.law B.group).mul t
          (CerednikDrinfeld.QM.mapPt φ.hom.hom.left φ.hom.hom.w P)
          (CerednikDrinfeld.QM.mapPt φ.hom.hom.left φ.hom.hom.w Q) := by
    intro T t P Q
    have hm := (IsMonHom.monoidHom φ.hom.hom (Over.mk t)).map_mul
      (schemeHomOverToOverHom P) (schemeHomOverToOverHom Q)
    exact Subtype.ext (congrArg Over.Hom.left hm)
  apply isLevelPairingValue_pullback (GroupScheme.law A.group)
    A.groupScheme_law_commutative (GroupScheme.law B.group)
    φ.hom.hom.left φ.hom.hom.w hmul M (ℓ ^ n) (a.1 n) (b.1 n)
    (by simpa only [natCast_zsmul] using TateModule.torsion a n)
  have h := he.level n
    (integralMap ℓ φ ((integralGeometricEquiv ℓ A).symm a))
    (integralMap ℓ φ ((integralGeometricEquiv ℓ A).symm b))
  change IsLevelPairingValue _ _ _ _
    (AlgPoints.toPoint (pointsGeometricEquiv B (pointsMap φ _)))
    (AlgPoints.toPoint (pointsGeometricEquiv B (pointsMap φ _))) _ at h
  simpa only [pointsGeometricEquiv_map, integralGeometricEquiv_symm_level,
    LinearMap.compl₁₂_apply, LinearEquiv.coe_coe] using h

end SupersingularCurves.Geometry.AbelianTate
