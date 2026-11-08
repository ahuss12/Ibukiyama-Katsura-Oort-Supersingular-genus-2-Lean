/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.SmoothDifferentialRoots
import SupersingularCurves.Geometry.ReducedModuleDetection
import SupersingularCurves.Geometry.LocalizedDifferentialDetection
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.RingTheory.Etale.Kaehler

/-! # Detection of universal differentials at closed points -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.SmoothDifferentialDetection
open CategoryTheory AlgebraicGeometry

variable {K : Type u} [Field K] {X : Scheme.{u}}
  (c : X ⟶ Spec (CommRingCat.of K))

/-- The ground-field action on sections of an arbitrary open. -/
@[instance_reducible] def sectionAlgebra (U : X.Opens) : Algebra K Γ(X, U) :=
  ((X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom.comp
    (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)).toAlgebra

/-- The section action and the actual stalk action form the natural tower. -/
theorem section_stalk_tower (U : X.Opens) (x : X) (hx : x ∈ U) :
    letI := sectionAlgebra c U
    letI := SmoothDifferentialRoots.stalkAlgebra c x
    letI := X.presheaf.algebra_section_stalk ⟨x, hx⟩
    IsScalarTower K Γ(X, U) (X.presheaf.stalk x) := by
  let := sectionAlgebra c U
  let := SmoothDifferentialRoots.stalkAlgebra c x
  let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change (X.presheaf.germ ⊤ x trivial)
      (c.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv r)) =
    (X.presheaf.germ U x hx)
      ((X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op)
        (c.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv r)))
  exact (X.presheaf.germ_res_apply _ x hx _).symm

/-- Smoothness gives the genuine smooth coordinate algebra on every affine open. -/
theorem smooth_sectionAlgebra [Smooth c] (U : X.Opens) (hU : IsAffineOpen U) :
    letI := sectionAlgebra c U
    Algebra.Smooth K Γ(X, U) := by
  let := sectionAlgebra c U
  have h := c.smooth_appLE (isAffineOpen_top _) hU (by simp)
  have he : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.Smooth :=
    RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.bijective
  have hh := he.comp h
  exact hh

/-- On a smooth scheme over a field, a section whose differential vanishes
in every closed cotangent fibre has zero universal differential. -/
theorem D_eq_zero_of_closed_stalk_D_mem [Smooth c]
    (U : X.Opens) (hU : IsAffineOpen U) (a : Γ(X, U))
    (h : ∀ (x : X) (hx : x ∈ U), IsClosed {x} →
      letI := SmoothDifferentialRoots.stalkAlgebra c x
      KaehlerDifferential.D K (X.presheaf.stalk x) (X.presheaf.germ U x hx a) ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
          (⊤ : Submodule (X.presheaf.stalk x)
            (KaehlerDifferential K (X.presheaf.stalk x)))) :
    letI := sectionAlgebra c U
    KaehlerDifferential.D K Γ(X, U) a = 0 := by
  let := sectionAlgebra c U
  let := smooth_sectionAlgebra c U hU
  have (x : X) : IsDomain (X.presheaf.stalk x) :=
    (SmoothDifferentialRoots.normal_stalk c x).1
  have : IsReduced X := isReduced_of_isReduced_stalk X
  have : IsJacobsonRing Γ(X, U) := isJacobsonRing_of_finiteType (A := K)
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace c
  apply ReducedModuleDetection.eq_zero_of_forall_dual_mem_maximal (A := Γ(X, U))
  intro I hI l
  let q : PrimeSpectrum Γ(X, U) := ⟨I, hI.isPrime⟩
  let x : U := hU.isoSpec.inv q
  have hxq : hU.primeIdealOf x = q := by
    change hU.isoSpec.hom (hU.isoSpec.inv q) = q
    rw [← Scheme.Hom.comp_apply, hU.isoSpec.inv_hom_id]
    rfl
  have hxclosed : IsClosed {(x : X)} := by
    have hq : q ∈ closedPoints (Spec Γ(X, U)) :=
      q.isClosed_singleton_iff_isMaximal.mpr hI
    rw [← hU.fromSpec.isOpenEmbedding.preimage_closedPoints] at hq
    exact hq
  let := SmoothDifferentialRoots.stalkAlgebra c (x : X)
  let := X.presheaf.algebra_section_stalk x
  let := section_stalk_tower c U x x.2
  have hloc := hU.isLocalization_stalk x
  have : IsLocalization.AtPrime (X.presheaf.stalk x) I := by
    simpa only [hxq] using hloc
  have := Algebra.FormallyEtale.of_isLocalization (Rₘ := X.presheaf.stalk x) I.primeCompl
  exact LocalizedDifferentialDetection.dual_D_mem_of_D_mem_maximalIdeal_smul
    K Γ(X, U) (X.presheaf.stalk x) I
    (IsLocalization.AtPrime.under_maximalIdeal _ I) a (h x x.2 hxclosed) l

/-- Closed cotangent fibres detect the universal differential of a section
at every stalk, including nonclosed points. -/
theorem stalk_D_eq_zero_of_closed_stalk_D_mem [Smooth c]
    (U : X.Opens) (a : Γ(X, U))
    (h : ∀ (x : X) (hx : x ∈ U), IsClosed {x} →
      letI := SmoothDifferentialRoots.stalkAlgebra c x
      KaehlerDifferential.D K (X.presheaf.stalk x) (X.presheaf.germ U x hx a) ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
          (⊤ : Submodule (X.presheaf.stalk x)
            (KaehlerDifferential K (X.presheaf.stalk x))))
    (x : X) (hx : x ∈ U) :
    letI := SmoothDifferentialRoots.stalkAlgebra c x
    KaehlerDifferential.D K (X.presheaf.stalk x) (X.presheaf.germ U x hx a) = 0 := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
  let aV : Γ(X, V) := X.presheaf.map (homOfLE hVU : V ⟶ U).op a
  have hD := D_eq_zero_of_closed_stalk_D_mem c V hV aV (fun y hy hclosed => by
    simpa only [aV, X.presheaf.germ_res_apply] using h y (hVU hy) hclosed)
  let := sectionAlgebra c V
  let := SmoothDifferentialRoots.stalkAlgebra c x
  let := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  let := section_stalk_tower c V x hxV
  have hh := congrArg (KaehlerDifferential.map K K Γ(X, V) (X.presheaf.stalk x)) hD
  rw [KaehlerDifferential.map_D, map_zero] at hh
  change KaehlerDifferential.D K (X.presheaf.stalk x)
    (X.presheaf.germ V x hxV aV) = 0 at hh
  simpa only [aV, X.presheaf.germ_res_apply] using hh

/-- Vanishing in all closed local cotangent fibres factors the actual
morphism uniquely through relative Frobenius. -/
theorem existsUnique_relative_factor_of_closed_stalk_D_mem
    (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K] [Smooth c]
    {Y : Scheme.{u}} (f : X ⟶ Y) (d : Y ⟶ Spec (CommRingCat.of K)) (hf : f ≫ d = c)
    (h : ∀ (x : X), IsClosed {x} →
      letI := SmoothDifferentialRoots.stalkAlgebra c x
      ∀ b : Y.presheaf.stalk (f x),
        KaehlerDifferential.D K (X.presheaf.stalk x) (f.stalkMap x b) ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
            (⊤ : Submodule (X.presheaf.stalk x)
              (KaehlerDifferential K (X.presheaf.stalk x)))) :
    ∃! g : SchemeFrobenius.Twist p c ⟶ Y,
      SchemeFrobenius.relative p c ≫ g = f ∧
        g ≫ d = SchemeFrobenius.toBase p c := by
  apply SmoothDifferentialRoots.existsUnique_relative_factor_of_stalk_D_eq_zero c p f d hf
  intro U s x hx
  apply stalk_D_eq_zero_of_closed_stalk_D_mem c (f ⁻¹ᵁ U) (f.app U s) _ x hx
  intro y hy hclosed
  rw [← Scheme.Hom.germ_stalkMap_apply]
  exact h y hclosed (Y.presheaf.germ U (f y) hy s)

/-- Over an algebraically closed field it suffices to test the actual
local differentials at rational points. -/
theorem existsUnique_relative_factor_of_rational_stalk_D_mem
    [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p] [Smooth c]
    {Y : Scheme.{u}} (f : X ⟶ Y) (d : Y ⟶ Spec (CommRingCat.of K)) (hf : f ≫ d = c)
    (h : ∀ a : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c,
      let x := a.1 (IsLocalRing.closedPoint K)
      letI := SmoothDifferentialRoots.stalkAlgebra c x
      ∀ b : Y.presheaf.stalk (f x),
        KaehlerDifferential.D K (X.presheaf.stalk x) (f.stalkMap x b) ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
            (⊤ : Submodule (X.presheaf.stalk x)
              (KaehlerDifferential K (X.presheaf.stalk x)))) :
    ∃! g : SchemeFrobenius.Twist p c ⟶ Y,
      SchemeFrobenius.relative p c ≫ g = f ∧
        g ≫ d = SchemeFrobenius.toBase p c := by
  apply existsUnique_relative_factor_of_closed_stalk_D_mem c p f d hf
  intro x hx
  let a : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c :=
    ⟨pointOfClosedPoint c x hx, pointOfClosedPoint_comp c x hx⟩
  have ha : a.1 (IsLocalRing.closedPoint K) = x :=
    pointOfClosedPoint_apply c x hx _
  have hh := h a
  dsimp only at hh
  rw [ha] at hh
  exact hh

end SupersingularCurves.Geometry.SmoothDifferentialDetection
