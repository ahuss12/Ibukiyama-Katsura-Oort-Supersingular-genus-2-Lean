/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.SchemeCechCohomology
import Theorems.Thm_AlgebraicCurve_cechH1ToH1_bijective
import Theorems.Thm_AlgebraicCurve_placesOf_union_eq_univ_of_sup_eq_top
import Theorems.Thm_AlgebraicGeometry_not_isAffine_of_isProper_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one

/-!
# Actual structure-sheaf Cech cohomology and repartition cohomology

The map first takes the generic germ of an overlap section, then extends it
by zero on the first chart's places. The resulting repartition is taken
modulo integral and principal repartitions. We discharge the cover and
approximation hypotheses of the existing function-field comparison for an
actual smooth proper integral curve. The bijectivity proof uses the pinned
upstream Riemann--Roch/approximation results; the map itself is specified.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.SchemeCech
open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace
open InfinitesimalPicard

variable {K : Type u} [Field K] {C : Scheme.{u}}
variable (c : C ⟶ Spec (CommRingCat.of K)) [IsIntegral C]
variable [IsProper c] [SmoothOfRelativeDimension 1 c]

include c

/-- No affine chart contains an entire smooth proper integral curve. -/
theorem affine_ne_top (U : C.Opens) (hU : IsAffineOpen U) : U ≠ ⊤ := by
  intro h
  apply not_isAffine_of_isProper_of_smoothOfRelativeDimension_one c
  have hT : IsAffineOpen (⊤ : C.Opens) := h ▸ hU
  letI : IsAffine (⊤ : C.Opens) := hT
  exact IsAffine.of_isIso C.topIso.inv

variable (𝒱 : C.TwoAffineOpenCover)

include 𝒱

/-- Both charts of a two-affine cover of the curve are nonempty. -/
theorem properCover_nonempty : Nonempty 𝒱.U0 ∧ Nonempty 𝒱.U1 := by
  constructor
  · by_contra hc
    have hb : 𝒱.U0 = ⊥ := by
      ext z
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hz => hc ⟨⟨z, hz⟩⟩
    apply affine_ne_top c 𝒱.U1 𝒱.isAffineOpen_U1
    simpa only [hb, bot_sup_eq] using 𝒱.sup_eq_top
  · by_contra hc
    have hb : 𝒱.U1 = ⊥ := by
      ext z
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hz => hc ⟨⟨z, hz⟩⟩
    apply affine_ne_top c 𝒱.U0 𝒱.isAffineOpen_U0
    simpa only [hb, sup_bot_eq] using 𝒱.sup_eq_top

/-- The place sets cover all places, and each affine chart misses a place. -/
theorem cover_places :
    letI := (baseToFunctionField c).toAlgebra
    placesOf c 𝒱.U0 ∪ placesOf c 𝒱.U1 = Set.univ ∧
      (∃ v : Place K C.functionField, v ∉ placesOf c 𝒱.U0) ∧
      (∃ v : Place K C.functionField, v ∉ placesOf c 𝒱.U1) :=
  letI := (baseToFunctionField c).toAlgebra
  placesOf_union_eq_univ_of_sup_eq_top c 𝒱.U0 𝒱.U1 𝒱.sup_eq_top
    (affine_ne_top c 𝒱.U0 𝒱.isAffineOpen_U0)
    (affine_ne_top c 𝒱.U1 𝒱.isAffineOpen_U1)

/-- H1 defined by the actual function-field repartition quotient at divisor zero. -/
abbrev RepartitionH1 :=
  letI := (baseToFunctionField c).toAlgebra
  H1 (0 : Divisor K C.functionField)

theorem properCover_overlap_nonempty : Nonempty (𝒱.U0 ⊓ 𝒱.U1 : C.Opens) :=
  (nonempty_preirreducible_inter 𝒱.U0.isOpen 𝒱.U1.isOpen
    (Set.nonempty_coe_sort.mp (properCover_nonempty c 𝒱).1)
    (Set.nonempty_coe_sort.mp (properCover_nonempty c 𝒱).2)).to_subtype

/-- The canonical generic-restriction / off-chart map to repartition H1. -/
def toRepartition :
    letI := (baseToFunctionField c).toAlgebra
    CechH1 c 𝒱 →ₗ[K] RepartitionH1 c :=
  letI := (baseToFunctionField c).toAlgebra
  letI := (properCover_nonempty c 𝒱).1
  letI := (properCover_nonempty c 𝒱).2
  cechH1ToH1 (cover_places c 𝒱).1 0 ∘ₗ (functionFieldCechEquiv c 𝒱).toLinearMap

/-- Formula on every actual structure-sheaf Cech representative. -/
theorem toRepartition_mk (f : (𝒱.structureSheafSections c).M01) :
    letI := (baseToFunctionField c).toAlgebra
    letI := properCover_overlap_nonempty c 𝒱
    toRepartition c 𝒱 (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (extendOffChart K (placesOf c 𝒱.U0)
        ((C.germToFunctionField (𝒱.U0 ⊓ 𝒱.U1)).hom f)) := rfl

/-- The displayed representative formula characterizes the map. -/
theorem toRepartition_unique :
    letI := (baseToFunctionField c).toAlgebra
    letI := properCover_overlap_nonempty c 𝒱
    ∀ e : CechH1 c 𝒱 →ₗ[K] RepartitionH1 c,
    (∀ f : (𝒱.structureSheafSections c).M01,
      e (Submodule.Quotient.mk f) =
        Submodule.Quotient.mk (extendOffChart K (placesOf c 𝒱.U0)
          ((C.germToFunctionField (𝒱.U0 ⊓ 𝒱.U1)).hom f))) →
    e = toRepartition c 𝒱 := by
  letI := (baseToFunctionField c).toAlgebra
  letI := properCover_overlap_nonempty c 𝒱
  intro e he
  apply LinearMap.ext
  intro q
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact he f

variable [PerfectField K]

/-- Approximation proves bijectivity of the specified map, not just equality
of dimensions. Constants are required to be the ground field. -/
theorem toRepartition_bijective :
    letI := (baseToFunctionField c).toAlgebra
    ConstantsAreBase K C.functionField → Function.Bijective (toRepartition c 𝒱) := by
  letI := (baseToFunctionField c).toAlgebra
  letI : IsCurveOver K C.functionField :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one c
      (RingEquiv.refl _) (fun _ => rfl)
  letI : Algebra.EssFiniteType K C.functionField := essFiniteType_functionField c
  letI := (properCover_nonempty c 𝒱).1
  letI := (properCover_nonempty c 𝒱).2
  intro hC
  obtain ⟨_, hL0, γ, E, hγ⟩ := stichtenothGenusExists_of_isCurveOver hC
  letI := hL0
  exact (cechH1ToH1_bijective hγ (cover_places c 𝒱).1
    (cover_places c 𝒱).2.1 (cover_places c 𝒱).2.2 0).comp
      (functionFieldCechEquiv c 𝒱).bijective

/-- The actual Cech/repartition comparison with its prescribed forward map. -/
def repartitionEquiv
    (hC : letI := (baseToFunctionField c).toAlgebra; ConstantsAreBase K C.functionField) :
    letI := (baseToFunctionField c).toAlgebra
    CechH1 c 𝒱 ≃ₗ[K] RepartitionH1 c :=
  letI := (baseToFunctionField c).toAlgebra
  LinearEquiv.ofBijective (toRepartition c 𝒱) (toRepartition_bijective c 𝒱 hC)

theorem repartitionEquiv_mk
    (hC : letI := (baseToFunctionField c).toAlgebra; ConstantsAreBase K C.functionField)
    (f : (𝒱.structureSheafSections c).M01) :
    letI := (baseToFunctionField c).toAlgebra
    letI := properCover_overlap_nonempty c 𝒱
    repartitionEquiv c 𝒱 hC (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (extendOffChart K (placesOf c 𝒱.U0)
        ((C.germToFunctionField (𝒱.U0 ⊓ 𝒱.U1)).hom f)) := rfl

/-- Over an algebraically closed field the constants hypothesis is proved
from a degree-one place of the actual curve. -/
theorem constantsAreBase [IsAlgClosed K] :
    letI := (baseToFunctionField c).toAlgebra
    ConstantsAreBase K C.functionField := by
  letI := (baseToFunctionField c).toAlgebra
  letI : IsCurveOver K C.functionField :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one c
      (RingEquiv.refl _) (fun _ => rfl)
  obtain ⟨v, _⟩ := (cover_places c 𝒱).2.1
  exact constantsAreBase_of_deg_eq_one v (IsCurveOver.deg_eq_one_of_isAlgClosed v)

/-- The comparison for an actual curve over an algebraically closed field,
with all auxiliary constants/approximation hypotheses discharged. -/
def repartitionEquivOfAlgClosed [IsAlgClosed K] :
    letI := (baseToFunctionField c).toAlgebra
    CechH1 c 𝒱 ≃ₗ[K] RepartitionH1 c :=
  letI := (baseToFunctionField c).toAlgebra
  repartitionEquiv c 𝒱 (constantsAreBase c 𝒱)

end SupersingularCurves.Geometry.SchemeCech
