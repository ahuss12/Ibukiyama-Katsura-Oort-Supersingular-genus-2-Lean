/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.PointedCotangentKernel
import SupersingularCurves.Geometry.FrobeniusCotangentVanishing

/-!
# Cotangent space of the fibre of a map with zero differential

If a pointed scheme morphism has zero cotangent differential, every actual
square-zero tangent point factors through its scheme-theoretic fibre.
Consequently the inclusion of that fibre induces an isomorphism of actual
local cotangent spaces. Neither smoothness nor reducedness is required.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.PointedCotangent.Fibre
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

variable {K : Type u} [Field K] {X Y : Scheme.{u}}
variable (c : X ⟶ Spec (CommRingCat.of K))
  (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
  {d : Y ⟶ Spec (CommRingCat.of K)}
  {z : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) d}
  (f : X ⟶ Y) (hf : f ≫ d = c) (hs : s.1 ≫ f = z.1)

abbrev scheme : Scheme.{u} := pullback f z.1

abbrev inclusion : scheme f (z := z) ⟶ X := pullback.fst f z.1

abbrev toBase : scheme f (z := z) ⟶ Spec (CommRingCat.of K) := pullback.snd f z.1

def point : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (toBase f (z := z)) :=
  ⟨pullback.lift s.1 (𝟙 _) (hs.trans (Category.id_comp _).symm),
    pullback.lift_snd _ _ _⟩

include hf in
theorem inclusion_over : inclusion f (z := z) ≫ c = toBase f (z := z) := by
  rw [← hf, ← Category.assoc, pullback.condition, Category.assoc, z.2, Category.comp_id]

theorem point_inclusion : (point c s f hs).1 ≫ inclusion f = s.1 :=
  pullback.lift_fst _ _ _

instance inclusion_mono : Mono (inclusion f (z := z)) := by
  let : Mono z.1 := by
    constructor
    intro T a b h
    simpa only [Category.assoc, z.2, Category.comp_id] using
      congrArg (fun q => q ≫ d) h
  infer_instance

/-- Every square-zero tangent point lifts to the actual fibre if the
pointed differential vanishes. -/
theorem tangentPoint_lift_of_differential_zero
    (hdf : differential c s f hf hs = 0)
    {W : Type u} [AddCommGroup W] [Module K W]
    [Module Kᵐᵒᵖ W] [IsCentralScalar K W]
    (t : TangentPoints c s.1 W) :
    ∃ q : TangentPoints (toBase f (z := z)) (point c s f hs).1 W,
      q.1 ≫ inclusion f = t.1 := by
  let l := (pointsEquiv c s W).symm t
  have h := differential_action c s f hf hs l
  rw [hdf, LinearMap.comp_zero] at h
  have ht := congrArg Subtype.val h
  rw [pointsEquiv_zero_coe] at ht
  change SquareZero.toBase K W ≫ z.1 = (pointsEquiv c s W l).1 ≫ f at ht
  rw [Equiv.apply_symm_apply] at ht
  let q := pullback.lift t.1 (SquareZero.toBase K W) ht.symm
  have hq : SquareZero.basePoint K W ≫ q = (point c s f hs).1 := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, point_inclusion, t.2.2]
    · rw [Category.assoc, pullback.lift_snd, (point c s f hs).2,
        SquareZero.basePoint_toBase]
  exact ⟨⟨q, pullback.lift_snd _ _ _, hq⟩, pullback.lift_fst _ _ _⟩

/-- The actual fibre inclusion induces a bijection on actual cotangent
spaces when the original map has zero differential. -/
theorem differential_bijective_of_zero (hdf : differential c s f hf hs = 0) :
    Function.Bijective
      (differential (toBase f (z := z)) (point c s f hs) (inclusion f)
        (inclusion_over c f hf) (point_inclusion c s f hs)) := by
  constructor
  · apply LinearMap.dualMap_surjective_iff.mp
    intro l
    obtain ⟨q, hq⟩ := tangentPoint_lift_of_differential_zero c s f hf hs hdf
      (pointsEquiv c s K l)
    let m := (pointsEquiv (toBase f (z := z)) (point c s f hs) K).symm q
    refine ⟨m, ?_⟩
    apply (pointsEquiv c s K).injective
    change pointsEquiv c s K
      (m ∘ₗ differential (toBase f (z := z)) (point c s f hs) (inclusion f)
        (inclusion_over c f hf) (point_inclusion c s f hs)) = _
    rw [differential_action]
    apply TangentPoints.ext
    change (pointsEquiv (toBase f (z := z)) (point c s f hs) K m).1 ≫ inclusion f = _
    rw [Equiv.apply_symm_apply]
    exact hq
  · exact differential_surjective_of_mono (toBase f (z := z)) (point c s f hs)
      (inclusion f) (inclusion_over c f hf) (point_inclusion c s f hs)

end SupersingularCurves.Geometry.PointedCotangent.Fibre
