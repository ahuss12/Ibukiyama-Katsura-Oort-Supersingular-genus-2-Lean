/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.PointedCotangentFibre
import SupersingularCurves.Geometry.PointedCotangentDimension

/-!
# The exact cotangent sequence of an actual fibre

The cotangent space of the scheme-theoretic fibre is the cokernel of the
actual pointed differential. The proof uses square-zero points: a cotangent
functional lifts to the fibre precisely when it annihilates the differential.
This yields both the exact sequence and the actual fibre dimension formula.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.PointedCotangent
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

variable {K : Type u} [Field K] {X : Scheme.{u}}
variable (c : X ⟶ Spec (CommRingCat.of K))
  (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)

/-- A rational point on a locally finite-type scheme has a finite actual
cotangent space over the original field. -/
theorem finite_of_locallyOfFiniteType [LocallyOfFiniteType c] :
    Module.Finite K (Cotangent c s) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian c
  let S := Stalk c s
  have hK :=
    P2MW.S_AlgebraicCurve_CurveModel_finrank_cotangentSpace_zeroSection_eq_genusFF_of_representsRelSubPic.P2mTJ.bijective_algebraMap_residueField
      c s.1 s.2
  let e : K ≃+* IsLocalRing.ResidueField S := RingEquiv.ofBijective _ hK
  let f : Cotangent c s →ₛₗ[e.symm.toRingHom] Cotangent c s :=
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

namespace Fibre

variable {Y : Scheme.{u}} {d : Y ⟶ Spec (CommRingCat.of K)}
  {z : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) d}
  (f : X ⟶ Y) (hf : f ≫ d = c) (hs : s.1 ≫ f = z.1)

abbrev cotangentMap : Cotangent c s →ₗ[K] Cotangent (toBase f (z := z)) (point c s f hs) :=
  differential (toBase f (z := z)) (point c s f hs) (inclusion f)
    (inclusion_over c f hf) (point_inclusion c s f hs)

/-- A functional annihilating the actual differential gives a square-zero
point of the actual fibre. -/
theorem tangentPoint_lift_of_comp_zero
    {W : Type u} [AddCommGroup W] [Module K W]
    [Module Kᵐᵒᵖ W] [IsCentralScalar K W]
    (l : Cotangent c s →ₗ[K] W) (hl : l ∘ₗ differential c s f hf hs = 0) :
    ∃ q : TangentPoints (toBase f (z := z)) (point c s f hs).1 W,
      q.1 ≫ inclusion f = (pointsEquiv c s W l).1 := by
  let t := pointsEquiv c s W l
  have h := differential_action c s f hf hs l
  rw [hl] at h
  have ht := congrArg Subtype.val h
  rw [pointsEquiv_zero_coe] at ht
  change SquareZero.toBase K W ≫ z.1 = t.1 ≫ f at ht
  let q := pullback.lift t.1 (SquareZero.toBase K W) ht.symm
  have hq : SquareZero.basePoint K W ≫ q = (point c s f hs).1 := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, point_inclusion, t.2.2]
    · rw [Category.assoc, pullback.lift_snd, (point c s f hs).2,
        SquareZero.basePoint_toBase]
  exact ⟨⟨q, pullback.lift_snd _ _ _, hq⟩, pullback.lift_fst _ _ _⟩

/-- The cokernel universal property for the actual cotangent map. -/
theorem exists_factor_of_comp_zero
    {W : Type u} [AddCommGroup W] [Module K W]
    [Module Kᵐᵒᵖ W] [IsCentralScalar K W]
    (l : Cotangent c s →ₗ[K] W) (hl : l ∘ₗ differential c s f hf hs = 0) :
    ∃ m : Cotangent (toBase f (z := z)) (point c s f hs) →ₗ[K] W,
      m ∘ₗ cotangentMap c s f hf hs = l := by
  obtain ⟨q, hq⟩ := tangentPoint_lift_of_comp_zero c s f hf hs l hl
  let m := (pointsEquiv (toBase f (z := z)) (point c s f hs) W).symm q
  refine ⟨m, ?_⟩
  apply (pointsEquiv c s W).injective
  rw [differential_action]
  apply TangentPoints.ext
  change (pointsEquiv (toBase f (z := z)) (point c s f hs) W m).1 ≫ inclusion f = _
  rw [Equiv.apply_symm_apply]
  exact hq

/-- The fibre inclusion kills the image of the original differential. -/
theorem cotangentMap_comp_differential :
    cotangentMap c s f hf hs ∘ₗ differential c s f hf hs = 0 := by
  have hzero := differential_eq_zero_of_eq_constant (toBase f (z := z))
    (point c s f hs) (inclusion f ≫ f)
    (by rw [Category.assoc, hf, inclusion_over c f hf])
    (by rw [← Category.assoc, point_inclusion, hs]) pullback.condition
  rw [differential_comp] at hzero
  exact hzero

/-- Exactness at the cotangent space of the ambient pointed scheme. -/
theorem range_differential_eq_ker_cotangentMap :
    LinearMap.range (differential c s f hf hs) =
      LinearMap.ker (cotangentMap c s f hf hs) := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    exact LinearMap.congr_fun (cotangentMap_comp_differential c s f hf hs) y
  · let R := LinearMap.range (differential c s f hf hs)
    let W := Cotangent c s ⧸ R
    let : Module Kᵐᵒᵖ W := Module.compHom _ (RingEquiv.toOpposite K).symm.toRingHom
    let : IsCentralScalar K W := ⟨fun _ _ => rfl⟩
    have hl : R.mkQ ∘ₗ differential c s f hf hs = 0 := by
      ext y
      exact (Submodule.Quotient.mk_eq_zero R).mpr ⟨y, rfl⟩
    obtain ⟨m, hm⟩ := exists_factor_of_comp_zero c s f hf hs R.mkQ hl
    intro x hx
    apply (Submodule.Quotient.mk_eq_zero R).mp
    change R.mkQ x = 0
    rw [← hm, LinearMap.comp_apply, LinearMap.mem_ker.mp hx, map_zero]

/-- Rank-nullity for the actual fibre cotangent space. -/
theorem finrank_add_rank_differential [Module.Finite K (Cotangent c s)] :
    Module.finrank K (Cotangent (toBase f (z := z)) (point c s f hs)) +
      Module.finrank K (LinearMap.range (differential c s f hf hs)) =
        Module.finrank K (Cotangent c s) := by
  have h := (cotangentMap c s f hf hs).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (differential_surjective_of_mono
    (toBase f (z := z)) (point c s f hs) (inclusion f)
    (inclusion_over c f hf) (point_inclusion c s f hs)),
    finrank_top, ← range_differential_eq_ker_cotangentMap c s f hf hs] at h
  exact h

/-- The actual fibre cotangent dimension is ambient dimension minus the
rank of the actual pointed differential. -/
theorem finrank_eq_sub_rank_differential [Module.Finite K (Cotangent c s)] :
    Module.finrank K (Cotangent (toBase f (z := z)) (point c s f hs)) =
      Module.finrank K (Cotangent c s) -
        Module.finrank K (LinearMap.range (differential c s f hf hs)) :=
  Nat.eq_sub_of_add_eq (finrank_add_rank_differential c s f hf hs)

end Fibre
end SupersingularCurves.Geometry.PointedCotangent
