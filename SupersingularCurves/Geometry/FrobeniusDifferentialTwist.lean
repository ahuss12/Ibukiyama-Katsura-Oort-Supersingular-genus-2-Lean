/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusCechPullback
import SupersingularCurves.Geometry.GlobalDifferentials

/-!
# The actual Frobenius twist of global differential forms

The projection from the Frobenius base change is an isomorphism of schemes
over a perfect field. Pullback by that projection, on genuine Kaehler sections,
is Frobenius-semilinear. Its inverse is induced by the inverse scheme map.
This is not pullback by relative Frobenius and uses neither Cartier nor
Verschiebung to define either map.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.SchemeFrobenius
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.TwoAffineOpenCover

variable (p : ℕ) [Fact p.Prime] {K : Type u} [Field K] [CharP K p]
variable {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
variable (𝒱 : C.TwoAffineOpenCover)

/-- Projection of the actual base change, with its Frobenius scalar map. -/
def projectionCoverHom :
    HomOver (frobenius K p) 𝒱 c (twistedCover p c 𝒱) (toBase p c) where
  hom := projection p c
  comm := pullback.condition
  U0_le := le_rfl
  U1_le := le_rfl

variable [PerfectField K]

instance frobeniusInversePair :
    RingHomInvPair (frobeniusEquiv K p).toRingHom
      (frobeniusEquiv K p).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (frobeniusEquiv K p)

instance inverseFrobeniusPair :
    RingHomInvPair (frobeniusEquiv K p).symm.toRingHom
      (frobeniusEquiv K p).toRingHom :=
  RingHomInvPair.of_ringEquiv_symm (frobeniusEquiv K p)

/-- The scalar Frobenius is an actual scheme isomorphism over a perfect field. -/
instance baseMap_isIso : IsIso (baseMap p K) := by
  exact inferInstanceAs
    (IsIso (Scheme.Spec.mapIso (frobeniusEquiv K p).toCommRingCatIso.op).hom)

/-- Base change of the field automorphism has an invertible projection. -/
instance projection_isIso : IsIso (projection p c) :=
  inferInstanceAs (IsIso (pullback.fst c (baseMap p K)))

/-- The inverse field morphism is induced by inverse Frobenius. -/
theorem inverse_baseMap :
    inv (baseMap p K) =
      Spec.map (CommRingCat.ofHom (frobeniusEquiv K p).symm.toRingHom) := by
  exact IsIso.inv_eq_of_hom_inv_id
    (Scheme.Spec.mapIso (frobeniusEquiv K p).toCommRingCatIso.op).hom_inv_id

/-- The inverse projection commutes with inverse Frobenius on the base. -/
theorem inverse_projection_over :
    inv (projection p c) ≫ toBase p c =
      c ≫ Spec.map (CommRingCat.ofHom (frobeniusEquiv K p).symm.toRingHom) := by
  rw [← inverse_baseMap p]
  apply (cancel_mono (baseMap p K)).mp
  rw [Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id,
    ← show projection p c ≫ c = toBase p c ≫ baseMap p K from pullback.condition,
    ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

/-- The inverse projection takes each base-changed chart back to its original. -/
theorem inverse_projection_preimage (U : C.Opens) :
    inv (projection p c) ⁻¹ᵁ (projection p c ⁻¹ᵁ U) = U := by
  rw [← Scheme.Hom.comp_preimage, IsIso.inv_hom_id]
  rfl

/-- The genuine inverse scheme map, with inverse-Frobenius scalar map. -/
def inverseProjectionCoverHom :
    HomOver (frobeniusEquiv K p).symm.toRingHom
      (twistedCover p c 𝒱) (toBase p c) 𝒱 c where
  hom := inv (projection p c)
  comm := inverse_projection_over p c
  U0_le := (inverse_projection_preimage p c 𝒱.U0).ge
  U1_le := (inverse_projection_preimage p c 𝒱.U1).ge

theorem inverse_projectionCoverHom_kaehler (ω : (𝒱.kaehlerSections c).H0) :
    (inverseProjectionCoverHom p c 𝒱).kaehlerH0map
      ((projectionCoverHom p c 𝒱).kaehlerH0map ω) = ω := by
  rw [← HomOver.comp_kaehlerH0map]
  exact (HomOver.kaehlerH0map_congr
    (f := (inverseProjectionCoverHom p c 𝒱).comp (projectionCoverHom p c 𝒱))
    (g := HomOver.id 𝒱 c) (IsIso.inv_hom_id (projection p c)) ω).trans
      (HomOver.id_kaehlerH0map ω)

theorem projection_inverseCoverHom_kaehler
    (ω : ((twistedCover p c 𝒱).kaehlerSections (toBase p c)).H0) :
    (projectionCoverHom p c 𝒱).kaehlerH0map
      ((inverseProjectionCoverHom p c 𝒱).kaehlerH0map ω) = ω := by
  rw [← HomOver.comp_kaehlerH0map]
  exact (HomOver.kaehlerH0map_congr
    (f := (projectionCoverHom p c 𝒱).comp (inverseProjectionCoverHom p c 𝒱))
    (g := HomOver.id (twistedCover p c 𝒱) (toBase p c))
    (IsIso.hom_inv_id (projection p c)) ω).trans (HomOver.id_kaehlerH0map ω)

/-- The actual Frobenius-semilinear twist of global sheaf differentials. -/
def globalFormsTwistEquiv :
    LinearEquiv (frobeniusEquiv K p).toRingHom
      (σ' := (frobeniusEquiv K p).symm.toRingHom) (𝒱.kaehlerSections c).H0
      ((twistedCover p c 𝒱).kaehlerSections (toBase p c)).H0 where
  toFun := (projectionCoverHom p c 𝒱).kaehlerH0map
  invFun := (inverseProjectionCoverHom p c 𝒱).kaehlerH0map
  left_inv := inverse_projectionCoverHom_kaehler p c 𝒱
  right_inv := projection_inverseCoverHom_kaehler p c 𝒱
  map_add' := (projectionCoverHom p c 𝒱).kaehlerH0map.map_add
  map_smul' := (projectionCoverHom p c 𝒱).kaehlerH0map.map_smulₛₗ

/-- In particular the scalar is raised to p, rather than left unchanged. -/
theorem globalFormsTwistEquiv_smul (a : K) (ω : (𝒱.kaehlerSections c).H0) :
    globalFormsTwistEquiv p c 𝒱 (a • ω) =
      a ^ p • globalFormsTwistEquiv p c 𝒱 ω :=
  (globalFormsTwistEquiv p c 𝒱).map_smulₛₗ a ω

/-- On the first chart the map is the actual differential pullback. -/
theorem globalFormsTwistEquiv_chart0 (ω : (𝒱.kaehlerSections c).H0) :
    (globalFormsTwistEquiv p c 𝒱 ω).val.1 =
      (projectionCoverHom p c 𝒱).kaehlerMap0 ω.val.1 := rfl

/-- On the second chart the map is the actual differential pullback. -/
theorem globalFormsTwistEquiv_chart1 (ω : (𝒱.kaehlerSections c).H0) :
    (globalFormsTwistEquiv p c 𝒱 ω).val.2 =
      (projectionCoverHom p c 𝒱).kaehlerMap1 ω.val.2 := rfl

omit [PerfectField K] in
/-- The formula on generators uses pullback of both the coefficient and function. -/
theorem projection_kaehlerMap0_smul_D (a t : (𝒱.cover c).A0) :
    (projectionCoverHom p c 𝒱).kaehlerMap0
      (a • KaehlerDifferential.D K _ t) =
      (projectionCoverHom p c 𝒱).map0 a •
        KaehlerDifferential.D K _ ((projectionCoverHom p c 𝒱).map0 t) :=
  (projectionCoverHom p c 𝒱).kaehlerMap0_smul_D a t

end SupersingularCurves.Geometry.SchemeFrobenius
