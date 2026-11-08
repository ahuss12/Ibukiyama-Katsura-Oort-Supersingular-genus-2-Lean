/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FiniteLocalGroupScheme
import SupersingularCurves.Geometry.AffineInvariantDerivation
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Actual invariant derivations on a local affine group scheme

A nonzero cotangent class at the actual identity gives a tangent functional
and its genuine square-zero point. The transported geometric group law
extends this tangent to a derivation of the actual identity stalk, taking
the chosen element to a unit. No derivation-existence hypothesis is used.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.LocalGroupInvariantDerivation
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open PointedCotangent
open P2MW.S_AlgebraicGeometry_Scheme_exists_tangentPoints_equiv_linearMap_cotangentSpace

variable {K : Type u} [Field K] {X : Scheme.{u}}
  (c : X ⟶ Spec (CommRingCat.of K))
  (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
  [IsAffine X] [Subsingleton X]
  (G : RelativeGroupLaw K c) (hs : G.one (𝟙 _) = s)

include hs in
/-- Every nonzero actual identity cotangent class is detected by a
geometrically constructed invariant derivation of the actual local ring. -/
theorem exists_derivation_augmentation_ne_zero
    (x : IsLocalRing.maximalIdeal (Stalk c s))
    (hx : (IsLocalRing.maximalIdeal (Stalk c s)).toCotangent x ≠ 0) :
    ∃ D : Derivation K (Stalk c s) (Stalk c s), augmentation c s (D x) ≠ 0 := by
  let ε := augmentation c s
  let xker : RingHom.ker ε.toRingHom :=
    ⟨x, by change (x : Stalk c s) ∈ RingHom.ker (augmentation c s); rw [ker_augmentation]; exact x.2⟩
  have hxker : (RingHom.ker ε.toRingHom).toCotangent xker ≠ 0 := by
    intro hz
    apply hx
    apply ((IsLocalRing.maximalIdeal (Stalk c s)).toCotangent_eq_zero x).mpr
    have hmem := ((RingHom.ker ε.toRingHom).toCotangent_eq_zero xker).mp hz
    change (x : Stalk c s) ∈ RingHom.ker (augmentation c s) ^ 2 at hmem
    rwa [ker_augmentation] at hmem
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_ne_zero K hxker
  let τ : Stalk c s →ₐ[K] TrivSqZeroExt K K :=
    P2mTJ1.liftHom (P2mTJ1.π_algebraMap (fun _ => rfl) s.2) l
  have hτ : (TrivSqZeroExt.fstHom K K K).comp τ = ε := by
    ext y
    exact P2mTJ1.fst_liftHom (P2mTJ1.π_algebraMap (fun _ => rfl) s.2) l y
  have hτx : (τ x).snd ≠ 0 := by
    change (τ (xker : Stalk c s)).snd ≠ 0
    rw [show (τ (xker : Stalk c s)).snd = l ((RingHom.ker ε.toRingHom).toCotangent xker) from
      P2mTJ1.snd_liftHom (P2mTJ1.π_algebraMap (fun _ => rfl) s.2) l xker]
    exact hl
  obtain ⟨D, hD⟩ := AffineInvariantDerivation.exists_derivation K
    (FiniteLocalGroupScheme.stalkLaw c s G) ε
    (FiniteLocalGroupScheme.stalkLaw_one c s G hs) τ hτ
  exact ⟨D, by rw [hD]; exact hτx⟩

include hs in
/-- In the actual local coordinate algebra, the same derivation takes the
specified cotangent generator to a unit. -/
theorem exists_derivation_isUnit
    (x : IsLocalRing.maximalIdeal (Stalk c s))
    (hx : (IsLocalRing.maximalIdeal (Stalk c s)).toCotangent x ≠ 0) :
    ∃ D : Derivation K (Stalk c s) (Stalk c s), IsUnit (D x) := by
  obtain ⟨D, hD⟩ := exists_derivation_augmentation_ne_zero c s G hs x hx
  refine ⟨D, ?_⟩
  by_contra hn
  have hm : D x ∈ IsLocalRing.maximalIdeal (Stalk c s) := by
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hn
  have hm' : D x ∈ RingHom.ker (augmentation c s) := by
    simpa only [ker_augmentation] using hm
  exact hD (RingHom.mem_ker.mp hm')

end SupersingularCurves.Geometry.LocalGroupInvariantDerivation
