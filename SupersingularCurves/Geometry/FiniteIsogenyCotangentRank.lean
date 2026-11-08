/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.GroupHomFibre
import SupersingularCurves.Geometry.FiniteLocalGroupPrimeCotangent

/-!
# Cotangent rank of an actual degree-p isogeny

An actual finite-flat group morphism of degree p with trivial rational
kernel has an actual one-point kernel group of order p. Its identity
cotangent dimension is one. The exact fibre cotangent sequence therefore
gives differential rank one when the source is a smooth surface.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.GroupHomFibre
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian FrobeniusFactorGroup PointedCotangent

variable {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}}
  {c : X ⟶ Spec (CommRingCat.of K)} {d : Y ⟶ Spec (CommRingCat.of K)}
  (L : RelativeGroupLaw K c) (M : RelativeGroupLaw K d)
  (f : X ⟶ Y) (hf : f ≫ d = c)
  (hm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t c),
    pointMap f hf (L.mul t x y) = M.mul t (pointMap f hf x) (pointMap f hf y))

include hm in
/-- Trivial rational kernel makes the actual finite kernel scheme one-point. -/
theorem subsingleton_of_kernel_trivial [IsFinite f]
    (hker : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c,
      pointMap f hf x = M.one (𝟙 _) → x = L.one (𝟙 _)) :
    Subsingleton (scheme M f) := by
  let s := Fibre.point c (L.one (𝟙 _)) f
    (congrArg Subtype.val (map_one L M f hf hm (𝟙 _)))
  apply FiniteGeometricPoints.subsingleton_of_unique_point (toBase M f) s
  intro x
  apply inclusionPoint_injective M f hf (𝟙 _)
  have hx := hker (inclusionPoint M f hf x) (inclusionPoint_kernel M f hf x)
  apply hx.trans
  apply Subtype.ext
  exact (Fibre.point_inclusion c (L.one (𝟙 _)) f _).symm

include hm in
/-- The actual kernel cotangent dimension is one for a degree-p finite-flat
group morphism with trivial rational kernel. -/
theorem fibre_cotangent_finrank_eq_one [IsFinite f] [Flat f]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (hker : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c,
      pointMap f hf x = M.one (𝟙 _) → x = L.one (𝟙 _))
    (hlen : f.finrank ((M.one (𝟙 _)).1 (IsLocalRing.closedPoint K)) = p) :
    Module.finrank K (Cotangent (toBase M f)
      (Fibre.point c (L.one (𝟙 _)) f
        (congrArg Subtype.val (map_one L M f hf hm (𝟙 _))))) = 1 := by
  have : Subsingleton (scheme M f) :=
    subsingleton_of_kernel_trivial L M f hf hm hker
  apply FiniteLocalGroupScheme.cotangent_finrank_eq_one_of_finrank_eq_prime
    (toBase M f) _ (law L M f hf hm) (law_one_eq_point L M f hf hm) p
  change (pullback.snd f (M.one (𝟙 _)).1).finrank _ = p
  rw [Scheme.Hom.finrank_pullback_snd]
  exact hlen

include hm in
/-- Rank one of the actual pointed differential on a smooth surface,
deduced from its actual degree-p kernel rather than assumed. -/
theorem differential_finrank_eq_one [IsFinite f] [Flat f]
    [SmoothOfRelativeDimension 2 c]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (hker : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c,
      pointMap f hf x = M.one (𝟙 _) → x = L.one (𝟙 _))
    (hlen : f.finrank ((M.one (𝟙 _)).1 (IsLocalRing.closedPoint K)) = p) :
    Module.finrank K (LinearMap.range (differential c (L.one (𝟙 _)) f hf
      (congrArg Subtype.val (map_one L M f hf hm (𝟙 _))))) = 1 := by
  have : Smooth c := SmoothOfRelativeDimension.smooth 2 c
  have : Module.Finite K (Cotangent c (L.one (𝟙 _))) :=
    finite_of_locallyOfFiniteType c (L.one (𝟙 _))
  have heq := Fibre.finrank_add_rank_differential c (L.one (𝟙 _)) f hf
    (congrArg Subtype.val (map_one L M f hf hm (𝟙 _)))
  rw [fibre_cotangent_finrank_eq_one L M f hf hm p hker hlen,
    finrank_eq_relativeDimension c (L.one (𝟙 _)) 2] at heq
  omega

end SupersingularCurves.Geometry.GroupHomFibre
