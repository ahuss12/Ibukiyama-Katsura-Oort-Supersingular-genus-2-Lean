/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentGroupIso
import SupersingularCurves.Geometry.FrobeniusFiniteFieldMorphismEquivariance

/-! # Frobenius invariance of actual homomorphisms between scalar-Frobenius models -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SupersingularCurves.Geometry.FrobeniusFiniteFieldScalarHom
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open FrobeniusDescent SchemeFrobenius FrobeniusFiniteFieldGroupDescent
variable {K : Type u} [Field K] [IsAlgClosed K]
variable (p : ℕ) [Fact p.Prime] [CharP K p] {g h : ℕ}

abbrev fixedBase : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (fixedField K p 2)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (fixedField K p 2) K))

/-- Frobenius squared fixes the actual coefficient subfield. -/
theorem frobenius_fixedBase :
    baseMap p K ≫ baseMap p K ≫ fixedBase (K := K) p = fixedBase p := by
  unfold baseMap fixedBase
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext a
  change ((a : K) ^ p) ^ p = (a : K)
  rw [← pow_mul, ← pow_two]
  exact a.property

/-- The coefficient Frobenius-square map on the genuine scalar-extension scheme. -/
def coefficientSquare (A : AbelianVariety (fixedField K p 2) g) :
    (A.baseChange K).group.X.left ⟶ (A.baseChange K).group.X.left :=
  pullback.lift (pullback.fst A.group.X.hom (fixedBase p))
    (pullback.snd A.group.X.hom (fixedBase p) ≫ baseMap p K ≫ baseMap p K) (by
      rw [pullback.condition, Category.assoc, Category.assoc, frobenius_fixedBase])

@[reassoc (attr := simp)] theorem coefficientSquare_fst
    (A : AbelianVariety (fixedField K p 2) g) :
    coefficientSquare p A ≫ pullback.fst A.group.X.hom (fixedBase p) =
      pullback.fst A.group.X.hom (fixedBase p) := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem coefficientSquare_snd
    (A : AbelianVariety (fixedField K p 2) g) :
    coefficientSquare p A ≫ (A.baseChange K).group.X.hom =
      (A.baseChange K).group.X.hom ≫ baseMap p K ≫ baseMap p K := pullback.lift_snd _ _ _

/-- Actual multiplication is compatible with the canonical base-change projection. -/
theorem baseChange_multiplication_fst (A : AbelianVariety (fixedField K p 2) g) (n : ℕ) :
    (GroupScheme.law (A.baseChange K).group).schemeNsmul n ≫
      pullback.fst A.group.X.hom (fixedBase p) =
        pullback.fst A.group.X.hom (fixedBase p) ≫ (GroupScheme.law A.group).schemeNsmul n :=
  schemeNsmul_comp_eq _ (IsPullback.of_hasPullback _ _) _ _
    (A.baseChange K).abelianSchemePropertyBundle (A.baseChange_zero_fst (K := K)) n

/-- For a scalar-Frobenius model, coefficient Frobenius squared is the canonical
descent operator characterized by [p]τ=F². -/
theorem multiplication_coefficientSquare
    (A : AbelianVariety (fixedField K p 2) g)
    (hA : absolute p A.group.X.hom ≫ absolute p A.group.X.hom =
      (GroupScheme.law A.group).schemeNsmul p) :
    (GroupScheme.law (A.baseChange K).group).schemeNsmul p ≫ coefficientSquare p A =
      absolute p (A.baseChange K).group.X.hom ≫ absolute p (A.baseChange K).group.X.hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, coefficientSquare_fst, baseChange_multiplication_fst, ← hA]
    have H := Scheme.frobenius_comp (pullback.fst A.group.X.hom (fixedBase p)) p 1
      (Fact.out : p.Prime) (globalChar p (A.baseChange K).group.X.hom)
      (globalChar p A.group.X.hom)
    change absolute p (A.baseChange K).group.X.hom ≫
      pullback.fst A.group.X.hom (fixedBase p) =
        pullback.fst A.group.X.hom (fixedBase p) ≫ absolute p A.group.X.hom at H
    simp only [Category.assoc]
    rw [← Category.assoc (pullback.fst A.group.X.hom (fixedBase p)),
      ← H, Category.assoc, ← H]
  · change (_ ≫ coefficientSquare p A) ≫ (A.baseChange K).group.X.hom = _
    rw [Category.assoc, coefficientSquare_snd, ← Category.assoc,
      (GroupScheme.law (A.baseChange K).group).schemeNsmul_over]
    change (A.baseChange K).group.X.hom ≫ baseMap p K ≫ baseMap p K =
      (absolute p (A.baseChange K).group.X.hom ≫
        absolute p (A.baseChange K).group.X.hom) ≫ (A.baseChange K).group.X.hom
    have H := absolute_over p (A.baseChange K).group.X.hom
    simp only [Category.assoc]
    rw [← Category.assoc (A.baseChange K).group.X.hom, ← H, Category.assoc, ← H]

/-- Every actual geometric homomorphism between scalar-Frobenius models is
invariant under the actual coefficient Frobenius action on its source. -/
theorem hom_projection_invariant
    (A : AbelianVariety (fixedField K p 2) g)
    (B : AbelianVariety (fixedField K p 2) h)
    (hA : absolute p A.group.X.hom ≫ absolute p A.group.X.hom =
      (GroupScheme.law A.group).schemeNsmul p)
    (hB : absolute p B.group.X.hom ≫ absolute p B.group.X.hom =
      (GroupScheme.law B.group).schemeNsmul p)
    (f : (A.baseChange K).group ⟶ (B.baseChange K).group) :
    coefficientSquare p A ≫ f.hom.hom.left ≫ pullback.fst B.group.X.hom (fixedBase p) =
      f.hom.hom.left ≫ pullback.fst B.group.X.hom (fixedBase p) := by
  have H := (A.baseChange K).frobeniusSquare_descent_natural (B.baseChange K) p
    (coefficientSquare p A) (coefficientSquare p B)
    (multiplication_coefficientSquare p A hA) (multiplication_coefficientSquare p B hB) f
  rw [← Category.assoc, H, Category.assoc, coefficientSquare_fst]

end SupersingularCurves.Geometry.FrobeniusFiniteFieldScalarHom
