/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusFiniteFieldHomGroup
import SupersingularCurves.Geometry.FrobeniusFiniteFieldScalarHomDescent

/-! # Actual homomorphisms descend between scalar-Frobenius abelian models -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SupersingularCurves.Geometry.FrobeniusFiniteFieldHomDescent
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open FrobeniusFactorGroup FrobeniusFiniteFieldGroupDescent

section BaseChange
variable {k K : Type} [Field k] [Field K] [Algebra k K] {a b : ℕ}
variable (A : AbelianVariety k a) (B : AbelianVariety k b)
local notation "ι" => Spec.map (CommRingCat.ofHom (algebraMap k K))

/-- The projection of an actual group morphism is a morphism over the original field. -/
theorem projection_over (f : (A.baseChange K).group ⟶ (B.baseChange K).group) :
    (f.hom.hom.left ≫ pullback.fst B.group.X.hom ι) ≫ B.group.X.hom =
      pullback.snd A.group.X.hom ι ≫ ι := by
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (fun z => z ≫ ι) f.hom.hom.w

/-- Scalar extension and actual group homomorphisms preserve multiplication on every test scheme. -/
theorem projection_respectsMul (f : (A.baseChange K).group ⟶ (B.baseChange K).group) :
    RespectsMul (GroupScheme.law A.group) (GroupScheme.law B.group) ι
      (f.hom.hom.left ≫ pullback.fst B.group.X.hom ι) (projection_over A B f) := by
  intro T t P Q
  let x : SchemeHomOver t (A.baseChange K).group.X.hom :=
    ⟨pullback.lift P.1 t P.2, pullback.lift_snd _ _ _⟩
  let y : SchemeHomOver t (A.baseChange K).group.X.hom :=
    ⟨pullback.lift Q.1 t Q.2, pullback.lift_snd _ _ _⟩
  have hA := mul_comp_eq_of_one_comp_eq
    (pullback.fst A.group.X.hom ι) (IsPullback.of_hasPullback _ _)
    (GroupScheme.law A.group) (GroupScheme.law (A.baseChange K).group)
    (A.baseChange K).abelianSchemePropertyBundle (A.baseChange_zero_fst (K := K)) t x y
  have hx : (⟨x.1 ≫ pullback.fst A.group.X.hom ι,
      by dsimp only [x]; rw [pullback.lift_fst, P.2]⟩ :
        SchemeHomOver (t ≫ ι) A.group.X.hom) = P := Subtype.ext (pullback.lift_fst _ _ _)
  have hy : (⟨y.1 ≫ pullback.fst A.group.X.hom ι,
      by dsimp only [y]; rw [pullback.lift_fst, Q.2]⟩ :
        SchemeHomOver (t ≫ ι) A.group.X.hom) = Q := Subtype.ext (pullback.lift_fst _ _ _)
  rw [hx, hy] at hA
  have hxy : pullback.lift ((GroupScheme.law A.group).mul (t ≫ ι) P Q).1 t
      ((GroupScheme.law A.group).mul (t ≫ ι) P Q).2 =
        ((GroupScheme.law (A.baseChange K).group).mul t x y).1 := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      exact hA.symm
    · exact (pullback.lift_snd _ _ _).trans
        ((GroupScheme.law (A.baseChange K).group).mul t x y).2.symm
  have hf := (A.baseChange K).abelianSchemePropertyBundle.mul_comp_eq_mul_comp_of_one_comp_eq_one
    (GroupScheme.law (A.baseChange K).group) (GroupScheme.law (B.baseChange K).group)
    f.hom.hom.left f.hom.hom.w (GroupScheme.zero_natural f) t x y
  have hB := mul_comp_eq_of_one_comp_eq
    (pullback.fst B.group.X.hom ι) (IsPullback.of_hasPullback _ _)
    (GroupScheme.law B.group) (GroupScheme.law (B.baseChange K).group)
    (B.baseChange K).abelianSchemePropertyBundle (B.baseChange_zero_fst (K := K)) t
    (pointMap f.hom.hom.left f.hom.hom.w x) (pointMap f.hom.hom.left f.hom.hom.w y)
  rw [hxy, ← Category.assoc, hf]
  simpa only [pointMap, x, y, Category.assoc] using hB
end BaseChange


section FixedField
open FrobeniusDescent SchemeFrobenius FrobeniusFiniteFieldScalarHom
variable {K : Type} [Field K] [IsAlgClosed K]
variable (p : ℕ) [Fact p.Prime] [CharP K p] {a b : ℕ}

/-- Every actual geometric group homomorphism between scalar-Frobenius models
has an actual group homomorphism over the p²-element field inducing it.
The line bundles are genuine very ample bundles, used for Hom representability. -/
theorem exists_descended_groupHom
    (A : AbelianVariety (fixedField K p 2) a)
    (B : AbelianVariety (fixedField K p 2) b)
    (hA : absolute p A.group.X.hom ≫ absolute p A.group.X.hom =
      (GroupScheme.law A.group).schemeNsmul p)
    (hB : absolute p B.group.X.hom ≫ absolute p B.group.X.hom =
      (GroupScheme.law B.group).schemeNsmul p)
    (𝓛A : A.group.X.left.Modules) (hA₁ : Scheme.Modules.IsInvertible 𝓛A)
    (hA₂ : Scheme.Modules.ClosedImmersionBySections 𝓛A A.group.X.hom)
    (𝓛B : B.group.X.left.Modules) (hB₁ : Scheme.Modules.IsInvertible 𝓛B)
    (hB₂ : Scheme.Modules.ClosedImmersionBySections 𝓛B B.group.X.hom)
    (f : (A.baseChange K).group ⟶ (B.baseChange K).group) :
    ∃ f₀ : A.group ⟶ B.group,
      pullback.fst A.group.X.hom (fixedBase p) ≫ f₀.hom.hom.left =
        f.hom.hom.left ≫ pullback.fst B.group.X.hom (fixedBase p) := by
  obtain ⟨φ₀, hφ₀, hmul₀, heq⟩ := exists_fixedField_hom p 2
    (GroupScheme.law A.group) (GroupScheme.law B.group)
    A.groupScheme_law_commutative B.groupScheme_law_commutative
    A.abelianSchemePropertyBundle B.abelianSchemePropertyBundle
    𝓛A hA₁ hA₂ 𝓛B hB₁ hB₂
    (f.hom.hom.left ≫ pullback.fst B.group.X.hom (fixedBase p))
    (projection_over A B f) (projection_respectsMul A B f)
    (changeBase_projection_invariant p A B hA hB f)
  refine ⟨unbaseGroupHom φ₀ hφ₀ hmul₀, ?_⟩
  exact (fst_unbase φ₀ (algebraMap (fixedField K p 2) K)).trans heq

/-- Faithfully flat scalar extension detects equality of actual group homomorphisms. -/
theorem descended_groupHom_unique
    (A : AbelianVariety (fixedField K p 2) a)
    (B : AbelianVariety (fixedField K p 2) b)
    (f₀ f₁ : A.group ⟶ B.group)
    (h : pullback.fst A.group.X.hom (fixedBase p) ≫ f₀.hom.hom.left =
      pullback.fst A.group.X.hom (fixedBase p) ≫ f₁.hom.hom.left) : f₀ = f₁ := by
  have hb : Flat (fixedBase (K := K) p) ∧ Surjective (fixedBase (K := K) p) :=
    (flat_and_surjective_SpecMap_iff
      (CommRingCat.ofHom (algebraMap (fixedField K p 2) K))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  letI : Flat (fixedBase (K := K) p) := hb.1
  letI : Surjective (fixedBase (K := K) p) := hb.2
  apply (Grp.forget _ ⋙ Over.forget _).map_injective
  exact (cancel_epi (pullback.fst A.group.X.hom (fixedBase p))).mp h
end FixedField

end SupersingularCurves.Geometry.FrobeniusFiniteFieldHomDescent
