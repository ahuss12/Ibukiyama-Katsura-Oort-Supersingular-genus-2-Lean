/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusFiniteFieldHomDescent
import SupersingularCurves.Geometry.FrobeniusFactorGroup

/-! # Recovering actual group morphisms from effective homomorphism descent -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SupersingularCurves.Geometry.FrobeniusFiniteFieldHomDescent
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open FrobeniusFactorGroup
variable {k : Type} [Field k] {G H : GroupScheme k}

/-- Undo scalar extension along the identity of the base. -/
def unbase (φ : pullback G.X.hom (𝟙 _) ⟶ H.X.left) : G.X.left ⟶ H.X.left :=
  pullback.lift (𝟙 _) G.X.hom (by simp) ≫ φ

theorem unbase_over (φ : pullback G.X.hom (𝟙 _) ⟶ H.X.left)
    (hφ : φ ≫ H.X.hom = pullback.snd G.X.hom (𝟙 _) ≫ 𝟙 _) :
    unbase φ ≫ H.X.hom = G.X.hom := by
  rw [unbase, Category.assoc, hφ, ← Category.assoc, pullback.lift_snd, Category.comp_id]

theorem unbase_point (φ : pullback G.X.hom (𝟙 _) ⟶ H.X.left)
    {T : Scheme} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t G.X.hom) :
    x.1 ≫ unbase φ = pullback.lift x.1 t (by simpa using x.2) ≫ φ := by
  rw [unbase, ← Category.assoc]
  congr 1
  apply pullback.hom_ext <;> simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
    Category.comp_id, x.2]

private theorem mul_base_eq {X T : Scheme.{0}} {c : X ⟶ Spec (CommRingCat.of k)}
    (L : RelativeGroupLaw k c) {t t' : T ⟶ Spec (CommRingCat.of k)}
    (h : t = t') (P Q : SchemeHomOver t c) :
    (L.mul t' ⟨P.1, P.2.trans h⟩ ⟨Q.1, Q.2.trans h⟩).1 = (L.mul t P Q).1 := by
  subst t'
  rfl

theorem unbase_mul (φ : pullback G.X.hom (𝟙 _) ⟶ H.X.left)
    (hφ : φ ≫ H.X.hom = pullback.snd G.X.hom (𝟙 _) ≫ 𝟙 _)
    (hmul : RespectsMul (GroupScheme.law G) (GroupScheme.law H) (𝟙 _) φ hφ)
    {T : Scheme} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t G.X.hom) :
    pointMap (unbase φ) (unbase_over φ hφ) ((GroupScheme.law G).mul t x y) =
      (GroupScheme.law H).mul t (pointMap (unbase φ) (unbase_over φ hφ) x)
        (pointMap (unbase φ) (unbase_over φ hφ) y) := by
  apply Subtype.ext
  have hm := hmul T t ⟨x.1, by simpa using x.2⟩ ⟨y.1, by simpa using y.2⟩
  dsimp only [pointMap]
  simp only [unbase_point]
  have hA := mul_base_eq (GroupScheme.law G) (Category.comp_id t).symm x y
  have hB := mul_base_eq (GroupScheme.law H) (Category.comp_id t).symm
    (⟨pullback.lift x.1 t (by simpa using x.2) ≫ φ, by
      rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd, Category.comp_id]⟩ :
      SchemeHomOver t H.X.hom)
    (⟨pullback.lift y.1 t (by simpa using y.2) ≫ φ, by
      rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd, Category.comp_id]⟩ :
      SchemeHomOver t H.X.hom)
  simpa only [hA, hB] using hm

/-- A descended relative homomorphism determines an actual internal group morphism. -/
def unbaseGroupHom (φ : pullback G.X.hom (𝟙 _) ⟶ H.X.left)
    (hφ : φ ≫ H.X.hom = pullback.snd G.X.hom (𝟙 _) ≫ 𝟙 _)
    (hmul : RespectsMul (GroupScheme.law G) (GroupScheme.law H) (𝟙 _) φ hφ) : G ⟶ H := by
  letI : IsMonHom (Over.homMk (unbase φ) (unbase_over φ hφ) : G.X ⟶ H.X) := by
    apply GroupScheme.isMonHom_of_pointMap
    · intro T t
      letI := (GroupScheme.law G).pointGroup t
      letI := (GroupScheme.law H).pointGroup t
      let m : SchemeHomOver t G.X.hom →ₙ* SchemeHomOver t H.X.hom :=
        ⟨pointMap (unbase φ) (unbase_over φ hφ), unbase_mul φ hφ hmul t⟩
      exact map_one m
    · exact unbase_mul φ hφ hmul
  exact Grp.homMk (Over.homMk (unbase φ) (unbase_over φ hφ) : G.X ⟶ H.X)

/-- The actual descended morphism has exactly the expected coefficient extension. -/
theorem fst_unbase (φ : pullback G.X.hom (𝟙 _) ⟶ H.X.left)
    {K : Type} [Field K] (i : k →+* K) :
    pullback.fst G.X.hom (Spec.map (CommRingCat.ofHom i)) ≫ unbase φ =
      changeBase i (𝟙 _) (Spec.map (CommRingCat.ofHom i)) (Category.comp_id _) φ := by
  rw [unbase, changeBase, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, Category.comp_id]
  · simp only [Category.assoc, pullback.lift_snd]
    exact pullback.condition

end SupersingularCurves.Geometry.FrobeniusFiniteFieldHomDescent
