/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.ScalarFrobeniusTateQuotientDescent
import Theorems.Thm_HopfAlgebra_exists_quotientFlag_of_galoisStableChain_of_fixedPoints

/-!
# Hopf quotients as actual closed finite flat subgroups

A surjective Hopf-algebra map defines an actual closed group subscheme.
Composing it with an actual closed group-scheme immersion into an abelian
variety supplies the all-test-scheme subgroup data required by the quotient
construction. The subgroup has the coordinate algebra's exact scheme rank.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
universe u

namespace SupersingularCurves.Geometry.ScalarFrobeniusTate
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian FrobeniusFactorGroup
open scoped CategoryTheory.MonObj
variable {K : Type u} [Field K] {g : ℕ} (A : AbelianVariety K g)

/-- A genuine finite group-scheme immersion supplies subgroup closure on
every test scheme automatically. -/
def FiniteSubgroup.ofHom {G : GroupScheme K} (i : G ⟶ A.group)
    [IsClosedImmersion (underlyingScheme.map i)] [IsFinite G.X.hom]
    [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom] : FiniteSubgroup A where
  carrier := G.X.left
  inclusion := underlyingScheme.map i
  closed := inferInstance
  finite := i.hom.hom.w.symm ▸ (inferInstance : IsFinite G.X.hom)
  flat := i.hom.hom.w.symm ▸ (inferInstance : Flat G.X.hom)
  lfp := i.hom.hom.w.symm ▸ (inferInstance : LocallyOfFinitePresentation G.X.hom)
  one := by
    intro T t
    refine ⟨((GroupScheme.law G).one t).1, ?_⟩
    exact congrArg Subtype.val
      (GroupHomFibre.map_one _ _ _ i.hom.hom.w (pointMap_mul i) t)
  mul := by
    intro T t x y hx hy
    obtain ⟨e₁, he₁⟩ := hx
    obtain ⟨e₂, he₂⟩ := hy
    have hi : underlyingScheme.map i ≫ A.group.X.hom = G.X.hom := i.hom.hom.w
    let x' : SchemeHomOver t G.X.hom := ⟨e₁, by
      rw [← hi, ← Category.assoc, he₁, x.2]⟩
    let y' : SchemeHomOver t G.X.hom := ⟨e₂, by
      rw [← hi, ← Category.assoc, he₂, y.2]⟩
    refine ⟨((GroupScheme.law G).mul t x' y').1, ?_⟩
    have h₁ : pointMap (underlyingScheme.map i) i.hom.hom.w x' = x := Subtype.ext he₁
    have h₂ : pointMap (underlyingScheme.map i) i.hom.hom.w y' = y := Subtype.ext he₂
    exact congrArg Subtype.val ((pointMap_mul i t x' y').trans (by rw [h₁, h₂]))
  inv := by
    intro T t x hx
    obtain ⟨e, he⟩ := hx
    have hi : underlyingScheme.map i ≫ A.group.X.hom = G.X.hom := i.hom.hom.w
    let x' : SchemeHomOver t G.X.hom := ⟨e, by
      rw [← hi, ← Category.assoc, he, x.2]⟩
    refine ⟨((GroupScheme.law G).inv t x').1, ?_⟩
    have h₁ : pointMap (underlyingScheme.map i) i.hom.hom.w x' = x := Subtype.ext he
    exact congrArg Subtype.val
      ((GroupHomFibre.map_inv _ _ _ i.hom.hom.w (pointMap_mul i) t x').trans (congrArg ((GroupScheme.law A.group).inv t) h₁))

/-- The actual affine group scheme of a commutative Hopf algebra. -/
def hopfGroup (B : Type u) [CommRing B] [HopfAlgebra K B] : GroupScheme K :=
  (hopfSpec (CommRingCat.of K)).obj (Opposite.op (CommHopfAlgCat.of K B))

/-- Every actual finite group scheme has an actual finite Hopf presentation,
including a group-scheme isomorphism, by the affine Hopf equivalence. -/
theorem exists_finite_hopf_presentation (G : GroupScheme K) [IsFinite G.X.hom] :
    ∃ (B : Type u) (_ : CommRing B) (_ : HopfAlgebra K B),
      Module.Finite K B ∧ Nonempty (hopfGroup (K := K) B ≅ G) := by
  have haff : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨B, ⟨e⟩⟩ := (essImage_hopfSpec (R := CommRingCat.of K)).mpr haff
  have hbase : underlyingScheme.map e.hom ≫ G.X.hom =
      ((hopfSpec (CommRingCat.of K)).obj B).X.hom := e.hom.hom.hom.w
  have hfin : IsFinite (underlyingScheme.map e.hom ≫ G.X.hom) := inferInstance
  rw [hbase] at hfin
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K B.unop))) at hfin
  have hmod : Module.Finite K B.unop := RingHom.finite_algebraMap.mp
    ((IsFinite.SpecMap_iff _).mp hfin)
  exact ⟨B.unop, inferInstance, inferInstance, hmod, ⟨e⟩⟩

/-- Contravariance of the actual affine-group functor. -/
def hopfGroupMap {B C : Type u} [CommRing B] [CommRing C]
    [HopfAlgebra K B] [HopfAlgebra K C] (π : B →ₐc[K] C) :
    hopfGroup (K := K) C ⟶ hopfGroup (K := K) B :=
  (hopfSpec (CommRingCat.of K)).map (CommHopfAlgCat.ofHom π).op

@[simp] theorem hopfGroupMap_left {B C : Type u} [CommRing B] [CommRing C]
    [HopfAlgebra K B] [HopfAlgebra K C] (π : B →ₐc[K] C) :
    underlyingScheme.map (hopfGroupMap π) =
      Spec.map (CommRingCat.ofHom (π : B →ₐ[K] C).toRingHom) := rfl

/-- A Hopf quotient of a presented finite subgroup constructs an actual
closed finite flat subgroup of the original abelian variety. -/
def FiniteSubgroup.ofHopfQuotient
    {B C : Type u} [CommRing B] [CommRing C]
    [HopfAlgebra K B] [HopfAlgebra K C] [Module.Finite K C]
    (i : hopfGroup (K := K) B ⟶ A.group)
    [IsClosedImmersion (underlyingScheme.map i)]
    (π : B →ₐc[K] C) (hπ : Function.Surjective π) : FiniteSubgroup A := by
  let : IsClosedImmersion (underlyingScheme.map (hopfGroupMap π)) :=
    IsClosedImmersion.spec_of_surjective _ hπ
  let : IsClosedImmersion (underlyingScheme.map (hopfGroupMap π ≫ i)) := by
    rw [Functor.map_comp]
    infer_instance
  let : IsFinite (hopfGroup (K := K) C).X.hom := by
    change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K C)))
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  let : Flat (hopfGroup (K := K) C).X.hom := by
    change Flat (Spec.map (CommRingCat.ofHom (algebraMap K C)))
    infer_instance
  let : LocallyOfFinitePresentation (hopfGroup (K := K) C).X.hom := by
    change LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap K C)))
    let : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K C))) :=
      (inferInstance : IsFinite (hopfGroup (K := K) C).X.hom)
    infer_instance
  exact FiniteSubgroup.ofHom A (hopfGroupMap π ≫ i)

/-- The actual subgroup rank is the dimension of the quotient Hopf algebra. -/
theorem FiniteSubgroup.ofHopfQuotient_finrank
    {B C : Type u} [CommRing B] [CommRing C]
    [HopfAlgebra K B] [HopfAlgebra K C] [Module.Finite K C]
    (i : hopfGroup (K := K) B ⟶ A.group)
    [IsClosedImmersion (underlyingScheme.map i)]
    (π : B →ₐc[K] C) (hπ : Function.Surjective π)
    (s : Spec (CommRingCat.of K)) :
    ((FiniteSubgroup.ofHopfQuotient A i π hπ).inclusion ≫ A.group.X.hom).finrank s =
      Module.finrank K C := by
  have heq : (FiniteSubgroup.ofHopfQuotient A i π hπ).inclusion ≫ A.group.X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap K C)) := (hopfGroupMap π ≫ i).hom.hom.w
  rw [heq, Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
  rfl

/-- A subgroup of rational points of a finite Hopf algebra defines an actual
Hopf quotient with exactly that rank. In particular this applies to all
geometric points when the ground field is algebraically closed. -/
theorem exists_hopf_quotient_of_point_subgroup
    {K : Type} [Field K] (B : Type) [CommRing B] [HopfAlgebra K B] [Module.Finite K B]
    (M : Type) [AddCommGroup M] [Finite M]
    (e : WithConv (B →ₐ[K] K) ≃ M)
    (he : ∀ f g, e (f * g) = e f + e g) (N : AddSubgroup M) :
    ∃ (C : Type) (_ : CommRing C) (_ : HopfAlgebra K C),
      Module.Finite K C ∧ Module.finrank K C = Nat.card N ∧
      ∃ π : B →ₐc[K] C, Function.Surjective π ∧
        ∀ φ : B →ₐ[K] K,
          (∃ ψ : C →ₐ[K] K, ψ.comp (π : B →ₐ[K] C) = φ) ↔ e (.toConv φ) ∈ N := by
  classical
  let Ns : Fin (1 + 1) → AddSubgroup M := ![N, ⊤]
  have hfix : ∀ c : K, (∀ σ : K ≃ₐ[K] K,
      (∀ r : K, σ (algebraMap K K r) = algebraMap K K r) → σ c = c) →
      ∃ a b : K, algebraMap K K b ≠ 0 ∧ c * algebraMap K K b = algebraMap K K a := by
    intro c _
    exact ⟨c, 1, by simp, by simp⟩
  have hact : ∀ (σ : K ≃ₐ[K] K) (f g : WithConv (B →ₐ[K] K)),
      (∀ b : B, g b = σ (f b)) → e g = e f := by
    intro σ f g h
    apply congrArg e
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro b
    exact (h b).trans (by simpa using σ.commutes (f b))
  obtain ⟨Cs, rings, hopfs, πs, φs, hft, hflat, hsurj, hφsurj, hcomp,
      hlast, hfactor, hcocomm, hfin⟩ :=
    HopfAlgebra.exists_quotientFlag_of_galoisStableChain_of_fixedPoints
      (K := K) (L := K) K (algebraMap K K).injective hfix
      B M e he (fun _ x => x) hact 1 Ns
      (by intro i; fin_cases i; exact le_top) rfl (by intros; assumption)
  let := rings
  let := hopfs
  exact ⟨Cs 0, inferInstance, inferInstance, (hfin inferInstance 0).1,
    (hfin inferInstance 0).2 (by decide), πs 0, hsurj 0, hfactor 0⟩

end SupersingularCurves.Geometry.ScalarFrobeniusTate
