/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.ScalarFrobeniusTateQuotient
import SupersingularCurves.Geometry.GroupHomFibre

/-!
# Descending actual morphisms through finite subgroup quotients

An actual homomorphism annihilating the subgroup descends uniquely to an
actual group-scheme homomorphism. If the original morphism is an isogeny,
the descended morphism is an isogeny as well. In particular multiplication
by n factors through a subgroup killed by n, and the reverse composition
is multiplication by n on the quotient too.
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

variable {K : Type u} [Field K] {g h : ℕ}

/-- The scheme-point action of an actual group-scheme map preserves products. -/
theorem pointMap_mul {G J : GroupScheme K} (f : G ⟶ J) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t G.X.hom) :
    pointMap (underlyingScheme.map f) f.hom.hom.w ((GroupScheme.law G).mul t x y) =
      (GroupScheme.law J).mul t
        (pointMap (underlyingScheme.map f) f.hom.hom.w x)
        (pointMap (underlyingScheme.map f) f.hom.hom.w y) := by
  have hm := (IsMonHom.monoidHom f.hom.hom (Over.mk t)).map_mul
    (schemeHomOverToOverHom x) (schemeHomOverToOverHom y)
  exact Subtype.ext (congrArg Over.Hom.left hm)

namespace Quotient
variable {A : AbelianVariety K g} {H : FiniteSubgroup A} (D : Quotient A H)
variable {B : AbelianVariety K h} (f : A.group ⟶ B.group)
variable (hk : H.inclusion ≫ underlyingScheme.map f =
  (H.inclusion ≫ A.group.X.hom) ≫ ((GroupScheme.law B.group).one (𝟙 _)).1)

include hk in
private theorem existsUnique_desc_pointMap :
    ∃! ψ : SchemeHomOver D.variety.group.X.hom B.group.X.hom,
      underlyingScheme.map D.map ≫ ψ.1 = underlyingScheme.map f ∧
        ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
          (x y : SchemeHomOver t D.variety.group.X.hom),
          pointMap ψ.1 ψ.2 ((GroupScheme.law D.variety.group).mul t x y) =
            (GroupScheme.law B.group).mul t (pointMap ψ.1 ψ.2 x) (pointMap ψ.1 ψ.2 y) := by
  apply (GroupScheme.law A.group).existsUnique_quotient_desc_hom_of_isColimit
    H.inclusion (underlyingScheme.map D.map) D.coequalizes D.coequalizer.some
    D.map.hom.hom.w (GroupScheme.law D.variety.group) (pointMap_mul D.map)
    (GroupScheme.law B.group) ⟨underlyingScheme.map f, f.hom.hom.w⟩ (pointMap_mul f)
  intro T t e he
  apply Subtype.ext
  change (e ≫ H.inclusion) ≫ underlyingScheme.map f = ((GroupScheme.law B.group).one t).1
  rw [Category.assoc, hk, ← Category.assoc, he]
  exact congrArg Subtype.val ((GroupScheme.law B.group).one_natural (𝟙 _) t t
    (Category.comp_id t))

private def descPointMap : SchemeHomOver D.variety.group.X.hom B.group.X.hom :=
  (D.existsUnique_desc_pointMap f hk).choose

private theorem descPointMap_spec :
    underlyingScheme.map D.map ≫ (D.descPointMap f hk).1 = underlyingScheme.map f ∧
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
        (x y : SchemeHomOver t D.variety.group.X.hom),
        pointMap (D.descPointMap f hk).1 (D.descPointMap f hk).2
          ((GroupScheme.law D.variety.group).mul t x y) =
          (GroupScheme.law B.group).mul t
            (pointMap (D.descPointMap f hk).1 (D.descPointMap f hk).2 x)
            (pointMap (D.descPointMap f hk).1 (D.descPointMap f hk).2 y) :=
  (D.existsUnique_desc_pointMap f hk).choose_spec.1

/-- The actual descended group-scheme homomorphism. -/
def desc : D.variety.group ⟶ B.group := by
  let ψ := D.descPointMap f hk
  have hm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
      (x y : SchemeHomOver t D.variety.group.X.hom),
      pointMap ψ.1 ψ.2 ((GroupScheme.law D.variety.group).mul t x y) =
        (GroupScheme.law B.group).mul t (pointMap ψ.1 ψ.2 x) (pointMap ψ.1 ψ.2 y) :=
    (D.descPointMap_spec f hk).2
  let : IsMonHom (Over.homMk ψ.1 ψ.2 : D.variety.group.X ⟶ B.group.X) :=
    GroupScheme.isMonHom_of_pointMap _ _
      (GroupHomFibre.map_one _ _ _ _ hm) hm
  exact ⟨⟨Over.homMk ψ.1 ψ.2⟩⟩

/-- The descended actual morphism factors the given actual homomorphism. -/
theorem map_desc : D.map ≫ D.desc f hk = f := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  exact (D.descPointMap_spec f hk).1

/-- Uniqueness holds in the category of actual group schemes. -/
theorem desc_unique (ψ : D.variety.group ⟶ B.group) (hψ : D.map ≫ ψ = f) :
    ψ = D.desc f hk := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply (cancel_epi (underlyingScheme.map D.map)).mp
  exact (congrArg (fun k => underlyingScheme.map k) hψ).trans
    ((D.descPointMap_spec f hk).1.symm)

/-- An isogeny descends through the constructed quotient to an isogeny. -/
theorem desc_isIsogeny (hf : IsIsogeny f) : IsIsogeny (D.desc f hk) := by
  let q := underlyingScheme.map D.map
  let ψ := underlyingScheme.map (D.desc f hk)
  have heq : q ≫ ψ = underlyingScheme.map f :=
    congrArg (fun k => underlyingScheme.map k) (D.map_desc f hk)
  have hbase : ψ ≫ B.group.X.hom = D.variety.group.X.hom := (D.desc f hk).hom.hom.w
  have : IsProper (ψ ≫ B.group.X.hom) := hbase.symm ▸ D.variety.proper
  have : IsProper ψ := IsProper.of_comp ψ B.group.X.hom
  have : IsFinite (q ≫ ψ) := heq.symm ▸ hf.1
  have : Surjective (q ≫ ψ) := heq.symm ▸ hf.2
  exact ⟨FiniteFlatFactor.isFinite q ψ, Surjective.of_comp q ψ⟩

/-- Flatness descends along the actual faithfully flat quotient map. -/
theorem desc_flat [Flat (underlyingScheme.map f)] :
    Flat (underlyingScheme.map (D.desc f hk)) := by
  have heq : underlyingScheme.map D.map ≫ underlyingScheme.map (D.desc f hk) =
      underlyingScheme.map f := congrArg (fun k => underlyingScheme.map k) (D.map_desc f hk)
  have : Flat (underlyingScheme.map D.map ≫ underlyingScheme.map (D.desc f hk)) :=
    heq.symm ▸ (inferInstance : Flat (underlyingScheme.map f))
  exact Flat.of_comp_of_flat_of_surjective (underlyingScheme.map D.map) _

end Quotient

/-- Multiplication by n as an actual internal group-scheme homomorphism. -/
def multiplication (A : AbelianVariety K g) (n : ℕ) : A.group ⟶ A.group := by
  let L := GroupScheme.law A.group
  let ψ := L.schemeNsmul n
  have hp {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
      (x : SchemeHomOver t A.group.X.hom) :
      pointMap ψ (L.schemeNsmul_over n) x = L.nsmul t n x := by
    apply Subtype.ext
    exact (SchemeFrobenius.nsmul_point A.group.X.hom L t n x).symm
  let : IsMonHom (Over.homMk ψ (L.schemeNsmul_over n) : A.group.X ⟶ A.group.X) := by
    apply GroupScheme.isMonHom_of_pointMap
    · intro T t
      rw [hp, L.nsmul_unit]
    · intro T t x y
      rw [hp, hp, hp]
      letI : CommGroup (SchemeHomOver t A.group.X.hom) :=
        { L.pointGroup t with mul_comm := fun a b => A.groupScheme_law_commutative t a b }
      have hpow : ∀ (m : ℕ) (a : SchemeHomOver t A.group.X.hom), L.nsmul t m a = a ^ m := by
        intro m a
        induction m with
        | zero => rfl
        | succ m ih =>
          change L.mul t (L.nsmul t m a) a = a ^ (m + 1)
          rw [ih]
          exact (pow_succ a m).symm
      rw [hpow, hpow, hpow]
      exact mul_pow x y n
  exact ⟨⟨Over.homMk ψ (L.schemeNsmul_over n)⟩⟩

@[simp] theorem multiplication_left (A : AbelianVariety K g) (n : ℕ) :
    underlyingScheme.map (multiplication A n) = (GroupScheme.law A.group).schemeNsmul n := rfl

/-- Actual multiplication by a positive integer is an isogeny over an
algebraically closed field, including characteristic-divisible integers. -/
theorem multiplication_isIsogeny [IsAlgClosed K] (A : AbelianVariety K g)
    (n : ℕ) (hn : n ≠ 0) : IsIsogeny (multiplication A n) :=
  ⟨(A.multiplication_finite_flat_degree n hn).2.2.1,
    ⟨(A.multiplication_finite_flat_degree n hn).2.2.2.2.1⟩⟩

namespace Quotient
variable {A : AbelianVariety K g} {H : FiniteSubgroup A} (D : Quotient A H)
variable (n : ℕ) (hk : H.inclusion ≫ (GroupScheme.law A.group).schemeNsmul n =
  (H.inclusion ≫ A.group.X.hom) ≫ ((GroupScheme.law A.group).one (𝟙 _)).1)

/-- The actual residual multiplication map from the quotient back to A. -/
def multiplicationFactor : D.variety.group ⟶ A.group := D.desc (multiplication A n) hk

theorem map_multiplicationFactor : D.map ≫ D.multiplicationFactor n hk = multiplication A n :=
  D.map_desc _ _

/-- The reverse composition is also actual multiplication on the quotient. -/
theorem multiplicationFactor_map :
    D.multiplicationFactor n hk ≫ D.map = multiplication D.variety n := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply (cancel_epi (underlyingScheme.map D.map)).mp
  change underlyingScheme.map D.map ≫
    (underlyingScheme.map (D.multiplicationFactor n hk) ≫ underlyingScheme.map D.map) =
    underlyingScheme.map D.map ≫ (GroupScheme.law D.variety.group).schemeNsmul n
  rw [← Category.assoc]
  have hcomp := congrArg (fun k => underlyingScheme.map k) (D.map_multiplicationFactor n hk)
  change underlyingScheme.map D.map ≫ underlyingScheme.map (D.multiplicationFactor n hk) =
    (GroupScheme.law A.group).schemeNsmul n at hcomp
  rw [hcomp]
  exact GroupScheme.schemeNsmul_natural D.map n

theorem multiplicationFactor_isIsogeny [IsAlgClosed K] (hn : n ≠ 0) :
    IsIsogeny (D.multiplicationFactor n hk) :=
  D.desc_isIsogeny _ _ (multiplication_isIsogeny A n hn)

/-- The exact degree formula for the actual residual multiplication map. -/
theorem subgroup_rank_mul_multiplicationFactor_finrank [IsAlgClosed K] (hn : n ≠ 0)
    (x : A.group.X.left) :
    (H.inclusion ≫ A.group.X.hom).finrank (IsLocalRing.closedPoint K) *
      (underlyingScheme.map (D.multiplicationFactor n hk)).finrank x = n ^ (2 * g) := by
  let : IsFinite (underlyingScheme.map (D.multiplicationFactor n hk)) :=
    (D.multiplicationFactor_isIsogeny n hk hn).1
  let : Flat (underlyingScheme.map (multiplication A n)) :=
    (A.multiplication_finite_flat_degree n hn).2.2.2.1
  let : Flat (underlyingScheme.map (D.multiplicationFactor n hk)) :=
    D.desc_flat (multiplication A n) hk
  have heq : underlyingScheme.map D.map ≫ underlyingScheme.map (D.multiplicationFactor n hk) =
      (GroupScheme.law A.group).schemeNsmul n :=
    congrArg (fun k => underlyingScheme.map k) (D.map_multiplicationFactor n hk)
  have hdeg := Scheme.Hom.finrank_comp_of_finrank_eq_const
    (underlyingScheme.map D.map) (underlyingScheme.map (D.multiplicationFactor n hk))
    ((H.inclusion ≫ A.group.X.hom).finrank (IsLocalRing.closedPoint K))
    D.finrank_eq_subgroup x
  rw [heq] at hdeg
  exact hdeg.symm.trans ((A.multiplication_finite_flat_degree n hn).2.2.2.2.2 x)

end Quotient
end SupersingularCurves.Geometry.ScalarFrobeniusTate
