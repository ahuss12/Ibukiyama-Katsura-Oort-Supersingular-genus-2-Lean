/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusFiniteFieldGroupDescentLaw
import SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentEquivariantModel

/-! # Actual abelian varieties over the p²-element fixed field -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SupersingularCurves.Geometry.FrobeniusFiniteFieldGroupDescent
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GoodReductionJacobian NeronModelInfra SchemeFrobenius PerfectFieldVerschiebung
open FrobeniusDescent

variable {K : Type u} [Field K] [IsAlgClosed K] {g : ℕ}
variable (p : ℕ) [Fact p.Prime] [CharP K p] (A : AbelianVariety K g)

/-- Multiplication and the genuine absolute Frobenius descend together. -/
theorem descended_scalar_frobenius {X₀ : Scheme.{u}}
    (c₀ : X₀ ⟶ Spec (CommRingCat.of (fixedField K p 2)))
    (d : A.group.X.left ⟶ X₀)
    (hd : IsPullback d A.group.X.hom c₀
      (Spec.map (CommRingCat.ofHom (algebraMap (fixedField K p 2) K))))
    (τ : A.group.X.left ⟶ A.group.X.left)
    (hτ : (GroupScheme.law A.group).schemeNsmul p ≫ τ =
      absolute p A.group.X.hom ≫ absolute p A.group.X.hom)
    (hτd : τ ≫ d = d)
    (L₀ : RelativeGroupLaw (fixedField K p 2) c₀)
    (hone : ((GroupScheme.law A.group).one (𝟙 _)).1 ≫ d =
        Spec.map (CommRingCat.ofHom (algebraMap (fixedField K p 2) K)) ≫
          (L₀.one (𝟙 _)).1) :
    absolute p c₀ ≫ absolute p c₀ = L₀.schemeNsmul p := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap (fixedField K p 2) K))
  have hb : Flat b ∧ Surjective b :=
    (flat_and_surjective_SpecMap_iff
      (CommRingCat.ofHom (algebraMap (fixedField K p 2) K))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  have : Flat d := MorphismProperty.of_isPullback hd.flip hb.1
  have : Surjective d := MorphismProperty.of_isPullback hd.flip hb.2
  have : QuasiCompact d := MorphismProperty.of_isPullback hd.flip
    (inferInstance : QuasiCompact b)
  apply (cancel_epi d).mp
  have h := Scheme.frobenius_comp d p 1 (Fact.out : p.Prime)
    (globalChar p A.group.X.hom) (globalChar p c₀)
  change absolute p A.group.X.hom ≫ d = d ≫ absolute p c₀ at h
  calc
    d ≫ absolute p c₀ ≫ absolute p c₀ =
        (absolute p A.group.X.hom ≫ absolute p A.group.X.hom) ≫ d := by
      simp only [Category.assoc]
      rw [← Category.assoc d, ← h, Category.assoc, ← h]
    _ = ((GroupScheme.law A.group).schemeNsmul p ≫ τ) ≫ d := by rw [hτ]
    _ = (GroupScheme.law A.group).schemeNsmul p ≫ d := by
      rw [Category.assoc, hτd]
    _ = d ≫ L₀.schemeNsmul p := schemeNsmul_comp_eq d hd L₀
      (GroupScheme.law A.group) A.abelianSchemePropertyBundle hone p

/-- Recovering a relative law as a group scheme recovers all multiplication maps. -/
theorem schemeNsmul_grpObjOverMk {k : Type u} [Field k]
    {X : Scheme.{u}} {c : X ⟶ Spec (CommRingCat.of k)}
    (L : RelativeGroupLaw k c) (n : ℕ) :
    letI := L.grpObjOverMk
    (relativeGroupLawOfGrpObj k c).schemeNsmul n = L.schemeNsmul n := by
  letI := L.grpObjOverMk
  have h : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
      (x : SchemeHomOver t c) (n : ℕ),
      (relativeGroupLawOfGrpObj k c).nsmul t n x = L.nsmul t n x := by
    intro T t x n
    induction n with
    | zero => simp only [RelativeGroupLaw.nsmul_zero, relativeGroupLawOfGrpObj_grpObjOverMk_one]
    | succ n ih =>
      simp only [RelativeGroupLaw.nsmul_succ, relativeGroupLawOfGrpObj_grpObjOverMk_mul, ih]
  exact congrArg Subtype.val (h c RelativeGroupLaw.idPoint n)

end FrobeniusFiniteFieldGroupDescent

namespace AbelianVariety
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GoodReductionJacobian NeronModelInfra SchemeFrobenius PerfectFieldVerschiebung
open FrobeniusDescent FrobeniusFiniteFieldGroupDescent
variable {K : Type u} [Field K] [IsAlgClosed K] {g : ℕ}
variable (A : AbelianVariety K g) (p : ℕ) [Fact p.Prime] [CharP K p]
local instance : Smooth A.group.X.hom := SmoothOfRelativeDimension.smooth g A.group.X.hom

/-- Zero Verschiebung cotangent constructs an actual abelian variety over the
actual p²-element subfield. Its scalar extension recovers the original scheme
and its multiplication on every test scheme. Its p²-power Frobenius is [p]. -/
theorem exists_finiteField_abelian_model_of_verschiebungCotangent_eq_zero
    (hV : GroupScheme.verschiebungCotangent p A.group A.groupScheme_law_commutative = 0) :
    Finite (fixedField K p 2) ∧ Nat.card (fixedField K p 2) = p ^ 2 ∧
    ∃ (A₀ : AbelianVariety (fixedField K p 2) g) (d : A.group.X.left ⟶ A₀.group.X.left),
      ∃ hbase : IsPullback d A.group.X.hom A₀.group.X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap (fixedField K p 2) K))),
      (((GroupScheme.law A.group).one (𝟙 _)).1 ≫ d =
        Spec.map (CommRingCat.ofHom (algebraMap (fixedField K p 2) K)) ≫
          ((GroupScheme.law A₀.group).one (𝟙 _)).1) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
          (x y : SchemeHomOver t A.group.X.hom),
        ((GroupScheme.law A.group).mul t x y).1 ≫ d =
          ((GroupScheme.law A₀.group).mul
            (t ≫ Spec.map (CommRingCat.ofHom (algebraMap (fixedField K p 2) K)))
            ⟨x.1 ≫ d, by rw [Category.assoc, hbase.w, ← Category.assoc, x.2]⟩
            ⟨y.1 ≫ d, by rw [Category.assoc, hbase.w, ← Category.assoc, y.2]⟩).1) ∧
      absolute p A₀.group.X.hom ≫ absolute p A₀.group.X.hom =
        (GroupScheme.law A₀.group).schemeNsmul p := by
  obtain ⟨τ, _, hτ, X₀, c₀, d, hd, hτd⟩ :=
    A.exists_finiteField_equivariant_scheme_model_of_verschiebungCotangent_eq_zero p hV
  obtain ⟨L₀, hA₀, hone⟩ := exists_descended_law p A c₀ d hd τ.hom hτ hτd
  obtain ⟨hs, hp, hc⟩ := descended_properties A c₀ d hd
  let G₀ : GroupScheme (fixedField K p 2) := { X := Over.mk c₀, grp := L₀.grpObjOverMk }
  let A₀ : AbelianVariety (fixedField K p 2) g :=
    { group := G₀
      comm := (L₀.isCommMonObj_grpObjOverMk_iff_mul_comm).mpr (hA₀.isCommutative L₀)
      smooth := hs
      proper := hp
      connected := hc }
  refine ⟨fixedField_finite K p 2 (by decide), fixedField_natCard K p 2 (by decide),
    A₀, d, hd, ?_, ?_, ?_⟩
  · simpa only [A₀, G₀, GroupScheme.law, relativeGroupLawOfGrpObj_grpObjOverMk_one] using hone
  · intro T t x y
    simpa only [A₀, G₀, GroupScheme.law, relativeGroupLawOfGrpObj_grpObjOverMk_mul] using
      mul_comp_eq_of_one_comp_eq d hd L₀ (GroupScheme.law A.group)
        A.abelianSchemePropertyBundle hone t x y
  · letI := L₀.grpObjOverMk
    change absolute p c₀ ≫ absolute p c₀ =
      (relativeGroupLawOfGrpObj (fixedField K p 2) c₀).schemeNsmul p
    rw [schemeNsmul_grpObjOverMk]
    exact descended_scalar_frobenius p A c₀ d hd τ.hom hτ hτd L₀ hone

end AbelianVariety
end SupersingularCurves.Geometry
