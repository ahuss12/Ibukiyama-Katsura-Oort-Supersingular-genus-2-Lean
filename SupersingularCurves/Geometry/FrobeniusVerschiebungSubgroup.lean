/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.AbelianMultiplicationDegree
import SupersingularCurves.Geometry.EllipticVerschiebungKernel
import SupersingularCurves.Geometry.FiniteGeometricPoints

/-!
# The actual simultaneous Frobenius and Verschiebung kernel

We construct the closed subgroup `ker F ∩ ker V` inside the actual Frobenius
twist of an abelian variety. Its structure morphism is finite and flat. Its
functor of points is characterized on every test scheme, including nonreduced
ones. In particular the construction retains the infinitesimal subgroup.

No order, quotient, or superspecial classification is asserted here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian SchemeFrobenius PerfectFieldVerschiebung

variable {K : Type u} [Field K]

private theorem one_coe {X : Scheme.{u}} {c : X ⟶ Spec (CommRingCat.of K)}
    (L : RelativeGroupLaw K c) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) :
    (L.one t).1 = t ≫ (L.one (𝟙 _)).1 :=
  (congrArg Subtype.val (L.one_natural (𝟙 _) t t (Category.comp_id t))).symm

variable (p : ℕ) [Fact p.Prime] [CharP K p] [IsAlgClosed K]
variable {g : ℕ} (A : AbelianVariety K g)

abbrev base : Twist p A.group.X.hom ⟶ Spec (CommRingCat.of K) :=
  toBase p A.group.X.hom

local instance base_isProper : IsProper (base p A) := by
  change IsProper (pullback.snd A.group.X.hom (baseMap p K))
  infer_instance

abbrev law : RelativeGroupLaw K (base p A) :=
  twistLaw p A.group.X.hom (GroupScheme.law A.group)

abbrev V : Twist p A.group.X.hom ⟶ A.group.X.left :=
  verschiebung p A.group.X.hom (GroupScheme.law A.group)
    A.groupScheme_law_commutative

abbrev F : Twist p A.group.X.hom ⟶ Twist p (base p A) :=
  relative p (base p A)

abbrev zero : Spec (CommRingCat.of K) ⟶ A.group.X.left :=
  ((GroupScheme.law A.group).one (𝟙 _)).1

abbrev twistZero : Spec (CommRingCat.of K) ⟶ Twist p A.group.X.hom :=
  ((law p A).one (𝟙 _)).1

abbrev twiceTwistZero : Spec (CommRingCat.of K) ⟶ Twist p (base p A) :=
  ((twistLaw p (base p A) (law p A)).one (𝟙 _)).1

abbrev vKernel : Scheme.{u} := pullback (V p A) (zero A)

abbrev vInclusion : vKernel p A ⟶ Twist p A.group.X.hom :=
  pullback.fst (V p A) (zero A)

abbrev vToBase : vKernel p A ⟶ Spec (CommRingCat.of K) :=
  pullback.snd (V p A) (zero A)

/-- The scheme-theoretic simultaneous kernel, formed by two actual fibres. -/
abbrev scheme : Scheme.{u} :=
  pullback (vInclusion p A ≫ F p A) (twiceTwistZero p A)

/-- Its closed immersion into the original Frobenius twist. -/
def inclusion : scheme p A ⟶ Twist p A.group.X.hom :=
  pullback.fst (vInclusion p A ≫ F p A) (twiceTwistZero p A) ≫ vInclusion p A

def toBase : scheme p A ⟶ Spec (CommRingCat.of K) :=
  inclusion p A ≫ base p A

theorem vInclusion_over : vInclusion p A ≫ base p A = vToBase p A := by
  change vInclusion p A ≫ SchemeFrobenius.toBase p A.group.X.hom = _
  rw [← verschiebung_over p A.group.X.hom (GroupScheme.law A.group)
    A.groupScheme_law_commutative, ← Category.assoc]
  change (pullback.fst _ _ ≫ V p A) ≫ A.group.X.hom = _
  rw [pullback.condition, Category.assoc,
    ((GroupScheme.law A.group).one (𝟙 _)).2, Category.comp_id]

instance vInclusion_isClosedImmersion : IsClosedImmersion (vInclusion p A) := by
  let : IsClosedImmersion (zero A) := isClosedImmersion_of_comp_eq_id
    A.group.X.hom (zero A) ((GroupScheme.law A.group).one (𝟙 _)).2
  infer_instance

instance vToBase_isFinite : IsFinite (vToBase p A) := by
  let := A.verschiebung_isFinite p
  infer_instance

instance inclusion_isClosedImmersion : IsClosedImmersion (inclusion p A) := by
  let : IsSeparated (SchemeFrobenius.toBase p (base p A)) := by
    change IsSeparated (pullback.snd (base p A) (baseMap p K))
    infer_instance
  let : IsClosedImmersion (twiceTwistZero p A) := isClosedImmersion_of_comp_eq_id
    (SchemeFrobenius.toBase p (base p A)) (twiceTwistZero p A)
    ((twistLaw p (base p A) (law p A)).one (𝟙 _)).2
  unfold inclusion
  infer_instance

instance structure_isFinite : IsFinite (toBase p A) := by
  have h : toBase p A =
      pullback.fst (vInclusion p A ≫ F p A) (twiceTwistZero p A) ≫ vToBase p A := by
    unfold toBase inclusion
    rw [Category.assoc, vInclusion_over]
  rw [h]
  let : IsSeparated (SchemeFrobenius.toBase p (base p A)) := by
    change IsSeparated (pullback.snd (base p A) (baseMap p K))
    infer_instance
  let : IsClosedImmersion (twiceTwistZero p A) := isClosedImmersion_of_comp_eq_id
    (SchemeFrobenius.toBase p (base p A)) (twiceTwistZero p A)
    ((twistLaw p (base p A) (law p A)).one (𝟙 _)).2
  infer_instance

instance structure_flat : Flat (toBase p A) := inferInstance

instance structure_locallyOfFinitePresentation : LocallyOfFinitePresentation (toBase p A) :=
  inferInstance

theorem structure_eq_snd : toBase p A =
    pullback.snd (vInclusion p A ≫ F p A) (twiceTwistZero p A) := by
  have hF : F p A ≫ SchemeFrobenius.toBase p (base p A) = base p A :=
    relative_toBase p (base p A)
  have h := congrArg (fun f : scheme p A ⟶ Twist p (base p A) =>
    f ≫ SchemeFrobenius.toBase p (base p A))
      (pullback.condition (f := vInclusion p A ≫ F p A) (g := twiceTwistZero p A))
  simp only [Category.assoc, hF,
    ((twistLaw p (base p A) (law p A)).one (𝟙 _)).2, Category.comp_id] at h
  exact (Category.assoc _ _ _).trans h

/-- Frobenius vanishes on this actual closed subscheme. -/
theorem inclusion_frobenius :
    inclusion p A ≫ F p A = toBase p A ≫ twiceTwistZero p A := by
  rw [structure_eq_snd]
  exact (Category.assoc _ _ _).trans pullback.condition

/-- Verschiebung vanishes on this actual closed subscheme. -/
theorem inclusion_verschiebung :
    inclusion p A ≫ V p A = toBase p A ≫ zero A := by
  dsimp only [toBase, inclusion]
  rw [Category.assoc, show vInclusion p A ≫ V p A = vToBase p A ≫ zero A from
    pullback.condition]
  simpa only [Category.assoc] using congrArg
    (fun f => pullback.fst (vInclusion p A ≫ F p A) (twiceTwistZero p A) ≫ f ≫ zero A)
    (vInclusion_over p A).symm

/-- The universal property holds on every test scheme, so it detects the
infinitesimal kernel as well as geometric points. -/
theorem factors_iff {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x : SchemeHomOver t (base p A)) :
    (∃ e : T ⟶ scheme p A, e ≫ inclusion p A = x.1) ↔
      x.1 ≫ F p A = t ≫ twiceTwistZero p A ∧
        x.1 ≫ V p A = t ≫ zero A := by
  constructor
  · rintro ⟨e, he⟩
    have ht : e ≫ toBase p A = t := by
      change e ≫ inclusion p A ≫ base p A = t
      rw [← Category.assoc, he, x.2]
    constructor
    · rw [← he, Category.assoc, inclusion_frobenius, ← Category.assoc, ht]
    · rw [← he, Category.assoc, inclusion_verschiebung, ← Category.assoc, ht]
  · rintro ⟨hF, hV⟩
    let y : T ⟶ vKernel p A := pullback.lift x.1 t hV
    have hy : y ≫ vInclusion p A = x.1 := pullback.lift_fst _ _ _
    let e : T ⟶ scheme p A := pullback.lift y t (by rw [← Category.assoc, hy, hF])
    refine ⟨e, ?_⟩
    change e ≫ pullback.fst _ _ ≫ vInclusion p A = x.1
    rw [← Category.assoc, pullback.lift_fst]
    exact hy

theorem factors_iff_points {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x : SchemeHomOver t (base p A)) :
    (∃ e : T ⟶ scheme p A, e ≫ inclusion p A = x.1) ↔
      relativePoint p (base p A) x = (twistLaw p (base p A) (law p A)).one t ∧
        verschiebungPoint p A.group.X.hom (GroupScheme.law A.group)
          A.groupScheme_law_commutative x = (GroupScheme.law A.group).one t := by
  rw [factors_iff]
  constructor
  · rintro ⟨hF, hV⟩
    exact ⟨Subtype.ext (hF.trans (one_coe _ t).symm),
      Subtype.ext (hV.trans (one_coe _ t).symm)⟩
  · rintro ⟨hF, hV⟩
    exact ⟨(congrArg Subtype.val hF).trans (one_coe _ t),
      (congrArg Subtype.val hV).trans (one_coe _ t)⟩

private theorem verschiebungPoint_one {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) :
    verschiebungPoint p A.group.X.hom (GroupScheme.law A.group)
      A.groupScheme_law_commutative ((law p A).one t) =
        (GroupScheme.law A.group).one t := by
  apply Subtype.ext
  change ((law p A).one t).1 ≫ V p A = _
  rw [one_coe, Category.assoc]
  exact (congrArg (fun f => t ≫ f) (verschiebung_zero p A.group.X.hom
    (GroupScheme.law A.group) A.groupScheme_law_commutative)).trans (one_coe _ t).symm

/-- The identity section factors through the actual simultaneous kernel. -/
theorem one_factors {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) :
    ∃ e : T ⟶ scheme p A, e ≫ inclusion p A = ((law p A).one t).1 := by
  apply (factors_iff_points p A t _).mpr
  exact ⟨relative_one p (base p A) (law p A) t, verschiebungPoint_one p A t⟩

/-- This closed subscheme is stable under the actual group multiplication. -/
theorem mul_factors {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t (base p A))
    (hx : ∃ e : T ⟶ scheme p A, e ≫ inclusion p A = x.1)
    (hy : ∃ e : T ⟶ scheme p A, e ≫ inclusion p A = y.1) :
    ∃ e : T ⟶ scheme p A, e ≫ inclusion p A = ((law p A).mul t x y).1 := by
  obtain ⟨hxF, hxV⟩ := (factors_iff_points p A t x).mp hx
  obtain ⟨hyF, hyV⟩ := (factors_iff_points p A t y).mp hy
  apply (factors_iff_points p A t _).mpr
  constructor
  · rw [relative_mul, hxF, hyF, (twistLaw p (base p A) (law p A)).one_mul]
  · rw [verschiebung_mul, hxV, hyV, (GroupScheme.law A.group).one_mul]

omit [IsAlgClosed K] in
private theorem map_inv_of_mul {X Y : Scheme.{u}}
    {c : X ⟶ Spec (CommRingCat.of K)} {d : Y ⟶ Spec (CommRingCat.of K)}
    (L : RelativeGroupLaw K c) (M : RelativeGroupLaw K d)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (f : SchemeHomOver t c → SchemeHomOver t d)
    (h1 : f (L.one t) = M.one t)
    (hm : ∀ x y, f (L.mul t x y) = M.mul t (f x) (f y))
    (x : SchemeHomOver t c) : f (L.inv t x) = M.inv t (f x) := by
  let := L.pointGroup t
  let := M.pointGroup t
  let φ : SchemeHomOver t c →* SchemeHomOver t d :=
    { toFun := f, map_one' := h1, map_mul' := hm }
  exact φ.map_inv x

/-- This closed subscheme is stable under the actual inverse morphism. -/
theorem inv_factors {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x : SchemeHomOver t (base p A))
    (hx : ∃ e : T ⟶ scheme p A, e ≫ inclusion p A = x.1) :
    ∃ e : T ⟶ scheme p A, e ≫ inclusion p A = ((law p A).inv t x).1 := by
  obtain ⟨hxF, hxV⟩ := (factors_iff_points p A t x).mp hx
  apply (factors_iff_points p A t _).mpr
  constructor
  · rw [map_inv_of_mul (law p A) (twistLaw p (base p A) (law p A)) t
      (relativePoint p (base p A)) (relative_one p (base p A) (law p A) t)
      (relative_mul p (base p A) (law p A) t), hxF]
    let := (twistLaw p (base p A) (law p A)).pointGroup t
    exact inv_one
  · rw [map_inv_of_mul (law p A) (GroupScheme.law A.group) t
      (verschiebungPoint p A.group.X.hom (GroupScheme.law A.group)
        A.groupScheme_law_commutative) (verschiebungPoint_one p A t)
      (verschiebung_mul p A.group.X.hom (GroupScheme.law A.group)
        A.groupScheme_law_commutative t), hxV]
    let := (GroupScheme.law A.group).pointGroup t
    exact inv_one

/-- The simultaneous kernel is annihilated by multiplication by `p` as a
scheme morphism, including on nonreduced test schemes. -/
theorem inclusion_nsmul : inclusion p A ≫ (law p A).schemeNsmul p =
    toBase p A ≫ twistZero p A := by
  have h := verschiebung_frobenius p A.group.X.hom (GroupScheme.law A.group)
    A.groupScheme_law_commutative
  change V p A ≫ relative p A.group.X.hom = (law p A).schemeNsmul p at h
  rw [← h, ← Category.assoc, inclusion_verschiebung, Category.assoc]
  exact congrArg (fun f => toBase p A ≫ f)
    (congrArg Subtype.val (relative_one p A.group.X.hom (GroupScheme.law A.group) (𝟙 _)))

/-- The actual identity point of this finite scheme. -/
def identityPoint : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (toBase p A) :=
  ⟨Classical.choose (one_factors p A (𝟙 _)), by
    change Classical.choose (one_factors p A (𝟙 _)) ≫ inclusion p A ≫ base p A = _
    rw [← Category.assoc, Classical.choose_spec (one_factors p A (𝟙 _))]
    exact ((law p A).one (𝟙 _)).2⟩

theorem identityPoint_inclusion :
    (identityPoint p A).1 ≫ inclusion p A = twistZero p A :=
  Classical.choose_spec (one_factors p A (𝟙 _))

/-- There is only one rational point, although the finite scheme can carry
nontrivial nilpotents. This follows from Frobenius itself. -/
theorem unique_point
    (q : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (toBase p A)) :
    q = identityPoint p A := by
  let x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (base p A) :=
    ⟨q.1 ≫ inclusion p A, by rw [Category.assoc]; exact q.2⟩
  have hx := ((factors_iff_points p A (𝟙 _) x).mp ⟨q.1, rfl⟩).1
  have hx0 : x = (law p A).one (𝟙 _) :=
    (relativePoint_injective p (base p A))
      (hx.trans (relative_one p (base p A) (law p A) (𝟙 _)).symm)
  apply Subtype.ext
  apply (cancel_mono (inclusion p A)).mp
  exact (congrArg Subtype.val hx0).trans (identityPoint_inclusion p A).symm

/-- The underlying topological space of the actual finite kernel is a point. -/
theorem subsingleton : Subsingleton (scheme p A) :=
  FiniteGeometricPoints.subsingleton_of_unique_point (toBase p A)
    (identityPoint p A) (unique_point p A)

end SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup
