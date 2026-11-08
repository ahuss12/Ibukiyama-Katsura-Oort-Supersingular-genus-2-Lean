/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusFactorIsomorphism

/-!
# Group structure on a residual Frobenius factor

The group law on the actual Frobenius twist is preserved by a factor of a
known group morphism. The equality descends along the faithfully flat product
of the actual relative Frobenius with itself.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FrobeniusFactorGroup
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open NeronModelInfra GoodReductionJacobian SchemeFrobenius

variable {K : Type u} [Field K]
variable {X Y : Scheme.{u}}
variable {c : X ⟶ Spec (CommRingCat.of K)} {d : Y ⟶ Spec (CommRingCat.of K)}

/-- Postcomposition with an actual morphism over the base, on every test scheme. -/
def pointMap (f : X ⟶ Y) (hf : f ≫ d = c) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of K)} (x : SchemeHomOver t c) : SchemeHomOver t d :=
  ⟨x.1 ≫ f, by rw [Category.assoc, hf, x.2]⟩

variable (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K] [Smooth c]
variable (L : RelativeGroupLaw K c) (M : RelativeGroupLaw K d)
variable (f : X ⟶ Y) (hf : f ≫ d = c)
variable (W : Twist p c ⟶ Y) (hW : W ≫ d = toBase p c)
variable (hfactor : relative p c ≫ W = f)

local instance : IsFinite (relative p c) := (finite_flat_surjective p c).1
local instance : Flat (relative p c) := (finite_flat_surjective p c).2.1
local instance : Surjective (relative p c) := (finite_flat_surjective p c).2.2.2

include hfactor in
/-- A factor through actual relative Frobenius inherits the group multiplication
law, without an extra preservation assumption on that factor. -/
theorem factor_mul
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
      (x y : SchemeHomOver t c),
      pointMap f hf (L.mul t x y) = M.mul t (pointMap f hf x) (pointMap f hf y))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t (toBase p c)) :
    pointMap W hW ((twistLaw p c L).mul t x y) =
      M.mul t (pointMap W hW x) (pointMap W hW y) := by
  let F := relative p c
  let V := W
  let L' := twistLaw p c L
  let q₁ := pullback.fst (toBase p c) (toBase p c)
  let q₂ := pullback.snd (toBase p c) (toBase p c)
  let r₁ := pullback.fst c c
  let r₂ := pullback.snd c c
  let tU : pullback c c ⟶ Spec (CommRingCat.of K) := r₁ ≫ c
  let tU' : pullback (toBase p c) (toBase p c) ⟶ Spec (CommRingCat.of K) :=
    q₁ ≫ toBase p c
  let u₁ : SchemeHomOver tU c := ⟨r₁, rfl⟩
  let u₂ : SchemeHomOver tU c := ⟨r₂, pullback.condition.symm⟩
  let u₁' : SchemeHomOver tU' (toBase p c) := ⟨q₁, rfl⟩
  let u₂' : SchemeHomOver tU' (toBase p c) := ⟨q₂, pullback.condition.symm⟩
  have hFover : c = F ≫ toBase p c := (relative_toBase p c).symm
  let G : pullback c c ⟶ pullback (toBase p c) (toBase p c) :=
    pullback.map c c (toBase p c) (toBase p c) F F (𝟙 _)
      (by simpa only [Category.comp_id] using hFover)
      (by simpa only [Category.comp_id] using hFover)
  have hG₁ : G ≫ q₁ = r₁ ≫ F := pullback.lift_fst _ _ _
  have hG₂ : G ≫ q₂ = r₂ ≫ F := pullback.lift_snd _ _ _
  have hGt : G ≫ tU' = tU := by
    change G ≫ q₁ ≫ toBase p c = r₁ ≫ c
    rw [← Category.assoc, hG₁, Category.assoc, ← hFover]
  have : Flat G := MorphismProperty.pullbackMap (P := @Flat) inferInstance inferInstance hFover hFover
  have : Surjective G := MorphismProperty.pullbackMap (P := @Surjective.{u})
    (inferInstance : Surjective F) (inferInstance : Surjective F) hFover hFover
  have : QuasiCompact G :=
    MorphismProperty.pullbackMap (P := @QuasiCompact) inferInstance inferInstance hFover hFover
  have hc₁ : GoodReductionJacobian.schemeHomOverComp G hGt u₁' = relativePoint p c u₁ :=
    Subtype.ext hG₁
  have hc₂ : GoodReductionJacobian.schemeHomOverComp G hGt u₂' = relativePoint p c u₂ :=
    Subtype.ext hG₂
  have hv₁ : GoodReductionJacobian.schemeHomOverComp G hGt
      (pointMap W hW u₁') = pointMap f hf u₁ := by
    apply Subtype.ext
    
    change G ≫ q₁ ≫ V = r₁ ≫ f
    rw [← Category.assoc, hG₁, Category.assoc, hfactor]
  have hv₂ : GoodReductionJacobian.schemeHomOverComp G hGt
      (pointMap W hW u₂') = pointMap f hf u₂ := by
    apply Subtype.ext
    
    change G ≫ q₂ ≫ V = r₂ ≫ f
    rw [← Category.assoc, hG₂, Category.assoc, hfactor]
  have key : (L'.mul tU' u₁' u₂').1 ≫ V =
      (M.mul tU' (pointMap W hW u₁')
        (pointMap W hW u₂')).1 := by
    rw [← cancel_epi G]
    have lhs : G ≫ (L'.mul tU' u₁' u₂').1 ≫ V =
        (pointMap f hf (L.mul tU u₁ u₂)).1 := by
      rw [← Category.assoc]
      change (GoodReductionJacobian.schemeHomOverComp G hGt (L'.mul tU' u₁' u₂')).1 ≫ V = _
      rw [L'.mul_natural, hc₁, hc₂, ← relative_mul]
      change ((L.mul tU u₁ u₂).1 ≫ F) ≫ V = _
      rw [Category.assoc, hfactor]
      rfl
    have rhs : G ≫ (M.mul tU' (pointMap W hW u₁')
        (pointMap W hW u₂')).1 =
        (M.mul tU (pointMap f hf u₁) (pointMap f hf u₂)).1 := by
      change (GoodReductionJacobian.schemeHomOverComp G hGt (M.mul tU' _ _)).1 = _
      rw [M.mul_natural, hv₁, hv₂]
    rw [lhs, rhs, hmul]
  let ψ : T ⟶ pullback (toBase p c) (toBase p c) :=
    pullback.lift x.1 y.1 (x.2.trans y.2.symm)
  have hψ : ψ ≫ tU' = t := by
    change ψ ≫ q₁ ≫ toBase p c = t
    rw [← Category.assoc, pullback.lift_fst, x.2]
  have hx : GoodReductionJacobian.schemeHomOverComp ψ hψ u₁' = x :=
    Subtype.ext (pullback.lift_fst _ _ _)
  have hy : GoodReductionJacobian.schemeHomOverComp ψ hψ u₂' = y :=
    Subtype.ext (pullback.lift_snd _ _ _)
  have hVx : GoodReductionJacobian.schemeHomOverComp ψ hψ
      (pointMap W hW u₁') = pointMap W hW x := by
    apply Subtype.ext
    change ψ ≫ q₁ ≫ V = x.1 ≫ V
    rw [← Category.assoc, pullback.lift_fst]
  have hVy : GoodReductionJacobian.schemeHomOverComp ψ hψ
      (pointMap W hW u₂') = pointMap W hW y := by
    apply Subtype.ext
    change ψ ≫ q₂ ≫ V = y.1 ≫ V
    rw [← Category.assoc, pullback.lift_snd]
  apply Subtype.ext
  have hkey := congrArg (fun a => ψ ≫ a) key
  rw [← Category.assoc] at hkey
  change (GoodReductionJacobian.schemeHomOverComp ψ hψ (L'.mul tU' u₁' u₂')).1 ≫ V =
    (GoodReductionJacobian.schemeHomOverComp ψ hψ (M.mul tU' _ _)).1 at hkey
  rw [L'.mul_natural, M.mul_natural, hx, hy, hVx, hVy] at hkey
  exact hkey


include hfactor in
omit [PerfectField K] [Smooth c] in
/-- Identity preservation descends through actual relative Frobenius. -/
theorem factor_one
    (hone : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)),
      pointMap f hf (L.one t) = M.one t)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) :
    pointMap W hW ((twistLaw p c L).one t) = M.one t := by
  apply Subtype.ext
  rw [← relative_one]
  change ((L.one t).1 ≫ relative p c) ≫ W = _
  rw [Category.assoc, hfactor]
  exact congrArg Subtype.val (hone t)

include hf hfactor in
/-- A residual factor of a morphism over the base is itself over the base. -/
theorem factor_over : W ≫ d = toBase p c := by
  apply (cancel_epi (relative p c)).mp
  rw [← Category.assoc, hfactor, hf, relative_toBase]

end SupersingularCurves.Geometry.FrobeniusFactorGroup

namespace SupersingularCurves.Geometry.GroupScheme
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open NeronModelInfra GoodReductionJacobian FrobeniusFactorGroup
open scoped CategoryTheory.MonObj

variable {K : Type u} [Field K] {G H : GroupScheme K}

/-- Pointwise preservation on every test scheme gives a genuine internal
monoid morphism, hence a morphism of the existing group schemes. -/
theorem isMonHom_of_pointMap
    (f : G.X.left ⟶ H.X.left) (hf : f ≫ H.X.hom = G.X.hom)
    (hone : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)),
      pointMap f hf ((law G).one t) = (law H).one t)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
      (x y : SchemeHomOver t G.X.hom),
      pointMap f hf ((law G).mul t x y) =
        (law H).mul t (pointMap f hf x) (pointMap f hf y)) :
    IsMonHom (Over.homMk f hf : G.X ⟶ H.X) := by
  let ff : G.X ⟶ H.X := Over.homMk f hf
  constructor
  · rw [MonObj.one_eq_one, MonObj.one_eq_one]
    apply overHomToSchemeHomOver_injective
    exact hone (𝟙_ (Over (Spec (CommRingCat.of K)))).hom
  · rw [MonObj.mul_eq_mul, MonObj.mul_eq_mul, MonObj.comp_mul]
    have key {T : Over (Spec (CommRingCat.of K))} (a : T ⟶ G.X) :
        schemeHomOverToOverHom (pointMap f hf (overHomToSchemeHomOver a)) =
          a ≫ Over.homMk f hf := by
      apply Over.OverMorphism.ext
      rfl
    have h := hmul (G.X ⊗ G.X).hom
      (overHomToSchemeHomOver (fst G.X G.X))
      (overHomToSchemeHomOver (snd G.X G.X))
    simp only [law, relativeGroupLawOfGrpObj_mul,
      schemeHomOverToOverHom_overHomToSchemeHomOver] at h
    have h' := congrArg schemeHomOverToOverHom h
    simp only [schemeHomOverToOverHom_overHomToSchemeHomOver, key] at h'
    simpa only [tensorHom_fst, tensorHom_snd] using h'

end SupersingularCurves.Geometry.GroupScheme

namespace SupersingularCurves.Geometry.AbelianVariety
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open NeronModelInfra GoodReductionJacobian SchemeFrobenius PerfectFieldVerschiebung
open FrobeniusFactorGroup

variable {K : Type u} [Field K] [IsAlgClosed K] {g : ℕ}
    (A : AbelianVariety K g) (p : ℕ) [Fact p.Prime] [CharP K p]

local instance : Smooth A.group.X.hom := SmoothOfRelativeDimension.smooth g A.group.X.hom
local instance : Smooth (toBase p A.group.X.hom) := by
  change Smooth (pullback.snd A.group.X.hom (baseMap p K))
  infer_instance

/-- The group scheme on the actual iterated Frobenius fibre product,
with the independently base-changed group law. -/
def doubleFrobeniusTwistGroup : GroupScheme K where
  X := Over.mk (toBase p (toBase p A.group.X.hom))
  grp := (twistLaw p (toBase p A.group.X.hom)
    (twistLaw p A.group.X.hom (GroupScheme.law A.group))).grpObjOverMk

variable (W : Twist p (toBase p A.group.X.hom) ⟶ A.group.X.left)
variable (hfactor : relative p (toBase p A.group.X.hom) ≫ W =
  verschiebung p A.group.X.hom (GroupScheme.law A.group) A.groupScheme_law_commutative)

include hfactor in
/-- The over-base identity required to regard the residual factor as a
morphism of group schemes is forced by the factorization. -/
theorem frobeniusFactor_over :
    W ≫ A.group.X.hom = toBase p (toBase p A.group.X.hom) :=
  factor_over p _ (verschiebung_over p A.group.X.hom
    (GroupScheme.law A.group) A.groupScheme_law_commutative) W hfactor

/-- The actual residual factor is a morphism of group objects; multiplication
and identity preservation descend along actual relative Frobenius. -/
theorem frobeniusFactor_isMonHom :
    IsMonHom (Over.homMk W (A.frobeniusFactor_over p W hfactor) :
      (A.doubleFrobeniusTwistGroup p).X ⟶ A.group.X) := by
  apply GroupScheme.isMonHom_of_pointMap
    (G := A.doubleFrobeniusTwistGroup p) (H := A.group) W
  · intro T t
    have h := factor_one p
      (twistLaw p A.group.X.hom (GroupScheme.law A.group))
      (GroupScheme.law A.group)
      (verschiebung p A.group.X.hom (GroupScheme.law A.group) A.groupScheme_law_commutative)
      (verschiebung_over p A.group.X.hom (GroupScheme.law A.group) A.groupScheme_law_commutative)
      W (A.frobeniusFactor_over p W hfactor) hfactor
      (fun t => by
        apply Subtype.ext
        rw [← relative_one]
        change (((GroupScheme.law A.group).one t).1 ≫ relative p A.group.X.hom) ≫
          verschiebung p A.group.X.hom (GroupScheme.law A.group)
            A.groupScheme_law_commutative = _
        rw [Category.assoc, frobenius_verschiebung, ← nsmul_point,
          (GroupScheme.law A.group).nsmul_unit]) t
    simpa only [GroupScheme.law, doubleFrobeniusTwistGroup,
      relativeGroupLawOfGrpObj_grpObjOverMk_one] using h
  · intro T t x y
    have h := factor_mul p
      (twistLaw p A.group.X.hom (GroupScheme.law A.group))
      (GroupScheme.law A.group)
      (verschiebung p A.group.X.hom (GroupScheme.law A.group) A.groupScheme_law_commutative)
      (verschiebung_over p A.group.X.hom (GroupScheme.law A.group) A.groupScheme_law_commutative)
      W (A.frobeniusFactor_over p W hfactor) hfactor
      (fun t x y => verschiebung_mul p A.group.X.hom
        (GroupScheme.law A.group) A.groupScheme_law_commutative t x y) t x y
    simpa only [GroupScheme.law, doubleFrobeniusTwistGroup,
      relativeGroupLawOfGrpObj_grpObjOverMk_mul] using h

/-- The factorization supplies an actual group-scheme isomorphism between
the double Frobenius twist and the original abelian variety. -/
def frobeniusFactorGroupIso : A.doubleFrobeniusTwistGroup p ≅ A.group := by
  have : IsIso W := A.isIso_of_frobenius_factor_verschiebung p W hfactor
  have hW := A.frobeniusFactor_over p W hfactor
  have hm := A.frobeniusFactor_isMonHom p W hfactor
  let e : (A.doubleFrobeniusTwistGroup p).X ≅ A.group.X := Over.isoMk (asIso W) hW
  have : IsMonHom e.hom := hm
  exact Grp.mkIso' e


/-- The bundled group isomorphism has exactly the original residual scheme
morphism as its forward map. -/
@[simp]
theorem frobeniusFactorGroupIso_hom_left :
    (A.frobeniusFactorGroupIso p W hfactor).hom.hom.hom.left = W := rfl

end SupersingularCurves.Geometry.AbelianVariety
