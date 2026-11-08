/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.EllipticTorsionRealization
import SupersingularCurves.Geometry.FrobeniusFactorGroup

/-!
# Actual divisibility of elliptic homomorphisms vanishing on p-torsion

Faithfully flat descent through multiplication by p constructs the quotient
homomorphism. Vanishing is on the entire finite p-torsion scheme. This is the
kernel-of-restriction step in Oort's endomorphism lifting argument; surjectivity
onto the restrictions of arbitrary p-torsion morphisms is a further theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.EllipticTorsionRealization
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian SchemeFrobenius FrobeniusFactorGroup
open scoped CategoryTheory.MonObj

variable {K : Type u} [Field K] [IsAlgClosed K]
variable (p : ℕ) [Fact p.Prime]
variable {E E' : AbelianVariety K 1}

omit [IsAlgClosed K] in
private theorem one_left (G : GroupScheme K) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) :
    (1 : Over.mk t ⟶ G.X).left = t ≫ (GroupScheme.zero G).1 := by
  change ((GroupScheme.law G).one t).1 = _
  exact (congrArg Subtype.val ((GroupScheme.law G).one_natural
    (𝟙 _) t t (Category.comp_id t))).symm

omit [IsAlgClosed K] in
private theorem pow_left (G : GroupScheme K) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (n : ℕ) (x : Over.mk t ⟶ G.X) :
    (x ^ n).left = x.left ≫ (GroupScheme.law G).schemeNsmul n := by
  have h := congrArg Subtype.val (GroupScheme.nsmul_eq_pow G t n x)
  rw [SchemeFrobenius.nsmul_point] at h
  exact h.symm

variable (f : E.group ⟶ E'.group)
variable (hzero : torsionInclusion p E ≫ f.hom.hom.left =
  torsionBase p E ≫ (GroupScheme.zero E'.group).1)

include hzero in
omit [IsAlgClosed K] [Fact p.Prime] in
/-- Vanishing on the actual finite kernel makes the homomorphism constant on
every scheme-theoretic fibre of multiplication by p. -/
theorem coequalizes_multiplication_of_torsion_zero {T : Scheme.{u}}
    (a b : T ⟶ E.group.X.left)
    (hab : a ≫ (GroupScheme.law E.group).schemeNsmul p =
      b ≫ (GroupScheme.law E.group).schemeNsmul p) :
    a ≫ f.hom.hom.left = b ≫ f.hom.hom.left := by
  have habase : a ≫ E.group.X.hom = b ≫ E.group.X.hom := by
    have h := congrArg (fun q => q ≫ E.group.X.hom) hab
    simpa only [Category.assoc, RelativeGroupLaw.schemeNsmul_over] using h
  let t := a ≫ E.group.X.hom
  let x : Over.mk t ⟶ E.group.X := Over.homMk a rfl
  let y : Over.mk t ⟶ E.group.X := Over.homMk b habase.symm
  have hpow : x ^ p = y ^ p := by
    apply Over.OverMorphism.ext
    rw [pow_left, pow_left]
    exact hab
  let z := x * y⁻¹
  have hz : z ^ p = 1 := by
    dsimp only [z]
    rw [mul_pow, inv_pow, hpow, mul_inv_cancel]
  have hzker : z.left ≫ (GroupScheme.law E.group).schemeNsmul p =
      t ≫ (GroupScheme.zero E.group).1 := by
    rw [← pow_left, hz, one_left]
  let k : T ⟶ torsion p E := pullback.lift z.left t hzker
  have hk : z.left ≫ f.hom.hom.left = t ≫ (GroupScheme.zero E'.group).1 := by
    have h := congrArg (fun q => k ≫ q) hzero
    have hk₁ : k ≫ torsionInclusion p E = z.left := pullback.lift_fst _ _ _
    have hk₂ : k ≫ torsionBase p E = t := pullback.lift_snd _ _ _
    simpa only [← Category.assoc, hk₁, hk₂] using h
  let φ := IsMonHom.monoidHom f.hom.hom (Over.mk t)
  have hφ : φ z = 1 := by
    apply Over.OverMorphism.ext
    change z.left ≫ f.hom.hom.left = (1 : Over.mk t ⟶ E'.group.X).left
    rw [one_left]
    exact hk
  have heq : φ x = φ y := by
    have hz' : φ x * (φ y)⁻¹ = 1 := by
      simpa only [z, map_mul, map_inv] using hφ
    exact mul_inv_eq_one.mp hz'
  exact congrArg Over.Hom.left heq

private instance multiplication_isFinite :
    IsFinite ((GroupScheme.law E.group).schemeNsmul p) :=
  (E.multiplication_finite_flat_degree p (Fact.out : p.Prime).ne_zero).2.2.1

private instance multiplication_flat :
    Flat ((GroupScheme.law E.group).schemeNsmul p) :=
  (E.multiplication_finite_flat_degree p (Fact.out : p.Prime).ne_zero).2.2.2.1

private instance multiplication_surjective :
    Surjective ((GroupScheme.law E.group).schemeNsmul p) :=
  ⟨(E.multiplication_finite_flat_degree p (Fact.out : p.Prime).ne_zero).2.2.2.2.1⟩

/-- The actual scheme map descended through multiplication by p. -/
def dividedMap : E.group.X.left ⟶ E'.group.X.left :=
  EffectiveEpi.desc ((GroupScheme.law E.group).schemeNsmul p) f.hom.hom.left
    (coequalizes_multiplication_of_torsion_zero p f hzero)

theorem multiplication_dividedMap :
    (GroupScheme.law E.group).schemeNsmul p ≫ dividedMap p f hzero = f.hom.hom.left :=
  EffectiveEpi.fac _ _ (coequalizes_multiplication_of_torsion_zero p f hzero)

theorem dividedMap_over :
    dividedMap p f hzero ≫ E'.group.X.hom = E.group.X.hom := by
  apply (cancel_epi ((GroupScheme.law E.group).schemeNsmul p)).mp
  rw [← Category.assoc, multiplication_dividedMap, f.hom.hom.w,
    RelativeGroupLaw.schemeNsmul_over]

theorem dividedMap_zero :
    (GroupScheme.zero E.group).1 ≫ dividedMap p f hzero =
      (GroupScheme.zero E'.group).1 := by
  have hp0 : (GroupScheme.zero E.group).1 ≫ (GroupScheme.law E.group).schemeNsmul p =
      (GroupScheme.zero E.group).1 := by
    rw [← SchemeFrobenius.nsmul_point]
    exact congrArg Subtype.val ((GroupScheme.law E.group).nsmul_unit (𝟙 _) p)
  rw [← hp0, Category.assoc, multiplication_dividedMap, GroupScheme.zero_natural]

private theorem dividedMap_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) :
    pointMap (dividedMap p f hzero) (dividedMap_over p f hzero)
      ((GroupScheme.law E.group).one t) = (GroupScheme.law E'.group).one t := by
  apply Subtype.ext
  change (1 : Over.mk t ⟶ E.group.X).left ≫ dividedMap p f hzero =
    (1 : Over.mk t ⟶ E'.group.X).left
  rw [one_left, one_left, Category.assoc, dividedMap_zero]

private theorem dividedMap_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t E.group.X.hom) :
    pointMap (dividedMap p f hzero) (dividedMap_over p f hzero)
        ((GroupScheme.law E.group).mul t x y) =
      (GroupScheme.law E'.group).mul t
        (pointMap (dividedMap p f hzero) (dividedMap_over p f hzero) x)
        (pointMap (dividedMap p f hzero) (dividedMap_over p f hzero) y) := by
  let c := E.group.X.hom
  let L := GroupScheme.law E.group
  let M := GroupScheme.law E'.group
  let W := dividedMap p f hzero
  have hW := dividedMap_over p f hzero
  have hfactor := multiplication_dividedMap p f hzero
  have hmul {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of K))
      (a b : SchemeHomOver t c) :
      pointMap f.hom.hom.left f.hom.hom.w (L.mul t a b) =
        M.mul t (pointMap f.hom.hom.left f.hom.hom.w a)
          (pointMap f.hom.hom.left f.hom.hom.w b) := by
    have h := (IsMonHom.monoidHom f.hom.hom (Over.mk t)).map_mul
      (schemeHomOverToOverHom a) (schemeHomOverToOverHom b)
    exact Subtype.ext (congrArg Over.Hom.left h)
  let F := L.schemeNsmul p
  let V := W
  let L' := L
  let q₁ := pullback.fst (c) (c)
  let q₂ := pullback.snd (c) (c)
  let r₁ := pullback.fst c c
  let r₂ := pullback.snd c c
  let tU : pullback c c ⟶ Spec (CommRingCat.of K) := r₁ ≫ c
  let tU' : pullback (c) (c) ⟶ Spec (CommRingCat.of K) :=
    q₁ ≫ c
  let u₁ : SchemeHomOver tU c := ⟨r₁, rfl⟩
  let u₂ : SchemeHomOver tU c := ⟨r₂, pullback.condition.symm⟩
  let u₁' : SchemeHomOver tU' (c) := ⟨q₁, rfl⟩
  let u₂' : SchemeHomOver tU' (c) := ⟨q₂, pullback.condition.symm⟩
  have hFover : c = F ≫ c := (L.schemeNsmul_over p).symm
  let G : pullback c c ⟶ pullback (c) (c) :=
    pullback.map c c (c) (c) F F (𝟙 _)
      (by simpa only [Category.comp_id] using hFover)
      (by simpa only [Category.comp_id] using hFover)
  have hG₁ : G ≫ q₁ = r₁ ≫ F := pullback.lift_fst _ _ _
  have hG₂ : G ≫ q₂ = r₂ ≫ F := pullback.lift_snd _ _ _
  have hGt : G ≫ tU' = tU := by
    change G ≫ q₁ ≫ c = r₁ ≫ c
    rw [← Category.assoc, hG₁, Category.assoc, ← hFover]
  have : Flat G := MorphismProperty.pullbackMap (P := @Flat) inferInstance inferInstance hFover hFover
  have : Surjective G := MorphismProperty.pullbackMap (P := @Surjective.{u})
    (inferInstance : Surjective F) (inferInstance : Surjective F) hFover hFover
  have : QuasiCompact G :=
    MorphismProperty.pullbackMap (P := @QuasiCompact) inferInstance inferInstance hFover hFover
  have hc₁ : GoodReductionJacobian.schemeHomOverComp G hGt u₁' = L.nsmul tU p u₁ :=
    Subtype.ext (hG₁.trans (nsmul_point c L tU p u₁).symm)
  have hc₂ : GoodReductionJacobian.schemeHomOverComp G hGt u₂' = L.nsmul tU p u₂ :=
    Subtype.ext (hG₂.trans (nsmul_point c L tU p u₂).symm)
  have hv₁ : GoodReductionJacobian.schemeHomOverComp G hGt
      (pointMap W hW u₁') = pointMap f.hom.hom.left f.hom.hom.w u₁ := by
    apply Subtype.ext
    
    change G ≫ q₁ ≫ V = r₁ ≫ f.hom.hom.left
    rw [← Category.assoc, hG₁, Category.assoc, hfactor]
  have hv₂ : GoodReductionJacobian.schemeHomOverComp G hGt
      (pointMap W hW u₂') = pointMap f.hom.hom.left f.hom.hom.w u₂ := by
    apply Subtype.ext
    
    change G ≫ q₂ ≫ V = r₂ ≫ f.hom.hom.left
    rw [← Category.assoc, hG₂, Category.assoc, hfactor]
  have key : (L'.mul tU' u₁' u₂').1 ≫ V =
      (M.mul tU' (pointMap W hW u₁')
        (pointMap W hW u₂')).1 := by
    rw [← cancel_epi G]
    have lhs : G ≫ (L'.mul tU' u₁' u₂').1 ≫ V =
        (pointMap f.hom.hom.left f.hom.hom.w (L.mul tU u₁ u₂)).1 := by
      rw [← Category.assoc]
      change (GoodReductionJacobian.schemeHomOverComp G hGt (L'.mul tU' u₁' u₂')).1 ≫ V = _
      rw [L'.mul_natural, hc₁, hc₂,
        ← PerfectFieldVerschiebung.nsmul_mul c L E.groupScheme_law_commutative]
      rw [nsmul_point]
      change ((L.mul tU u₁ u₂).1 ≫ F) ≫ V = _
      rw [Category.assoc, hfactor]
      rfl
    have rhs : G ≫ (M.mul tU' (pointMap W hW u₁')
        (pointMap W hW u₂')).1 =
        (M.mul tU (pointMap f.hom.hom.left f.hom.hom.w u₁) (pointMap f.hom.hom.left f.hom.hom.w u₂)).1 := by
      change (GoodReductionJacobian.schemeHomOverComp G hGt (M.mul tU' _ _)).1 = _
      rw [M.mul_natural, hv₁, hv₂]
    rw [lhs, rhs, hmul]
  let ψ : T ⟶ pullback (c) (c) :=
    pullback.lift x.1 y.1 (x.2.trans y.2.symm)
  have hψ : ψ ≫ tU' = t := by
    change ψ ≫ q₁ ≫ c = t
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
/-- The divided map is an actual elliptic group homomorphism. -/
def dividedHom : E.group ⟶ E'.group := by
  letI : IsMonHom (Over.homMk (dividedMap p f hzero) (dividedMap_over p f hzero) :
      E.group.X ⟶ E'.group.X) :=
    GroupScheme.isMonHom_of_pointMap _ _ (dividedMap_one p f hzero)
      (dividedMap_mul p f hzero)
  exact Grp.homMk (Over.homMk (dividedMap p f hzero) (dividedMap_over p f hzero) :
    E.group.X ⟶ E'.group.X)

/-- The genuine restriction kernel is precisely divisibility by multiplication
by p, expressed with actual scheme group homomorphisms. -/
theorem torsion_zero_iff_exists_dividedHom :
    (torsionInclusion p E ≫ f.hom.hom.left =
      torsionBase p E ≫ (GroupScheme.zero E'.group).1) ↔
    ∃ u : E.group ⟶ E'.group,
      (GroupScheme.law E.group).schemeNsmul p ≫ u.hom.hom.left = f.hom.hom.left := by
  constructor
  · intro h
    exact ⟨dividedHom p f h, multiplication_dividedMap p f h⟩
  · rintro ⟨u, hu⟩
    rw [← hu, ← Category.assoc]
    change (pullback.fst _ _ ≫ (GroupScheme.law E.group).schemeNsmul p) ≫ _ = _
    rw [pullback.condition, Category.assoc, GroupScheme.zero_natural]
    rfl

end SupersingularCurves.Geometry.EllipticTorsionRealization
