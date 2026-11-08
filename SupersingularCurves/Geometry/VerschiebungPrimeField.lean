/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.Frobenius
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_comp_schemeNsmul_eq_of_comp_frobenius_eq_of_isCommutative

/-!
# Verschiebung for a smooth commutative group scheme over the prime field

Over `ZMod p`, absolute Frobenius is a morphism over the base. It is faithfully
flat for a smooth group scheme. The pinned group-scheme proof shows that
multiplication by p coequalizes its fibres; effective descent therefore
constructs a unique actual scheme morphism V with F V = [p]. Naturality of
absolute Frobenius proves V F = [p] as well.

The construction is independent of Cartier. Its scope is the prime field,
not arbitrary perfect fields. No Cartier comparison or genus-two geometric
classification is asserted in this module.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SupersingularCurves.Geometry.PrimeFieldVerschiebung
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open NeronModelInfra GoodReductionJacobian
open SchemeFrobenius

variable (p : ℕ) [Fact p.Prime]
variable {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of (ZMod p)))

theorem baseMap_eq_id : baseMap p (ZMod p) = 𝟙 _ := by
  simp [baseMap, ZMod.frobenius_zmod]

theorem frobenius_over : absolute p c ≫ c = c := by
  rw [absolute_over, baseMap_eq_id, Category.comp_id]

/-- Absolute Frobenius, now over the prime field. -/
def frobeniusOver : SchemeHomOver c c := ⟨absolute p c, frobenius_over p c⟩

theorem frobenius_on_affine (B : Type) [CommRing B] [CharP B p]
    (x : Spec (CommRingCat.of B) ⟶ X) :
    x ≫ absolute p c = Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ x := by
  simpa using relative_on_affine p c B x

theorem frobenius_finite_flat_surjective [Smooth c] :
    IsFinite (absolute p c) ∧ Flat (absolute p c) ∧ Surjective (absolute p c) := by
  obtain ⟨hfin, hflat, _, hsurj⟩ := finite_flat_surjective p c
  letI := hfin
  letI := hflat
  letI := hsurj
  haveI : IsIso (baseMap p (ZMod p)) := by rw [baseMap_eq_id]; infer_instance
  haveI : IsIso (projection p c) := inferInstanceAs (IsIso (pullback.fst c (baseMap p (ZMod p))))
  rw [← relative_projection]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

variable (L : RelativeGroupLaw (ZMod p) c) (hc : L.IsCommutative)
variable [Smooth c]

/-- The scheme map induced on test-scheme points. -/
def mapPoint (g : X ⟶ X) (hg : g ≫ c = c) {T : Scheme.{0}}
    {t : T ⟶ Spec (CommRingCat.of (ZMod p))} (x : SchemeHomOver t c) :
    SchemeHomOver t c :=
  ⟨x.1 ≫ g, by rw [Category.assoc, hg, x.2]⟩

theorem nsmul_point {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (ZMod p)))
    (n : ℕ) (x : SchemeHomOver t c) :
    (L.nsmul t n x).1 = x.1 ≫ L.schemeNsmul n := by
  have h := L.nsmul_natural c t x.1 x.2 n ⟨𝟙 _, Category.id_comp _⟩
  have hi : GoodReductionJacobian.schemeHomOverComp x.1 x.2
      (⟨𝟙 _, Category.id_comp _⟩ : SchemeHomOver c c) = x := by
    apply Subtype.ext
    exact Category.comp_id _
  rw [hi] at h
  exact (congrArg Subtype.val h).symm

include hc in
theorem nsmul_mul {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (ZMod p)))
    (n : ℕ) (x y : SchemeHomOver t c) :
    L.nsmul t n (L.mul t x y) = L.mul t (L.nsmul t n x) (L.nsmul t n y) := by
  letI : CommGroup (SchemeHomOver t c) :=
    { L.pointGroup t with mul_comm := fun a b => hc t a b }
  have hpow : ∀ (m : ℕ) (a : SchemeHomOver t c), L.nsmul t m a = a ^ m := by
    intro m a
    induction m with
    | zero => rfl
    | succ m ih =>
      change L.mul t (L.nsmul t m a) a = a ^ (m + 1)
      rw [ih]
      exact (pow_succ a m).symm
  rw [hpow, hpow, hpow]
  exact mul_pow x y n

theorem frobenius_mul {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (ZMod p)))
    (x y : SchemeHomOver t c) :
    mapPoint p c (absolute p c) (frobenius_over p c) (L.mul t x y) =
      L.mul t (mapPoint p c (absolute p c) (frobenius_over p c) x)
        (mapPoint p c (absolute p c) (frobenius_over p c) y) := by
  have he : ∀ a : SchemeHomOver t c,
      mapPoint p c (absolute p c) (frobenius_over p c) a =
        GoodReductionJacobian.schemeHomOverComp (absolute p t) (frobenius_over p t) a := by
    intro a
    apply Subtype.ext
    exact (Scheme.frobenius_comp a.1 p 1 (Fact.out : p.Prime)
      (globalChar p t) (globalChar p c)).symm
  rw [he, he, he]
  exact L.mul_natural t t (absolute p t) (frobenius_over p t) x y

include hc in
/-- The p-multiplication morphism coequalizes the actual Frobenius fibres. -/
theorem multiplication_coequalizes {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ X)
    (h : g₁ ≫ absolute p c = g₂ ≫ absolute p c) :
    g₁ ≫ L.schemeNsmul p = g₂ ≫ L.schemeNsmul p := by
  apply RelativeGroupLaw.comp_schemeNsmul_eq_of_comp_frobenius_eq_of_isCommutative
    p L hc (frobeniusOver p c) ?_ g₁ g₂ h
  intro B _ _ _ x
  exact frobenius_on_affine p c B x.1

/-- The descended scheme morphism, characterized by F V = [p]. -/
def verschiebung : X ⟶ X := by
  letI := (frobenius_finite_flat_surjective p c).1
  letI := (frobenius_finite_flat_surjective p c).2.1
  letI := (frobenius_finite_flat_surjective p c).2.2
  exact EffectiveEpi.desc (absolute p c) (L.schemeNsmul p)
    (multiplication_coequalizes p c L hc)

theorem frobenius_verschiebung :
    absolute p c ≫ verschiebung p c L hc = L.schemeNsmul p := by
  letI := (frobenius_finite_flat_surjective p c).1
  letI := (frobenius_finite_flat_surjective p c).2.1
  letI := (frobenius_finite_flat_surjective p c).2.2
  exact EffectiveEpi.fac (absolute p c) (L.schemeNsmul p)
    (multiplication_coequalizes p c L hc)

theorem verschiebung_frobenius :
    verschiebung p c L hc ≫ absolute p c = L.schemeNsmul p := by
  letI := (frobenius_finite_flat_surjective p c).1
  letI := (frobenius_finite_flat_surjective p c).2.1
  letI := (frobenius_finite_flat_surjective p c).2.2
  rw [← cancel_epi (absolute p c), ← Category.assoc, frobenius_verschiebung]
  exact (Scheme.frobenius_comp (L.schemeNsmul p) p 1 (Fact.out : p.Prime)
    (globalChar p c) (globalChar p c)).symm

theorem verschiebung_over : verschiebung p c L hc ≫ c = c := by
  letI := (frobenius_finite_flat_surjective p c).1
  letI := (frobenius_finite_flat_surjective p c).2.1
  letI := (frobenius_finite_flat_surjective p c).2.2
  rw [← cancel_epi (absolute p c), ← Category.assoc, frobenius_verschiebung,
    L.schemeNsmul_over, frobenius_over]

/-- The factorization uniquely determines the morphism on the actual scheme. -/
theorem verschiebung_unique (v : X ⟶ X)
    (hv : absolute p c ≫ v = L.schemeNsmul p) :
    v = verschiebung p c L hc := by
  letI := (frobenius_finite_flat_surjective p c).1
  letI := (frobenius_finite_flat_surjective p c).2.1
  letI := (frobenius_finite_flat_surjective p c).2.2
  rw [← cancel_epi (absolute p c), hv, frobenius_verschiebung]

include hc in
theorem existsUnique_verschiebung :
    ∃! v : X ⟶ X, absolute p c ≫ v = L.schemeNsmul p :=
  ⟨verschiebung p c L hc, frobenius_verschiebung p c L hc,
    fun v hv => verschiebung_unique p c L hc v hv⟩

/-- The descended morphism preserves the identity section. -/
theorem verschiebung_zero :
    (L.one (𝟙 (Spec (CommRingCat.of (ZMod p))))).1 ≫ verschiebung p c L hc =
      (L.one (𝟙 (Spec (CommRingCat.of (ZMod p))))).1 := by
  let z := L.one (𝟙 (Spec (CommRingCat.of (ZMod p))))
  have hzF : z.1 ≫ absolute p c = z.1 := by
    rw [frobenius_on_affine]
    change baseMap p (ZMod p) ≫ z.1 = z.1
    rw [baseMap_eq_id, Category.id_comp]
  have hzM : z.1 ≫ L.schemeNsmul p = z.1 := by
    have h := L.nsmul_natural c (𝟙 _) z.1 z.2 p ⟨𝟙 _, Category.id_comp _⟩
    have he : GoodReductionJacobian.schemeHomOverComp z.1 z.2
        (⟨𝟙 _, Category.id_comp _⟩ : SchemeHomOver c c) = z := by
      apply Subtype.ext
      exact Category.comp_id _
    rw [he, L.nsmul_unit] at h
    exact congrArg Subtype.val h
  change z.1 ≫ verschiebung p c L hc = z.1
  calc
    z.1 ≫ verschiebung p c L hc =
        (z.1 ≫ absolute p c) ≫ verschiebung p c L hc :=
      congrArg (fun a => a ≫ verschiebung p c L hc) hzF.symm
    _ = z.1 ≫ L.schemeNsmul p := by rw [Category.assoc, frobenius_verschiebung]
    _ = z.1 := hzM

/-- The descended morphism is a group homomorphism on every test scheme. -/
theorem verschiebung_mul {T : Scheme.{0}}
    (t : T ⟶ Spec (CommRingCat.of (ZMod p))) (x y : SchemeHomOver t c) :
    mapPoint p c (verschiebung p c L hc) (verschiebung_over p c L hc) (L.mul t x y) =
      L.mul t
        (mapPoint p c (verschiebung p c L hc) (verschiebung_over p c L hc) x)
        (mapPoint p c (verschiebung p c L hc) (verschiebung_over p c L hc) y) := by
  letI := (frobenius_finite_flat_surjective p c).1
  letI := (frobenius_finite_flat_surjective p c).2.1
  letI := (frobenius_finite_flat_surjective p c).2.2
  let F := absolute p c
  let V := verschiebung p c L hc
  let q₁ := pullback.fst c c
  let q₂ := pullback.snd c c
  let tU : pullback c c ⟶ Spec (CommRingCat.of (ZMod p)) := q₁ ≫ c
  let u₁ : SchemeHomOver tU c := ⟨q₁, rfl⟩
  let u₂ : SchemeHomOver tU c := ⟨q₂, pullback.condition.symm⟩
  have hf : c = F ≫ c := (frobenius_over p c).symm
  let G : pullback c c ⟶ pullback c c :=
    pullback.map c c c c F F (𝟙 _) (by simpa only [Category.comp_id] using hf)
      (by simpa only [Category.comp_id] using hf)
  have hG₁ : G ≫ q₁ = q₁ ≫ F := pullback.lift_fst _ _ _
  have hG₂ : G ≫ q₂ = q₂ ≫ F := pullback.lift_snd _ _ _
  have hGt : G ≫ tU = tU := by
    change G ≫ q₁ ≫ c = q₁ ≫ c
    rw [← Category.assoc, hG₁, Category.assoc, ← hf]
  haveI : Flat G := MorphismProperty.pullbackMap (P := @Flat) inferInstance inferInstance hf hf
  haveI : Surjective G := MorphismProperty.pullbackMap (P := @Surjective.{0})
    (inferInstance : Surjective F) (inferInstance : Surjective F) hf hf
  haveI : QuasiCompact G := MorphismProperty.pullbackMap (P := @QuasiCompact) inferInstance inferInstance hf hf
  have hc₁ : GoodReductionJacobian.schemeHomOverComp G hGt u₁ =
      mapPoint p c F (frobenius_over p c) u₁ := Subtype.ext hG₁
  have hc₂ : GoodReductionJacobian.schemeHomOverComp G hGt u₂ =
      mapPoint p c F (frobenius_over p c) u₂ := Subtype.ext hG₂
  have hv₁ : GoodReductionJacobian.schemeHomOverComp G hGt
      (mapPoint p c V (verschiebung_over p c L hc) u₁) = L.nsmul tU p u₁ := by
    apply Subtype.ext
    rw [nsmul_point]
    change G ≫ q₁ ≫ V = q₁ ≫ L.schemeNsmul p
    rw [← Category.assoc, hG₁, Category.assoc, frobenius_verschiebung]
  have hv₂ : GoodReductionJacobian.schemeHomOverComp G hGt
      (mapPoint p c V (verschiebung_over p c L hc) u₂) = L.nsmul tU p u₂ := by
    apply Subtype.ext
    rw [nsmul_point]
    change G ≫ q₂ ≫ V = q₂ ≫ L.schemeNsmul p
    rw [← Category.assoc, hG₂, Category.assoc, frobenius_verschiebung]
  have key : (L.mul tU u₁ u₂).1 ≫ V =
      (L.mul tU (mapPoint p c V (verschiebung_over p c L hc) u₁)
        (mapPoint p c V (verschiebung_over p c L hc) u₂)).1 := by
    rw [← cancel_epi G]
    have lhs : G ≫ (L.mul tU u₁ u₂).1 ≫ V =
        (L.nsmul tU p (L.mul tU u₁ u₂)).1 := by
      rw [← Category.assoc]
      change (GoodReductionJacobian.schemeHomOverComp G hGt (L.mul tU u₁ u₂)).1 ≫ V = _
      rw [L.mul_natural, hc₁, hc₂, ← frobenius_mul, nsmul_point]
      change ((L.mul tU u₁ u₂).1 ≫ F) ≫ V = _
      rw [Category.assoc, frobenius_verschiebung]
    have rhs : G ≫ (L.mul tU (mapPoint p c V (verschiebung_over p c L hc) u₁)
        (mapPoint p c V (verschiebung_over p c L hc) u₂)).1 =
        (L.mul tU (L.nsmul tU p u₁) (L.nsmul tU p u₂)).1 := by
      change (GoodReductionJacobian.schemeHomOverComp G hGt (L.mul tU _ _)).1 = _
      rw [L.mul_natural, hv₁, hv₂]
    rw [lhs, rhs, nsmul_mul p c L hc]
  let ψ : T ⟶ pullback c c := pullback.lift x.1 y.1 (x.2.trans y.2.symm)
  have hψ : ψ ≫ tU = t := by
    change ψ ≫ q₁ ≫ c = t
    rw [← Category.assoc, pullback.lift_fst, x.2]
  have hx : GoodReductionJacobian.schemeHomOverComp ψ hψ u₁ = x :=
    Subtype.ext (pullback.lift_fst _ _ _)
  have hy : GoodReductionJacobian.schemeHomOverComp ψ hψ u₂ = y :=
    Subtype.ext (pullback.lift_snd _ _ _)
  have hVx : GoodReductionJacobian.schemeHomOverComp ψ hψ
      (mapPoint p c V (verschiebung_over p c L hc) u₁) =
      mapPoint p c V (verschiebung_over p c L hc) x := by
    apply Subtype.ext
    change ψ ≫ q₁ ≫ V = x.1 ≫ V
    rw [← Category.assoc, pullback.lift_fst]
  have hVy : GoodReductionJacobian.schemeHomOverComp ψ hψ
      (mapPoint p c V (verschiebung_over p c L hc) u₂) =
      mapPoint p c V (verschiebung_over p c L hc) y := by
    apply Subtype.ext
    change ψ ≫ q₂ ≫ V = y.1 ≫ V
    rw [← Category.assoc, pullback.lift_snd]
  apply Subtype.ext
  have hkey := congrArg (fun a => ψ ≫ a) key
  rw [← Category.assoc] at hkey
  change (GoodReductionJacobian.schemeHomOverComp ψ hψ (L.mul tU u₁ u₂)).1 ≫ V =
    (GoodReductionJacobian.schemeHomOverComp ψ hψ (L.mul tU _ _)).1 at hkey
  rw [L.mul_natural, L.mul_natural, hx, hy, hVx, hVy] at hkey
  exact hkey

end SupersingularCurves.Geometry.PrimeFieldVerschiebung
