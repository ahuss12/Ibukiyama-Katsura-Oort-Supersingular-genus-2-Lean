/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusTwistGroup
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_nsmulPt_eq_of_mapPt_relFrobenius_eq

/-!
# Verschiebung over a perfect field

For a smooth commutative group scheme, multiplication by p coequalizes
relative Frobenius. Faithfully flat descent constructs the unique morphism
from the actual Frobenius twist back to the original scheme. Both composition
identities use the actual group laws, including the base-changed law.

The coequalization input is the general `RelVersch.comp_schemeNsmul_eq`
lemma in the pinned upstream source. That lemma has no fake-elliptic,
quaternionic, dimension, or algebraic-closedness hypotheses. Its full proof
and dependency closure are vendored without alteration.

Cartier and the genus-two classification are not assumed or proved here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.PerfectFieldVerschiebung
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open NeronModelInfra GoodReductionJacobian SchemeFrobenius

variable (p : ℕ) [Fact p.Prime]
variable {K : Type u} [Field K] [CharP K p]
variable {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of K))
variable (L : RelativeGroupLaw K c) (hc : L.IsCommutative)

include hc in
/-- Multiplication by p coequalizes actual relative Frobenius over any field
of characteristic p. Perfection and smoothness are not needed for this lemma. -/
theorem multiplication_coequalizes {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ X)
    (h : g₁ ≫ relative p c = g₂ ≫ relative p c) :
    g₁ ≫ L.schemeNsmul p = g₂ ≫ L.schemeNsmul p := by
  have hbase : g₁ ≫ c = g₂ ≫ c := by
    have h' := congrArg (fun a => a ≫ toBase p c) h
    simpa only [Category.assoc, relative_toBase] using h'
  have habs : g₁ ≫ absolute p c = g₂ ≫ absolute p c := by
    have h' := congrArg (fun a => a ≫ projection p c) h
    simpa only [Category.assoc, relative_projection] using h'
  exact P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_nsmulPt_eq_of_mapPt_relFrobenius_eq.RelVersch.comp_schemeNsmul_eq
    K p L hc (globalChar p c) g₁ g₂ hbase habs

variable [PerfectField K] [Smooth c]

local instance finiteRelative : IsFinite (relative p c) :=
  (finite_flat_surjective p c).1

local instance flatRelative : Flat (relative p c) :=
  (finite_flat_surjective p c).2.1

local instance surjectiveRelative : Surjective (relative p c) :=
  (finite_flat_surjective p c).2.2.2

/-- The unique scheme morphism descended from multiplication by p. -/
def verschiebung : Twist p c ⟶ X :=
  EffectiveEpi.desc (relative p c) (L.schemeNsmul p)
    (multiplication_coequalizes p c L hc)

theorem frobenius_verschiebung :
    relative p c ≫ verschiebung p c L hc = L.schemeNsmul p :=
  EffectiveEpi.fac (relative p c) (L.schemeNsmul p)
    (multiplication_coequalizes p c L hc)

/-- The other composition is multiplication by p on the actual twist. -/
theorem verschiebung_frobenius :
    verschiebung p c L hc ≫ relative p c = (twistLaw p c L).schemeNsmul p := by
  rw [← cancel_epi (relative p c), ← Category.assoc, frobenius_verschiebung,
    schemeNsmul_relative]

theorem verschiebung_over : verschiebung p c L hc ≫ c = toBase p c := by
  rw [← cancel_epi (relative p c), ← Category.assoc, frobenius_verschiebung,
    L.schemeNsmul_over, relative_toBase]

theorem verschiebung_unique (v : Twist p c ⟶ X)
    (hv : relative p c ≫ v = L.schemeNsmul p) :
    v = verschiebung p c L hc := by
  rw [← cancel_epi (relative p c), hv, frobenius_verschiebung]

include hc in
theorem existsUnique_verschiebung :
    ∃! v : Twist p c ⟶ X, relative p c ≫ v = L.schemeNsmul p :=
  ⟨verschiebung p c L hc, frobenius_verschiebung p c L hc,
    fun v hv => verschiebung_unique p c L hc v hv⟩

/-- The scheme morphism respects the actual identity section of the twist. -/
theorem verschiebung_zero :
    ((twistLaw p c L).one (𝟙 (Spec (CommRingCat.of K)))).1 ≫
        verschiebung p c L hc = (L.one (𝟙 (Spec (CommRingCat.of K)))).1 := by
  rw [← relative_one]
  change ((L.one (𝟙 _)).1 ≫ relative p c) ≫ verschiebung p c L hc = _
  rw [Category.assoc, frobenius_verschiebung, ← nsmul_point, L.nsmul_unit]

/-- The morphism on every test-scheme point. -/
def verschiebungPoint {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (x : SchemeHomOver t (toBase p c)) : SchemeHomOver t c :=
  ⟨x.1 ≫ verschiebung p c L hc, by rw [Category.assoc, verschiebung_over, x.2]⟩

theorem relative_verschiebungPoint {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t c) :
    verschiebungPoint p c L hc (relativePoint p c x) = L.nsmul t p x := by
  apply Subtype.ext
  change (x.1 ≫ relative p c) ≫ verschiebung p c L hc = _
  rw [Category.assoc, frobenius_verschiebung, nsmul_point]

theorem verschiebung_relativePoint {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t (toBase p c)) :
    relativePoint p c (verschiebungPoint p c L hc x) = (twistLaw p c L).nsmul t p x := by
  apply Subtype.ext
  change (x.1 ≫ verschiebung p c L hc) ≫ relative p c = _
  rw [Category.assoc, verschiebung_frobenius, nsmul_point]

include hc in
theorem nsmul_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
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

/-- V is a group morphism on every test scheme. The proof descends equality
along the actual faithfully flat product F × F. -/
theorem verschiebung_mul {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t (toBase p c)) :
    verschiebungPoint p c L hc ((twistLaw p c L).mul t x y) =
      L.mul t (verschiebungPoint p c L hc x) (verschiebungPoint p c L hc y) := by
  let F := relative p c
  let V := verschiebung p c L hc
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
  have hf : c = F ≫ toBase p c := (relative_toBase p c).symm
  let G : pullback c c ⟶ pullback (toBase p c) (toBase p c) :=
    pullback.map c c (toBase p c) (toBase p c) F F (𝟙 _)
      (by simpa only [Category.comp_id] using hf)
      (by simpa only [Category.comp_id] using hf)
  have hG₁ : G ≫ q₁ = r₁ ≫ F := pullback.lift_fst _ _ _
  have hG₂ : G ≫ q₂ = r₂ ≫ F := pullback.lift_snd _ _ _
  have hGt : G ≫ tU' = tU := by
    change G ≫ q₁ ≫ toBase p c = r₁ ≫ c
    rw [← Category.assoc, hG₁, Category.assoc, ← hf]
  haveI : Flat G := MorphismProperty.pullbackMap (P := @Flat) inferInstance inferInstance hf hf
  haveI : Surjective G := MorphismProperty.pullbackMap (P := @Surjective.{u})
    (inferInstance : Surjective F) (inferInstance : Surjective F) hf hf
  haveI : QuasiCompact G :=
    MorphismProperty.pullbackMap (P := @QuasiCompact) inferInstance inferInstance hf hf
  have hc₁ : GoodReductionJacobian.schemeHomOverComp G hGt u₁' = relativePoint p c u₁ :=
    Subtype.ext hG₁
  have hc₂ : GoodReductionJacobian.schemeHomOverComp G hGt u₂' = relativePoint p c u₂ :=
    Subtype.ext hG₂
  have hv₁ : GoodReductionJacobian.schemeHomOverComp G hGt
      (verschiebungPoint p c L hc u₁') = L.nsmul tU p u₁ := by
    apply Subtype.ext
    rw [nsmul_point]
    change G ≫ q₁ ≫ V = r₁ ≫ L.schemeNsmul p
    rw [← Category.assoc, hG₁, Category.assoc, frobenius_verschiebung]
  have hv₂ : GoodReductionJacobian.schemeHomOverComp G hGt
      (verschiebungPoint p c L hc u₂') = L.nsmul tU p u₂ := by
    apply Subtype.ext
    rw [nsmul_point]
    change G ≫ q₂ ≫ V = r₂ ≫ L.schemeNsmul p
    rw [← Category.assoc, hG₂, Category.assoc, frobenius_verschiebung]
  have key : (L'.mul tU' u₁' u₂').1 ≫ V =
      (L.mul tU' (verschiebungPoint p c L hc u₁')
        (verschiebungPoint p c L hc u₂')).1 := by
    rw [← cancel_epi G]
    have lhs : G ≫ (L'.mul tU' u₁' u₂').1 ≫ V =
        (L.nsmul tU p (L.mul tU u₁ u₂)).1 := by
      rw [← Category.assoc]
      change (GoodReductionJacobian.schemeHomOverComp G hGt (L'.mul tU' u₁' u₂')).1 ≫ V = _
      rw [L'.mul_natural, hc₁, hc₂, ← relative_mul, nsmul_point]
      change ((L.mul tU u₁ u₂).1 ≫ F) ≫ V = _
      rw [Category.assoc, frobenius_verschiebung]
    have rhs : G ≫ (L.mul tU' (verschiebungPoint p c L hc u₁')
        (verschiebungPoint p c L hc u₂')).1 =
        (L.mul tU (L.nsmul tU p u₁) (L.nsmul tU p u₂)).1 := by
      change (GoodReductionJacobian.schemeHomOverComp G hGt (L.mul tU' _ _)).1 = _
      rw [L.mul_natural, hv₁, hv₂]
    rw [lhs, rhs, nsmul_mul c L hc]
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
      (verschiebungPoint p c L hc u₁') = verschiebungPoint p c L hc x := by
    apply Subtype.ext
    change ψ ≫ q₁ ≫ V = x.1 ≫ V
    rw [← Category.assoc, pullback.lift_fst]
  have hVy : GoodReductionJacobian.schemeHomOverComp ψ hψ
      (verschiebungPoint p c L hc u₂') = verschiebungPoint p c L hc y := by
    apply Subtype.ext
    change ψ ≫ q₂ ≫ V = y.1 ≫ V
    rw [← Category.assoc, pullback.lift_snd]
  apply Subtype.ext
  have hkey := congrArg (fun a => ψ ≫ a) key
  rw [← Category.assoc] at hkey
  change (GoodReductionJacobian.schemeHomOverComp ψ hψ (L'.mul tU' u₁' u₂')).1 ≫ V =
    (GoodReductionJacobian.schemeHomOverComp ψ hψ (L.mul tU' _ _)).1 at hkey
  rw [L'.mul_natural, L.mul_natural, hx, hy, hVx, hVy] at hkey
  exact hkey

end SupersingularCurves.Geometry.PerfectFieldVerschiebung
