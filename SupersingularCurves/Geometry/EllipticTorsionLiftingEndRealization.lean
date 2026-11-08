/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import Theorems.Thm_WeierstrassCurve_free_and_finrank_rationalEndSubring_eq_four
import Theorems.Thm_WeierstrassProjModel_exists_action_rationalEndSubring_of_isAlgClosed

/-!
# Faithful realization of the supersingular elliptic endomorphism lattice

Rational elliptic endomorphisms act faithfully on the genuine projective scheme,
compatibly with the group law on every test scheme. For a supersingular elliptic
curve over an algebraic closure of a finite field this realizes a free rank-four
integer lattice as actual scheme group morphisms.

The result does not assert that every scheme endomorphism belongs to this lattice,
or that the lattice is saturated under division by the characteristic. Those
are additional comparison statements needed for Oort's torsion restriction count.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SupersingularCurves.Geometry.EllipticTorsionLiftingEndRealization
open CategoryTheory AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open WeierstrassCurve.DrinfeldGlobal

variable {k : Type} [Field k] [IsAlgClosed k] [DecidableEq k]
variable (X : WeierstrassCurve k) [X.IsElliptic]

abbrev Model := projModelCR X.toProjective
abbrev modelBase : Model X ⟶ Spec (CommRingCat.of k) := projModelStrCR X.toProjective
abbrev RationalEnd := ↥(WeierstrassCurve.rationalEndSubring k X)

variable (G : WeierstrassProjModel.RelativeGroupLaw k (modelBase X))
variable (ev : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k k)))
    (modelBase X) ≃ (X.toProjective.baseChange k).toAffine.Point)
variable (hev_add : ∀ P Q : SchemeHomOver
    (Spec.map (CommRingCat.ofHom (algebraMap k k))) (modelBase X),
    ev (G.mul (Spec.map (CommRingCat.ofHom (algebraMap k k))) P Q) = ev P + ev Q)
variable (hev_chart : ∀ (P : SchemeHomOver
    (Spec.map (CommRingCat.ofHom (algebraMap k k))) (modelBase X))
    (χ : ZChartRing X.toProjective →+* k),
    P.1 = Spec.map (CommRingCat.ofHom χ) ≫ zChartι X.toProjective →
    ∃ hxy : (X.toProjective.baseChange k).toAffine.Nonsingular
      (χ (xOverZ X.toProjective)) (χ (yOverZ X.toProjective)),
      ev P = WeierstrassCurve.Affine.Point.some _ _ hxy)

include hev_add hev_chart

/-- A faithful realization, with addition and multiplication by natural numbers
expressed using the genuine scheme group law. -/
theorem exists_faithful_action :
    ∃ Φ : RationalEnd X → SchemeHomOver (modelBase X) (modelBase X),
      Function.Injective Φ ∧
      (∀ α P, ev (NeronModelInfra.schemeHomOverComp P (Φ α)) =
        (α : AddMonoid.End (X.baseChange k).toAffine.Point) (ev P)) ∧
      (∀ α {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k))
        (P Q : SchemeHomOver t (modelBase X)),
        NeronModelInfra.schemeHomOverComp (G.mul t P Q) (Φ α) =
          G.mul t (NeronModelInfra.schemeHomOverComp P (Φ α))
            (NeronModelInfra.schemeHomOverComp Q (Φ α))) ∧
      Φ 0 = G.one (modelBase X) ∧
      Φ 1 = NeronModelInfra.schemeHomOverId (modelBase X) ∧
      (∀ α β, Φ (α + β) = G.mul (modelBase X) (Φ α) (Φ β)) ∧
      (∀ α β, Φ (α * β) = NeronModelInfra.schemeHomOverComp (Φ β) (Φ α)) ∧
      (∀ (n : ℕ) α, Φ (n • α) = G.nsmul (modelBase X) n (Φ α)) := by
  obtain ⟨Φ, heval, hgroup, hone, hcomp, hadd⟩ :=
    WeierstrassProjModel.exists_action_rationalEndSubring_of_isAlgClosed
      X G ev hev_add hev_chart
  have hinj : Function.Injective Φ := by
    intro α β h
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro P
    obtain ⟨Q, rfl⟩ := ev.surjective P
    exact (heval α Q).symm.trans ((congrArg
      (fun q => ev (NeronModelInfra.schemeHomOverComp Q q)) h).trans (heval β Q))
  have hadd' : ∀ α β, Φ (α + β) = G.mul (modelBase X) (Φ α) (Φ β) := by
    intro α β
    simpa only [NeronModelInfra.schemeHomOverComp_id_left] using
      hadd α β (modelBase X) (NeronModelInfra.schemeHomOverId (modelBase X))
  have hzero : Φ 0 = G.one (modelBase X) := by
    letI := G.pointGroup (modelBase X)
    have hh : Φ 0 = Φ 0 * Φ 0 := by
      change Φ 0 = G.mul (modelBase X) (Φ 0) (Φ 0)
      simpa only [add_zero] using hadd' 0 0
    exact (mul_eq_left.mp hh.symm)
  have hnsmul : ∀ (n : ℕ) α, Φ (n • α) = G.nsmul (modelBase X) n (Φ α) := by
    intro n α
    induction n with
    | zero => simpa only [zero_nsmul, WeierstrassProjModel.RelativeGroupLaw.nsmul_zero]
        using hzero
    | succ n ih =>
      rw [succ_nsmul, hadd', ih, WeierstrassProjModel.RelativeGroupLaw.nsmul_succ]
  exact ⟨Φ, hinj, heval, hgroup, hzero, hone, hadd', hcomp, hnsmul⟩

/-- A rank-four integer lattice of genuine endomorphisms of the projective
elliptic scheme. Injectivity is equality of scheme morphisms. -/
theorem exists_rankFour_scheme_lattice
    (p : ℕ) [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    [Algebra.IsAlgebraic (ZMod p) k]
    (hss : ∀ P : X.toAffine.Point, p • P = 0 → P = 0) :
    ∃ Φ : (Fin 4 → ℤ) → SchemeHomOver (modelBase X) (modelBase X),
      Function.Injective Φ ∧
      (∀ a {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k))
        (P Q : SchemeHomOver t (modelBase X)),
        NeronModelInfra.schemeHomOverComp (G.mul t P Q) (Φ a) =
          G.mul t (NeronModelInfra.schemeHomOverComp P (Φ a))
            (NeronModelInfra.schemeHomOverComp Q (Φ a))) ∧
      Φ 0 = G.one (modelBase X) ∧
      (∀ a b, Φ (a + b) = G.mul (modelBase X) (Φ a) (Φ b)) ∧
      (∀ (n : ℕ) a, Φ (n • a) = G.nsmul (modelBase X) n (Φ a)) := by
  obtain ⟨hfree, hfinite, hrank⟩ :=
    WeierstrassCurve.free_and_finrank_rationalEndSubring_eq_four p X hss
  letI := hfree
  letI := hfinite
  let b := Module.finBasisOfFinrankEq ℤ (RationalEnd X) hrank
  let e : (Fin 4 → ℤ) ≃ₗ[ℤ] RationalEnd X := b.equivFun.symm
  obtain ⟨Ψ, hinj, -, hgroup, hzero, -, hadd, -, hnsmul⟩ :=
    exists_faithful_action X G ev hev_add hev_chart
  refine ⟨fun a => Ψ (e a), hinj.comp e.injective, fun a => hgroup (e a), ?_, ?_, ?_⟩
  · simpa only [map_zero] using hzero
  · intro a c
    exact (congrArg Ψ (map_add e a c)).trans (hadd (e a) (e c))
  · intro n a
    exact (congrArg Ψ (map_nsmul e n a)).trans (hnsmul n (e a))

end SupersingularCurves.Geometry.EllipticTorsionLiftingEndRealization
