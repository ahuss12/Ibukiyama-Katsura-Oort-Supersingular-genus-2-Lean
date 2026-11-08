/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Elliptic.Legendre
import SupersingularCurves.Geometry.Superspecial
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Theorems.Thm_WeierstrassProjModel_exists_relativeGroupLaw_one_eq_zeroSect_isPointsEval_of_isElliptic_of_isDomain
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_goodReductionJacobian_mul_eq_and_nsmul_eq
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_isCommutative_of_isElliptic_of_baseChangeIso_of_isDomain
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_smoothOfRelativeDimension_one
import Theorems.Thm_WeierstrassProjModel_kw_hgi_geometricallyIntegral_of_baseChangeIso
import Theorems.Thm_WeierstrassProjModel_projModel_pullback_iso_baseChange
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_isProper
import Theorems.Thm_WeierstrassProjModel_exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion_of_isDomain

/-!
# Independently supersingular elliptic curves as actual abelian varieties

A root of the Deuring polynomial supplies a nonsingular Legendre equation in
every odd characteristic. The projective Weierstrass model and its actual group
law realize that equation as a dimension-one abelian variety. Its genuine
scheme-valued points are identified with the Weierstrass point group, so the
supersingularity assertion uses the project's geometric torsion definition.
In characteristic two, the equation y² + y = x³ supplies the model and the
negation formula proves directly that its geometric 2-torsion is trivial.

This construction supplies an elliptic curve independently of a given surface;
it does not assert an elliptic map into that surface.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SupersingularCurves.Elliptic

open Polynomial WeierstrassCurve

theorem exists_supersingular_legendre {K : Type*} [Field K] [IsAlgClosed K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2) :
    ∃ t : K, t ≠ 0 ∧ t ≠ 1 ∧ IsSupersingular p (legendreCurve t) := by
  let H : K[X] := hassePolynomial p
  have hdeg : H.natDegree = (p - 1) / 2 :=
    P2MW.S_Polynomial_separable_deuringPolynomial_map.Polynomial.natDegree_deuringPolynomial_map p
  have hp := (Fact.out : p.Prime).two_le
  have hpos : 0 < H.natDegree := by rw [hdeg]; omega
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_root H (by
    intro h
    have hz : H.natDegree = 0 := Polynomial.natDegree_eq_of_degree_eq_some (n := 0) h
    omega)
  have ht0 : t ≠ 0 := by
    intro h
    subst t
    have he : H.eval 0 = 1 :=
      P2MW.S_Polynomial_separable_deuringPolynomial_map.Polynomial.eval_zero_deuringPolynomial_map p
    exact one_ne_zero (he.symm.trans ht)
  have ht1 : t ≠ 1 := by
    intro h
    subst t
    have he : H.eval 1 = (-1 : K) ^ ((p - 1) / 2) :=
      P2MW.S_Polynomial_separable_deuringPolynomial_map.Polynomial.eval_one_deuringPolynomial_map p
    exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero) (he.symm.trans ht)
  exact ⟨t, ht0, ht1, (legendre_isSupersingular_iff p hp2 t ht0 ht1).mpr ht⟩

/-- The nonsingular characteristic-two equation y² + y = x³. -/
def charTwoCurve {K : Type*} [Field K] : WeierstrassCurve K := ⟨0, 0, 1, 0, 0⟩

/-- The characteristic-two model is nonsingular. -/
theorem charTwoCurve_isElliptic {K : Type*} [Field K] [CharP K 2] :
    (charTwoCurve : WeierstrassCurve K).IsElliptic := by
  have h27 : (27 : K) ≠ 0 := (CharP.cast_eq_zero_iff K 2 27).not.mpr (by decide)
  rw [isElliptic_iff]
  norm_num [charTwoCurve, Δ, b₂, b₄, b₆, b₈, h27]

/-- A point of order dividing two would equal its negative, contradicting the
constant term one in the negation formula unless it is the origin. -/
theorem charTwoCurve_torsion {K : Type*} [Field K] [CharP K 2]
    (P : (charTwoCurve : WeierstrassCurve K).toAffine.Point)
    (hP : 2 • P = 0) : P = 0 := by
  have hneg : P = -P := eq_neg_iff_add_eq_zero.mpr (by simpa only [two_nsmul] using hP)
  cases P with
  | zero => rfl
  | some x y h =>
    have hy := (WeierstrassCurve.Affine.Point.some.inj
      (hneg.trans (WeierstrassCurve.Affine.Point.neg_some h))).2
    simp only [WeierstrassCurve.Affine.negY, charTwoCurve, zero_mul, sub_zero] at hy
    have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have hone : (1 : K) = 0 := by linear_combination hy - y * htwo
    exact (one_ne_zero hone).elim

end SupersingularCurves.Elliptic

namespace SupersingularCurves.Geometry

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

variable {K : Type} [Field K]

/-- The actual projective Weierstrass group law, including its point comparison.
The group operations are defined on every test scheme. -/
structure WeierstrassGroupModel (W : WeierstrassCurve K) where
  weierstrassLaw : WeierstrassProjModel.RelativeGroupLaw K (projModelStrCR W.toProjective)
  law : GoodReductionJacobian.RelativeGroupLaw K (projModelStrCR W.toProjective)
  commutative : law.IsCommutative
  law_mul : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of K))
      (x y : SchemeHomOver t (projModelStrCR W.toProjective)),
    law.mul t x y = weierstrassLaw.mul t x y
  eval : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra K F],
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F)))
      (projModelStrCR W.toProjective) ≃ (W.baseChange F).toAffine.Point
  isPointsEval : WeierstrassProjModel.IsPointsEval W.toProjective weierstrassLaw eval
  eval_chart : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra K F]
      (P : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F)))
        (projModelStrCR W.toProjective)) (χ : ZChartRing W.toProjective →+* F),
    P.1 = Spec.map (CommRingCat.ofHom χ) ≫ zChartι W.toProjective →
      ∃ hxy : (W.baseChange F).toAffine.Nonsingular
          (χ (xOverZ W.toProjective)) (χ (yOverZ W.toProjective)),
        eval F P = WeierstrassCurve.Affine.Point.some _ _ hxy

namespace WeierstrassGroupModel

/-- Construct the projective model and its comparison from a nonsingular
Weierstrass equation. No group law or point comparison is assumed. -/
theorem nonempty (W : WeierstrassCurve K) [W.IsElliptic] :
    Nonempty (WeierstrassGroupModel W) := by
  obtain ⟨G, _, hG, _⟩ :=
    WeierstrassProjModel.exists_relativeGroupLaw_one_eq_zeroSect_isPointsEval_of_isElliptic_of_isDomain
      W.toProjective
  obtain ⟨ev, hev, _, hchart⟩ :=
    WeierstrassProjModel.exists_isPointsEval_apply_eq_some_of_eq_comp_zChartInclusion_of_isDomain
      W G (by simpa only [Category.id_comp] using hG (𝟙 _))
  obtain ⟨G', hmul, _, _, _⟩ := G.exists_goodReductionJacobian_mul_eq_and_nsmul_eq
  refine ⟨{
    weierstrassLaw := G
    law := G'
    commutative := ?_
    law_mul := hmul
    eval := ev
    isPointsEval := hev
    eval_chart := hchart
  }⟩
  intro T t x y
  rw [hmul, hmul]
  exact WeierstrassProjModel.RelativeGroupLaw.isCommutative_of_isElliptic_of_baseChangeIso_of_isDomain
    W.toProjective (projModel_pullback_iso_baseChange W.toProjective) G t x y

theorem eval_mul {W : WeierstrassCurve K} (D : WeierstrassGroupModel W)
    (F : Type) [Field F] [DecidableEq F] [Algebra K F]
    (P Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F)))
      (projModelStrCR W.toProjective)) :
    D.eval F (D.law.mul _ P Q) = D.eval F P + D.eval F Q := by
  rw [D.law_mul]
  exact D.isPointsEval.1 F P Q

/-- The scheme, group law, smoothness, properness and connectedness of the
Weierstrass model, bundled as an actual abelian variety. -/
def abelianVariety {W : WeierstrassCurve K} [W.IsElliptic]
    (D : WeierstrassGroupModel W) : AbelianVariety K 1 where
  group := { X := Over.mk (projModelStrCR W.toProjective), grp := D.law.grpObjOverMk }
  comm := (D.law.isCommMonObj_grpObjOverMk_iff_mul_comm).mpr D.commutative
  smooth := projModelStrCR_smoothOfRelativeDimension_one W.toProjective
  proper := projModelStrCR_isProper W.toProjective
  connected := by
    change GeometricallyConnected (projModelStrCR W.toProjective)
    constructor
    intro F _ y Z fst snd h
    have : IsIntegral Z :=
      (kw_hgi_geometricallyIntegral_of_baseChangeIso W
        (projModel_pullback_iso_baseChange W.toProjective)).geometrically_isIntegral y fst snd h
    infer_instance

/-- The points of the constructed group scheme have the usual elliptic-curve
group law, with multiplicative notation for the scheme group. -/
def pointsMulEquiv {W : WeierstrassCurve K} [W.IsElliptic]
    (D : WeierstrassGroupModel W) :
    D.abelianVariety.Points ≃* Multiplicative (W.baseChange K).toAffine.Point := by
  classical
  have hex : ∃ ev : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
      (projModelStrCR W.toProjective) ≃ (W.baseChange K).toAffine.Point,
      ∀ (x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
        (projModelStrCR W.toProjective)),
        ev (D.law.mul _ x y) = ev x + ev y := by
    have he : ∃ ev : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K K)))
        (projModelStrCR W.toProjective) ≃ (W.baseChange K).toAffine.Point,
        ∀ (x y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K K)))
          (projModelStrCR W.toProjective)),
          ev (D.law.mul _ x y) = ev x + ev y := ⟨D.eval K, D.eval_mul K⟩
    have hid : Spec.map (CommRingCat.ofHom (algebraMap K K)) =
        𝟙 (Spec (CommRingCat.of K)) := Spec.map_id _
    rw [hid] at he
    exact he
  let ev := Classical.choose hex
  have hmul := Classical.choose_spec hex
  refine { toEquiv := (schemeHomOverEquivOverHom _ _).symm.trans ev, map_mul' := ?_ }
  intro P Q
  change ev (overHomToSchemeHomOver (P * Q)) =
    ev (overHomToSchemeHomOver P) + ev (overHomToSchemeHomOver Q)
  rw [D.law.overHomToSchemeHomOver_mul]
  exact hmul _ _

/-- Trivial torsion in the usual point group implies trivial torsion in the
actual dimension-one group scheme, using the proved group equivalence. -/
theorem isSupersingularElliptic_of_points [IsAlgClosed K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    {W : WeierstrassCurve K} [W.IsElliptic] (D : WeierstrassGroupModel W)
    (ht : ∀ P : (W.baseChange K).toAffine.Point, p • P = 0 → P = 0) :
    D.abelianVariety.IsSupersingularElliptic p := by
  intro P hP
  apply D.pointsMulEquiv.injective
  have he : (D.pointsMulEquiv P) ^ p = 1 := by rw [← map_pow, hP, map_one]
  have hz := ht (Multiplicative.toAdd (D.pointsMulEquiv P))
    (by simpa using congrArg Multiplicative.toAdd he)
  simpa using hz

/-- The coefficient criterion implies trivial p-torsion for the points of the
actual group scheme; the target predicate is independent of that coefficient. -/
theorem isSupersingularElliptic_of_hasseInvariant_eq_zero
    [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    {W : WeierstrassCurve K} [W.IsElliptic] (D : WeierstrassGroupModel W)
    (hW : W.hasseInvariant p = 0) : D.abelianVariety.IsSupersingularElliptic p := by
  classical
  let : (W.baseChange K).IsElliptic := WeierstrassCurve.instIsEllipticBaseChange W
  have hbase : (W.baseChange K).hasseInvariant p = 0 := by
    rw [Elliptic.hasseInvariant_baseChange, hW, map_zero]
  exact D.isSupersingularElliptic_of_points p
    ((WeierstrassCurve.forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero
      p hp2 (W.baseChange K)).mpr hbase)

end WeierstrassGroupModel

namespace AbelianVariety

/-- An independently supersingular elliptic abelian variety exists over every
algebraically closed field of odd characteristic. -/
theorem exists_isSupersingularElliptic_of_ne_two [IsAlgClosed K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2) :
    ∃ E : AbelianVariety K 1, E.IsSupersingularElliptic p := by
  obtain ⟨t, ht0, ht1, ht⟩ := Elliptic.exists_supersingular_legendre (K := K) p hp2
  letI := Elliptic.legendre_isElliptic p hp2 t ht0 ht1
  obtain ⟨D⟩ := WeierstrassGroupModel.nonempty (WeierstrassCurve.legendreCurve t)
  exact ⟨D.abelianVariety, D.isSupersingularElliptic_of_hasseInvariant_eq_zero p hp2
    ((Elliptic.isSupersingular_iff_hasseInvariant_eq_zero p hp2 _).mp ht)⟩

/-- An actual supersingular elliptic abelian variety exists over every
algebraically closed field of positive prime characteristic, including two. -/
theorem exists_isSupersingularElliptic [IsAlgClosed K]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    ∃ E : AbelianVariety K 1, E.IsSupersingularElliptic p := by
  by_cases hp2 : p = 2
  · subst p
    let W : WeierstrassCurve K := Elliptic.charTwoCurve
    letI : W.IsElliptic := Elliptic.charTwoCurve_isElliptic
    obtain ⟨D⟩ := WeierstrassGroupModel.nonempty W
    refine ⟨D.abelianVariety, D.isSupersingularElliptic_of_points 2 ?_⟩
    have hW : W.baseChange K = (Elliptic.charTwoCurve : WeierstrassCurve K) := by
      ext <;> simp [W, Elliptic.charTwoCurve]
    rw [hW]
    exact Elliptic.charTwoCurve_torsion
  · exact exists_isSupersingularElliptic_of_ne_two p hp2

end AbelianVariety

end SupersingularCurves.Geometry
