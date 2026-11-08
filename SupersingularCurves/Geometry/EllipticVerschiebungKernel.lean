/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.VerschiebungNaturality
import SupersingularCurves.Geometry.AbelianVerschiebungProducts
import SupersingularCurves.Geometry.Superspecial

/-!
# Rational Frobenius and Verschiebung kernels

Relative Frobenius is bijective on rational points over a perfect field.
The proof uses the actual Frobenius fibre product and the field Frobenius
automorphism, without replacing the twist by the original scheme.

For an actual elliptic abelian variety over an algebraically closed field,
the independently defined triviality of geometric p-torsion is equivalent
to triviality of the rational kernel of the actual Verschiebung morphism.
This point-kernel result does not identify the infinitesimal kernel or assert
the vanishing of the Verschiebung cotangent map.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.SchemeFrobenius
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

variable (p : ℕ) [Fact p.Prime]
variable {K : Type u} [Field K] [CharP K p] [PerfectField K]
variable {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of K))

/-- The actual Frobenius of the base is an isomorphism over a perfect field. -/
theorem baseMap_isIso : IsIso (baseMap p K) := by
  let : IsIso (CommRingCat.ofHom (frobenius K p)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_frobenius K p)
  change IsIso (Spec.map (CommRingCat.ofHom (frobenius K p)))
  infer_instance

/-- Relative Frobenius is injective on actual rational points. -/
theorem relativePoint_injective :
    Function.Injective (relativePoint p c
      (t := 𝟙 (Spec (CommRingCat.of K)))) := by
  let := baseMap_isIso (K := K) p
  intro x y h
  apply Subtype.ext
  apply (cancel_epi (baseMap p K)).mp
  have hx := relative_on_affine p c K x.1
  have hy := relative_on_affine p c K y.1
  have he := congrArg (fun z : SchemeHomOver (𝟙 _) (toBase p c) =>
    z.1 ≫ projection p c) h
  exact hx.symm.trans (he.trans hy)

/-- Every actual rational point of the Frobenius fibre product lifts through
relative Frobenius; no smoothness assumption is required. -/
theorem relativePoint_surjective :
    Function.Surjective (relativePoint p c
      (t := 𝟙 (Spec (CommRingCat.of K)))) := by
  let := baseMap_isIso (K := K) p
  intro x
  let y : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c :=
    ⟨inv (baseMap p K) ≫ x.1 ≫ projection p c, by
      rw [Category.assoc, Category.assoc,
        show projection p c ≫ c = toBase p c ≫ baseMap p K from pullback.condition,
        ← Category.assoc x.1, x.2, Category.id_comp, IsIso.inv_hom_id]⟩
  refine ⟨y, Subtype.ext ?_⟩
  apply pullback.hom_ext
  · change (y.1 ≫ relative p c) ≫ projection p c = x.1 ≫ projection p c
    rw [Category.assoc, relative_on_affine p c K y.1]
    change baseMap p K ≫ (inv (baseMap p K) ≫ x.1 ≫ projection p c) = _
    rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  · change (y.1 ≫ relative p c) ≫ toBase p c = x.1 ≫ toBase p c
    rw [Category.assoc, relative_toBase, y.2, x.2]

/-- The canonical rational-point equivalence induced by actual relative
Frobenius over a perfect field. -/
def relativePointEquiv :
    SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c ≃
      SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (toBase p c) :=
  Equiv.ofBijective (relativePoint p c)
    ⟨relativePoint_injective p c, relativePoint_surjective p c⟩

end SupersingularCurves.Geometry.SchemeFrobenius

namespace SupersingularCurves.Geometry.PerfectFieldVerschiebung
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open SchemeFrobenius

variable (p : ℕ) [Fact p.Prime]
variable {K : Type u} [Field K] [CharP K p] [PerfectField K]
variable {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of K)) [Smooth c]
variable (L : RelativeGroupLaw K c) (hc : L.IsCommutative)

/-- The rational Verschiebung kernel is trivial exactly when the rational
multiplication-by-p kernel is trivial. This uses the actual Frobenius point
bijection, so the statement retains both schemes and both group laws. -/
theorem verschiebungPoint_kernel_trivial_iff :
    (∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (toBase p c),
      verschiebungPoint p c L hc x = L.one (𝟙 _) →
        x = (twistLaw p c L).one (𝟙 _)) ↔
    (∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c,
      L.nsmul (𝟙 _) p x = L.one (𝟙 _) → x = L.one (𝟙 _)) := by
  constructor
  · intro h x hx
    apply relativePoint_injective p c
    rw [relative_one]
    apply h
    rw [relative_verschiebungPoint, hx]
  · intro h x hx
    obtain ⟨y, rfl⟩ := relativePoint_surjective p c x
    rw [relative_verschiebungPoint] at hx
    rw [h y hx, relative_one]

end SupersingularCurves.Geometry.PerfectFieldVerschiebung

namespace SupersingularCurves.Geometry.AbelianVariety
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open SchemeFrobenius PerfectFieldVerschiebung
open scoped CategoryTheory.MonObj

variable (p : ℕ) [Fact p.Prime]
variable {K : Type u} [Field K] [CharP K p] [IsAlgClosed K]

/-- The original point-torsion definition of a supersingular elliptic curve
is equivalent to triviality of the rational kernel of actual Verschiebung. -/
theorem isSupersingularElliptic_iff_verschiebung_kernel_trivial
    (E : AbelianVariety K 1) :
    E.IsSupersingularElliptic p ↔
      ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (toBase p E.group.X.hom),
        verschiebungPoint p E.group.X.hom (GroupScheme.law E.group)
            (GroupScheme.law_commutative E.group) x =
          (GroupScheme.law E.group).one (𝟙 _) →
        x = (twistLaw p E.group.X.hom (GroupScheme.law E.group)).one (𝟙 _) := by
  rw [verschiebungPoint_kernel_trivial_iff]
  constructor
  · intro h x hx
    let P : E.Points := schemeHomOverToOverHom x
    have hP : P ^ p = 1 := by
      apply Over.OverMorphism.ext
      have ht := congrArg Subtype.val (GroupScheme.nsmul_eq_pow E.group (𝟙 _) p P)
      simp only [P, overHomToSchemeHomOver_schemeHomOverToOverHom] at ht
      change ((GroupScheme.law E.group).nsmul (𝟙 _) p x).1 = (P ^ p).left at ht
      rw [← ht, hx]
      rfl
    have hz := congrArg overHomToSchemeHomOver (h P hP)
    apply Subtype.ext
    have hz' := congrArg Subtype.val hz
    exact hz'
  · intro h P hP
    have hx := h (overHomToSchemeHomOver P) (by
      rw [GroupScheme.nsmul_eq_pow, hP]
      rfl)
    apply Over.OverMorphism.ext
    exact congrArg Subtype.val hx

/-- A point in the geometric Verschiebung fibre over the identity is the
actual identity of the Frobenius twist, for a supersingular elliptic curve. -/
theorem IsSupersingularElliptic.verschiebung_kernel_trivial
    {E : AbelianVariety K 1} (hE : E.IsSupersingularElliptic p)
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (toBase p E.group.X.hom))
    (hx : x.1 ≫ verschiebung p E.group.X.hom (GroupScheme.law E.group)
        (GroupScheme.law_commutative E.group) = (GroupScheme.zero E.group).1) :
    x = GroupScheme.twistZero p E.group := by
  apply (isSupersingularElliptic_iff_verschiebung_kernel_trivial p E).mp hE
  exact Subtype.ext hx

end SupersingularCurves.Geometry.AbelianVariety
