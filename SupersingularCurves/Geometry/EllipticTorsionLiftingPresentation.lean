/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.EllipticTorsionLiftingAmbient
import SupersingularCurves.Geometry.EllipticFrobeniusKernelHopf

/-!
# Hopf presentations of actual torsion levels

Each actual nonzero torsion level admits a finite Hopf presentation with a
specified isomorphism onto that very kernel scheme. The comparison retains
multiplication on every test algebra and is natural in the test algebra.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.TorsionLevels
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian

variable {K : Type u} [Field K] {g : ℕ} (A : AbelianVariety K g) (n : ℕ)

/-- Factoring through the scheme kernel is exactly the actual torsion condition. -/
theorem factors_iff_torsion {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (P : SchemeHomOver t A.group.X.hom) :
    (∃ P₀ : T ⟶ kernel A n, P₀ ≫ inclusion A n = P.1) ↔
      (GroupScheme.law A.group).nsmul t n P = (GroupScheme.law A.group).one t := by
  have hone : t ≫ (GroupScheme.zero A.group).1 = ((GroupScheme.law A.group).one t).1 := by
    exact congrArg Subtype.val ((GroupScheme.law A.group).one_natural (𝟙 _) t t
      (Category.comp_id _))
  constructor
  · rintro ⟨P₀, hP₀⟩
    have hb : P₀ ≫ base A n = t := by
      rw [← inclusion_over, ← Category.assoc, hP₀, P.2]
    apply Subtype.ext
    rw [SchemeFrobenius.nsmul_point, ← hP₀, Category.assoc]
    change P₀ ≫ (pullback.fst _ _ ≫ (GroupScheme.law A.group).schemeNsmul n) = _
    rw [pullback.condition, ← Category.assoc, hb]
    exact hone
  · intro hP
    refine ⟨pullback.lift P.1 t ?_, pullback.lift_fst _ _ _⟩
    rw [← SchemeFrobenius.nsmul_point, hP]
    exact hone.symm

private theorem torsion_pow {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (P : SchemeHomOver t A.group.X.hom) :
    letI := (GroupScheme.law A.group).pointGroup t
    (GroupScheme.law A.group).nsmul t n P = P ^ n := by
  letI := (GroupScheme.law A.group).pointGroup t
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [RelativeGroupLaw.nsmul_succ, pow_succ, ih]
    rfl

/-- Kernel membership is preserved by multiplication and inverse on every test scheme. -/
theorem subgroup_factors {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t A.group.X.hom)
    (hP : ∃ P₀ : T ⟶ kernel A n, P₀ ≫ inclusion A n = P.1)
    (hQ : ∃ Q₀ : T ⟶ kernel A n, Q₀ ≫ inclusion A n = Q.1) :
    (∃ R₀ : T ⟶ kernel A n, R₀ ≫ inclusion A n = ((GroupScheme.law A.group).mul t P Q).1) ∧
      (∃ S₀ : T ⟶ kernel A n, S₀ ≫ inclusion A n = ((GroupScheme.law A.group).inv t P).1) := by
  rw [factors_iff_torsion] at hP hQ
  constructor
  · apply (factors_iff_torsion A n t _).2
    letI : CommGroup (SchemeHomOver t A.group.X.hom) :=
      { (GroupScheme.law A.group).pointGroup t with
        mul_comm := fun x y => A.groupScheme_law_commutative t x y }
    rw [torsion_pow] at hP hQ ⊢
    change P ^ n = 1 at hP
    change Q ^ n = 1 at hQ
    change (P * Q) ^ n = 1
    rw [mul_pow, hP, hQ, one_mul]
  · apply (factors_iff_torsion A n t _).2
    letI := (GroupScheme.law A.group).pointGroup t
    rw [torsion_pow] at hP ⊢
    change P ^ n = 1 at hP
    change (P⁻¹) ^ n = 1
    rw [inv_pow, hP, inv_one]

/-- A finite Hopf algebra with a genuine isomorphism to the actual n-torsion. -/
structure Presentation where
  Coord : Type u
  [commRing : CommRing Coord]
  [hopf : HopfAlgebra K Coord]
  [finite : Module.Finite K Coord]
  [cocomm : Coalgebra.IsCocomm K Coord]
  specIso : Spec (CommRingCat.of Coord) ≅ kernel A n
  specIso_over : specIso.hom ≫ inclusion A n ≫ A.group.X.hom =
    Spec.map (CommRingCat.ofHom (algebraMap K Coord))
  points : ∀ (T : Type u) [CommRing T] [Algebra K T],
    WithConv (Coord →ₐ[K] T) ≃ (GroupScheme.law A.group).torsionSubset
      (Spec.map (CommRingCat.ofHom (algebraMap K T))) n
  points_scheme : ∀ (T : Type u) [CommRing T] [Algebra K T]
    (φ : WithConv (Coord →ₐ[K] T)),
    ((points T φ).val : SchemeHomOver _ A.group.X.hom).1 =
      Spec.map (CommRingCat.ofHom φ.ofConv.toRingHom) ≫ specIso.hom ≫ inclusion A n
  points_mul : ∀ (T : Type u) [CommRing T] [Algebra K T]
    (φ ψ : WithConv (Coord →ₐ[K] T)),
    ((points T (φ * ψ)).val : SchemeHomOver _ A.group.X.hom) =
      (GroupScheme.law A.group).mul _ (points T φ).val (points T ψ).val
  points_natural : ∀ (T T' : Type u) [CommRing T] [Algebra K T]
    [CommRing T'] [Algebra K T'] (a : T →ₐ[K] T') (φ : WithConv (Coord →ₐ[K] T)),
    ((points T' (.toConv (a.comp φ.ofConv))).val : SchemeHomOver _ A.group.X.hom).1 =
      Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (points T φ).val.1

attribute [instance] Presentation.commRing Presentation.hopf Presentation.finite Presentation.cocomm

/-- Construct the presentation from actual torsion geometry. -/
def presentation [IsAlgClosed K] (hn : n ≠ 0) : Presentation A n := by
  letI : IsFinite (inclusion A n ≫ A.group.X.hom) := by
    rw [inclusion_over]
    exact (A.multiplication_finite_flat_degree n hn).1
  have hone : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)),
      ∃ P₀ : T ⟶ kernel A n, P₀ ≫ inclusion A n = ((GroupScheme.law A.group).one t).1 := by
    intro T t
    apply (factors_iff_torsion A n t _).2
    exact (GroupScheme.law A.group).nsmul_unit t n
  let hex := (GroupScheme.law A.group).exists_hopfAlgebra_iso_of_isClosedImmersion_of_isFinite_of_subgroup
    A.groupScheme_law_commutative (inclusion A n) hone (subgroup_factors A n)
  choose H hR hH hfin hcomm j e hj hjbase he hbij hmul hnat using hex
  letI := hj
  let ec : ∀ (T : Type u) [CommRing T] [Algebra K T],
      {P : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K T))) A.group.X.hom //
        ∃ P₀ : Spec (CommRingCat.of T) ⟶ kernel A n, P₀ ≫ inclusion A n = P.1} ≃
        (GroupScheme.law A.group).torsionSubset
          (Spec.map (CommRingCat.ofHom (algebraMap K T))) n :=
    fun T _ _ => {
      toFun := fun P => ⟨P.val, (factors_iff_torsion A n _ P.val).1 P.property⟩
      invFun := fun P => ⟨P.val, (factors_iff_torsion A n _ P.val).2 P.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact {
    Coord := H
    commRing := hR
    hopf := hH
    finite := hfin
    cocomm := hcomm
    specIso := asIso j
    specIso_over := hjbase
    points := fun T => (Equiv.ofBijective (e T) (hbij T)).trans (ec T)
    points_scheme := he
    points_mul := hmul
    points_natural := hnat }

end SupersingularCurves.Geometry.TorsionLevels
