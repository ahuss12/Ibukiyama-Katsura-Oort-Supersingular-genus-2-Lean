/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.EllipticTorsionRealization
import SupersingularCurves.Geometry.EllipticTorsionRealizationDieudonne
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_iso_of_isClosedImmersion_of_isFinite_of_subgroup
import Theorems.Thm_BialgHom_exists_comp_eq_of_natural_of_map_mul

/-!
# The actual Frobenius kernel and its torsion coordinate restriction

The coordinate Hopf algebra below represents the actual Frobenius kernel,
with an actual scheme isomorphism and comparison on every test algebra.
The inclusion in actual elliptic p-torsion induces a Hopf algebra map, hence
an F/V-compatible Dieudonné map. No identification with an abstract alpha-p
model or supersingular Dieudonné normal form is postulated.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.EllipticTorsionRealization
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

variable {K : Type u} [Field K] [IsAlgClosed K]
variable (p : ℕ) [Fact p.Prime] [CharP K p] (E : AbelianVariety K 1)

/-- Points of the actual closed Frobenius kernel, retained as ambient points
with their scheme-theoretic factorization. -/
abbrev FrobeniusKernelPoints (T : Type u) [CommRing T] [Algebra K T] :=
  {P : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K T))) E.group.X.hom //
    ∃ P₀ : Spec (CommRingCat.of T) ⟶ frobeniusKernel p E,
      P₀ ≫ frobeniusKernelInclusion p E = P.1}

/-- A Hopf presentation with an actual scheme isomorphism to ker(F). -/
structure FrobeniusKernelHopf where
  Coord : Type u
  [commRing : CommRing Coord]
  [hopf : HopfAlgebra K Coord]
  [finite : Module.Finite K Coord]
  [cocomm : Coalgebra.IsCocomm K Coord]
  specIso : Spec (CommRingCat.of Coord) ≅ frobeniusKernel p E
  specIso_over : specIso.hom ≫ frobeniusKernelInclusion p E ≫ E.group.X.hom =
    Spec.map (CommRingCat.ofHom (algebraMap K Coord))
  points : ∀ (T : Type u) [CommRing T] [Algebra K T],
    WithConv (Coord →ₐ[K] T) ≃ FrobeniusKernelPoints p E T
  points_scheme : ∀ (T : Type u) [CommRing T] [Algebra K T]
    (φ : WithConv (Coord →ₐ[K] T)),
    ((points T φ).val : SchemeHomOver _ E.group.X.hom).1 =
      Spec.map (CommRingCat.ofHom φ.ofConv.toRingHom) ≫
        specIso.hom ≫ frobeniusKernelInclusion p E
  points_mul : ∀ (T : Type u) [CommRing T] [Algebra K T]
    (φ ψ : WithConv (Coord →ₐ[K] T)),
    ((points T (φ * ψ)).val : SchemeHomOver _ E.group.X.hom) =
      (GroupScheme.law E.group).mul _ (points T φ).val (points T ψ).val
  points_natural : ∀ (T T' : Type u) [CommRing T] [Algebra K T]
    [CommRing T'] [Algebra K T'] (a : T →ₐ[K] T') (φ : WithConv (Coord →ₐ[K] T)),
    ((points T' (.toConv (a.comp φ.ofConv))).val : SchemeHomOver _ E.group.X.hom).1 =
      Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (points T φ).val.1

attribute [instance] FrobeniusKernelHopf.commRing FrobeniusKernelHopf.hopf
  FrobeniusKernelHopf.finite FrobeniusKernelHopf.cocomm

/-- The actual geometric kernel supplies this Hopf presentation. -/
def frobeniusKernelHopf : FrobeniusKernelHopf p E := by
  letI : IsFinite (frobeniusKernelInclusion p E ≫ E.group.X.hom) := by
    rw [frobeniusKernelInclusion_over]
    infer_instance
  let hex := (GroupScheme.law E.group).exists_hopfAlgebra_iso_of_isClosedImmersion_of_isFinite_of_subgroup
    (GroupScheme.law_commutative E.group) (frobeniusKernelInclusion p E)
    (fun t => one_factors p E t)
    (fun t P Q hP hQ => ⟨mul_factors p E t P Q hP hQ, inv_factors p E t P hP⟩)
  choose H hR hH hfin hcomm j e hj hjbase he hbij hmul hnat using hex
  letI := hj
  exact {
    Coord := H
    commRing := hR
    hopf := hH
    finite := hfin
    cocomm := hcomm
    specIso := asIso j
    specIso_over := hjbase
    points := fun T => Equiv.ofBijective (e T) (hbij T)
    points_scheme := he
    points_mul := hmul
    points_natural := hnat }

variable {p E}

/-- Membership in the actual Frobenius kernel gives membership in actual
p-torsion by the proved inclusion of schemes. -/
def FrobeniusKernelPoints.toTorsion {T : Type u} [CommRing T] [Algebra K T]
    (P : FrobeniusKernelPoints p E T) :
    (GroupScheme.law E.group).torsionSubset
      (Spec.map (CommRingCat.ofHom (algebraMap K T))) p := by
  refine ⟨P.val, ?_⟩
  change (GroupScheme.law E.group).nsmul _ p P.val = (GroupScheme.law E.group).one _
  rw [← PerfectFieldVerschiebung.relative_verschiebungPoint p E.group.X.hom
    (GroupScheme.law E.group) (GroupScheme.law_commutative E.group)]
  rw [(factors_iff_points p E _ P.val).mp P.property,
    ← SchemeFrobenius.relative_one p E.group.X.hom (GroupScheme.law E.group),
    PerfectFieldVerschiebung.relative_verschiebungPoint,
    (GroupScheme.law E.group).nsmul_unit]

namespace FrobeniusKernelHopf
variable (HF : FrobeniusKernelHopf p E) (HT : TorsionHopfRealization E p)

/-- The coordinate algebra of the actual Frobenius kernel has dimension p. -/
theorem finrank_eq_prime : Module.finrank K HF.Coord = p := by
  have hover : HF.specIso.hom ≫ frobeniusKernelBase p E =
      Spec.map (CommRingCat.ofHom (algebraMap K HF.Coord)) := by
    rw [← frobeniusKernelInclusion_over]
    exact HF.specIso_over
  have h := congrFun (Scheme.Hom.finrank_comp_left_of_isIso
    HF.specIso.hom (frobeniusKernelBase p E)) (IsLocalRing.closedPoint K)
  rw [hover, Scheme.Hom.finrank_SpecMap_algebraMap,
    Module.rankAtStalk_eq_finrank_of_free, frobeniusKernelBase_finrank] at h
  exact h

/-- On every test algebra, the actual inclusion ker(F)→E[p]. -/
def inclusionPoints (T : Type u) [CommRing T] [Algebra K T]
    (x : WithConv (HF.Coord →ₐ[K] T)) : WithConv (HT.Coord →ₐ[K] T) :=
  (HT.points T).symm (HF.points T x).toTorsion

theorem inclusionPoints_comparison (T : Type u) [CommRing T] [Algebra K T]
    (x : WithConv (HF.Coord →ₐ[K] T)) :
    ((HT.points T (inclusionPoints HF HT T x)).val : SchemeHomOver _ E.group.X.hom) =
      (HF.points T x).val := by
  exact congrArg Subtype.val ((HT.points T).apply_symm_apply _)

omit [IsAlgClosed K] in
private theorem kernel_points_one (T : Type u) [CommRing T] [Algebra K T] :
    ((HF.points T 1).val : SchemeHomOver _ E.group.X.hom) =
      (GroupScheme.law E.group).one _ := by
  let := (GroupScheme.law E.group).pointGroup
    (Spec.map (CommRingCat.ofHom (algebraMap K T)))
  have hm := HF.points_mul T 1 1
  rw [one_mul] at hm
  change (HF.points T 1).val = (HF.points T 1).val * (HF.points T 1).val at hm
  change (HF.points T 1).val = 1
  exact mul_left_cancel (hm.symm.trans (mul_one _).symm)

omit [IsAlgClosed K] [Fact p.Prime] [CharP K p] in
private theorem torsion_points_one (T : Type u) [CommRing T] [Algebra K T] :
    ((HT.points T 1).val : SchemeHomOver _ E.group.X.hom) =
      (GroupScheme.law E.group).one _ := by
  let := (GroupScheme.law E.group).pointGroup
    (Spec.map (CommRingCat.ofHom (algebraMap K T)))
  have hm := HT.points_mul T 1 1
  rw [one_mul] at hm
  change (HT.points T 1).val = (HT.points T 1).val * (HT.points T 1).val at hm
  change (HT.points T 1).val = 1
  exact mul_left_cancel (hm.symm.trans (mul_one _).symm)

theorem inclusionPoints_natural
    (T T' : Type u) [CommRing T] [Algebra K T] [CommRing T'] [Algebra K T']
    (a : T →ₐ[K] T') (x : WithConv (HF.Coord →ₐ[K] T)) :
    (inclusionPoints HF HT T' (.toConv (a.comp x.ofConv))).ofConv =
      a.comp (inclusionPoints HF HT T x).ofConv := by
  have hh : inclusionPoints HF HT T' (.toConv (a.comp x.ofConv)) =
      .toConv (a.comp (inclusionPoints HF HT T x).ofConv) := by
    apply (HT.points T').injective
    apply Subtype.ext
    apply Subtype.ext
    rw [HT.points_natural]
    rw [show ((HT.points T' (inclusionPoints HF HT T'
      (.toConv (a.comp x.ofConv)))).val : SchemeHomOver _ E.group.X.hom) =
        (HF.points T' (.toConv (a.comp x.ofConv))).val from
      inclusionPoints_comparison HF HT T' _]
    rw [HF.points_natural, inclusionPoints_comparison]
  exact congrArg WithConv.ofConv hh

theorem inclusionPoints_mul (T : Type u) [CommRing T] [Algebra K T]
    (x y : WithConv (HF.Coord →ₐ[K] T)) :
    inclusionPoints HF HT T (x * y) =
      inclusionPoints HF HT T x * inclusionPoints HF HT T y := by
  apply (HT.points T).injective
  apply Subtype.ext
  rw [HT.points_mul, inclusionPoints_comparison, inclusionPoints_comparison,
    inclusionPoints_comparison, HF.points_mul]

theorem inclusionPoints_one (T : Type u) [CommRing T] [Algebra K T] :
    inclusionPoints HF HT T 1 = 1 := by
  apply (HT.points T).injective
  apply Subtype.ext
  rw [inclusionPoints_comparison, kernel_points_one, torsion_points_one]

/-- The actual scheme inclusion induces a genuine Hopf algebra map. -/
theorem exists_restriction :
    ∃ r : HT.Coord →ₐc[K] HF.Coord,
      ∀ (T : Type u) [CommRing T] [Algebra K T] (x : WithConv (HF.Coord →ₐ[K] T)),
        (inclusionPoints HF HT T x).ofConv = x.ofConv.comp (r : HT.Coord →ₐ[K] HF.Coord) :=
  BialgHom.exists_comp_eq_of_natural_of_map_mul (inclusionPoints HF HT)
    (inclusionPoints_natural HF HT) (inclusionPoints_mul HF HT) (inclusionPoints_one HF HT)

def restriction : HT.Coord →ₐc[K] HF.Coord := Classical.choose (exists_restriction HF HT)

theorem restriction_points (T : Type u) [CommRing T] [Algebra K T]
    (x : WithConv (HF.Coord →ₐ[K] T)) :
    ((HT.points T (.toConv (x.ofConv.comp
      (restriction HF HT : HT.Coord →ₐ[K] HF.Coord)))).val : SchemeHomOver _ E.group.X.hom) =
        (HF.points T x).val := by
  have he := Classical.choose_spec (exists_restriction HF HT) T x
  rw [restriction, ← he]
  exact inclusionPoints_comparison HF HT T x

/-- The restriction on actual Dieudonné groups is obtained from the actual
coordinate restriction, not from a chosen linear comparison. -/
def dieudonneRestriction :
    Deformation.DieudonneModule K p HT.Coord →+
      Deformation.DieudonneModule K p HF.Coord :=
  Deformation.DieudonneModule.map K p (restriction HF HT)

theorem dieudonneRestriction_frobenius (z : Deformation.DieudonneModule K p HT.Coord) :
    dieudonneRestriction HF HT (Deformation.DieudonneModule.frobenius K p HT.Coord z) =
      Deformation.DieudonneModule.frobenius K p HF.Coord (dieudonneRestriction HF HT z) :=
  Deformation.DieudonneModule.map_frobenius (restriction HF HT) z

theorem dieudonneRestriction_verschiebung (z : Deformation.DieudonneModule K p HT.Coord) :
    dieudonneRestriction HF HT (Deformation.DieudonneModule.verschiebung K p HT.Coord z) =
      Deformation.DieudonneModule.verschiebung K p HF.Coord (dieudonneRestriction HF HT z) :=
  Deformation.DieudonneModule.map_verschiebung (restriction HF HT) z

end FrobeniusKernelHopf
end SupersingularCurves.Geometry.EllipticTorsionRealization
