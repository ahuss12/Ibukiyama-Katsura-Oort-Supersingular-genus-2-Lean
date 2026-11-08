/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.EllipticTorsionLiftingPresentation
import SupersingularCurves.Geometry.EllipticTorsionLiftingVerschiebung

/-!
# Canonical Cartier-dual Verschiebung on the actual torsion scheme

The abstract perfect-field Hopf construction is transported along a proved
Spec isomorphism to the actual torsion kernel. Its Frobenius composition is
identified with multiplication on the original abelian variety.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.TorsionLevels.Presentation
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian SchemeFrobenius

variable {K : Type u} [Field K] {g n : ℕ} {A : AbelianVariety K g}
  (H : Presentation A n)

/-- The presentation sends the identity of every test group to the actual identity. -/
theorem points_one (T : Type u) [CommRing T] [Algebra K T] :
    ((H.points T 1).val : SchemeHomOver _ A.group.X.hom) =
      (GroupScheme.law A.group).one _ := by
  letI := (GroupScheme.law A.group).pointGroup
    (Spec.map (CommRingCat.ofHom (algebraMap K T)))
  have h := H.points_mul T 1 1
  rw [one_mul] at h
  change (H.points T 1).val = (H.points T 1).val * (H.points T 1).val at h
  change (H.points T 1).val = 1
  exact mul_left_cancel (h.symm.trans (mul_one _).symm)

/-- The finite Hopf multiplication is the actual ambient multiplication on every test algebra. -/
theorem points_pow (T : Type u) [CommRing T] [Algebra K T]
    (x : WithConv (H.Coord →ₐ[K] T)) (m : ℕ) :
    ((H.points T (x ^ m)).val : SchemeHomOver _ A.group.X.hom) =
      (GroupScheme.law A.group).nsmul _ m (H.points T x).val := by
  induction m with
  | zero => rw [pow_zero, RelativeGroupLaw.nsmul_zero, points_one]
  | succ m ih => rw [pow_succ, H.points_mul, ih, RelativeGroupLaw.nsmul_succ]

/-- Coordinate [m]* corresponds to multiplication on the original abelian variety. -/
theorem nsmul_spec_inclusion (m : ℕ) :
    Spec.map (CommRingCat.ofHom
      (PDivisibleGroup.Hopf.nsmulAlgHom K H.Coord m).toRingHom) ≫
        H.specIso.hom ≫ inclusion A n =
      H.specIso.hom ≫ inclusion A n ≫ (GroupScheme.law A.group).schemeNsmul m := by
  have h := congrArg Subtype.val (H.points_pow H.Coord (.toConv (AlgHom.id K H.Coord)) m)
  rw [SchemeFrobenius.nsmul_point, H.points_scheme, H.points_scheme] at h
  have hid : Spec.map (CommRingCat.ofHom (AlgHom.id K H.Coord).toRingHom) = 𝟙 _ := by
    change Spec.map (𝟙 (CommRingCat.of H.Coord)) = _
    exact Spec.map_id _
  have hp : ((WithConv.toConv (AlgHom.id K H.Coord)) ^ m).ofConv =
      PDivisibleGroup.Hopf.nsmulAlgHom K H.Coord m := rfl
  rw [hp] at h
  simpa only [WithConv.ofConv_toConv, hid, Category.id_comp, Category.assoc] using h

variable (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectRing K p]

private instance coord_nontrivial : Nontrivial H.Coord :=
  (Bialgebra.counitAlgHom K H.Coord).toRingHom.domain_nontrivial

private instance coord_charP : CharP H.Coord p :=
  charP_of_injective_algebraMap (algebraMap K H.Coord).injective p

/-- Canonical Cartier-dual Verschiebung on the actual n-torsion scheme. -/
def canonical : kernel A n ⟶ kernel A n :=
  H.specIso.inv ≫ Spec.map (CommRingCat.ofHom
    (PerfectHopfVerschiebung.ringHom (K := K) p H.Coord)) ≫ H.specIso.hom

theorem canonical_spec : H.specIso.hom ≫ H.canonical p =
    Spec.map (CommRingCat.ofHom (PerfectHopfVerschiebung.ringHom (K := K) p H.Coord)) ≫
      H.specIso.hom := by
  simp only [canonical, Iso.hom_inv_id_assoc]

@[reassoc]
private theorem spec_absolute :
    Spec.map (CommRingCat.ofHom (frobenius H.Coord p)) ≫ H.specIso.hom =
      H.specIso.hom ≫ absolute p (base A n) := by
  have h := Scheme.frobenius_comp H.specIso.hom p 1 (Fact.out : p.Prime)
    (Scheme.natCast_eq_zero_ΓSpec (CharP.cast_eq_zero H.Coord p)) (globalChar p (base A n))
  rw [Scheme.frobenius_Spec p 1 (Fact.out : p.Prime) (CharP.cast_eq_zero H.Coord p),
    SchemeFrobenius.powerRingHom_one p H.Coord (CharP.cast_eq_zero H.Coord p)] at h
  exact h

/-- The canonical VF identity holds on the actual torsion scheme and recovers
ambient [p] after the actual kernel inclusion. -/
theorem canonical_absolute_inclusion :
    H.canonical p ≫ absolute p (base A n) ≫ inclusion A n =
      inclusion A n ≫ (GroupScheme.law A.group).schemeNsmul p := by
  apply (cancel_epi H.specIso.hom).mp
  rw [← Category.assoc H.specIso.hom, canonical_spec,
    Category.assoc, ← spec_absolute_assoc, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hFV : (PerfectHopfVerschiebung.ringHom (K := K) p H.Coord).comp
      (frobenius H.Coord p) =
        (PDivisibleGroup.Hopf.nsmulAlgHom K H.Coord p).toRingHom := by
    ext a
    exact PerfectHopfVerschiebung.verschiebung_pow_arg (K := K) p H.Coord a
  rw [hFV, nsmul_spec_inclusion]

end SupersingularCurves.Geometry.TorsionLevels.Presentation
