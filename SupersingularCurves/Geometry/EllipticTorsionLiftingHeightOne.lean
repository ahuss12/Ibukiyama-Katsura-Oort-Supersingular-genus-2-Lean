/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.EllipticFrobeniusKernelHopf

/-!
# Height one on the actual Frobenius-kernel coordinate algebra

The scheme-theoretic vanishing of relative Frobenius is transported through
the actual Hopf presentation. Every element of its augmentation ideal has
pth power zero. No identification with an abstract alpha-p model is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.EllipticTorsionRealization.FrobeniusKernelHopf
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian SchemeFrobenius

variable {K : Type u} [Field K] [IsAlgClosed K]
  {p : ℕ} [Fact p.Prime] [CharP K p] {E : AbelianVariety K 1}
  (HF : FrobeniusKernelHopf p E)

theorem points_one (T : Type u) [CommRing T] [Algebra K T] :
    ((HF.points T 1).val : SchemeHomOver _ E.group.X.hom) =
      (GroupScheme.law E.group).one _ := by
  letI := (GroupScheme.law E.group).pointGroup
    (Spec.map (CommRingCat.ofHom (algebraMap K T)))
  have h := HF.points_mul T 1 1
  rw [one_mul] at h
  change (HF.points T 1).val = (HF.points T 1).val * (HF.points T 1).val at h
  change (HF.points T 1).val = 1
  exact mul_left_cancel (h.symm.trans (mul_one _).symm)

@[reassoc]
theorem counit_spec :
    Spec.map (CommRingCat.ofHom (Bialgebra.counitAlgHom K HF.Coord).toRingHom) ≫
      HF.specIso.hom = (frobeniusKernelZero p E).1 := by
  apply (cancel_mono (frobeniusKernelInclusion p E)).mp
  rw [frobeniusKernelZero_inclusion]
  have h := congrArg Subtype.val (HF.points_one K)
  rw [HF.points_scheme] at h
  have hc : (1 : WithConv (HF.Coord →ₐ[K] K)).ofConv =
      Bialgebra.counitAlgHom K HF.Coord := by ext a; rfl
  rw [hc] at h
  have hid : Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 _ :=
    Spec.map_id _
  rw [hid] at h
  simpa only [Category.assoc, GroupScheme.zero] using h

private instance coord_nontrivial : Nontrivial HF.Coord :=
  (Bialgebra.counitAlgHom K HF.Coord).toRingHom.domain_nontrivial

private instance coord_charP : CharP HF.Coord p :=
  charP_of_injective_algebraMap (algebraMap K HF.Coord).injective p

@[reassoc]
theorem spec_absolute :
    Spec.map (CommRingCat.ofHom (frobenius HF.Coord p)) ≫ HF.specIso.hom =
      HF.specIso.hom ≫ absolute p (frobeniusKernelBase p E) := by
  have h := Scheme.frobenius_comp HF.specIso.hom p 1 (Fact.out : p.Prime)
    (Scheme.natCast_eq_zero_ΓSpec (CharP.cast_eq_zero HF.Coord p))
    (globalChar p (frobeniusKernelBase p E))
  rw [Scheme.frobenius_Spec p 1 (Fact.out : p.Prime) (CharP.cast_eq_zero HF.Coord p),
    SchemeFrobenius.powerRingHom_one p HF.Coord (CharP.cast_eq_zero HF.Coord p)] at h
  exact h

/-- Actual scheme height one gives the explicit coordinate power identity. -/
theorem pow_eq_counit_pow (a : HF.Coord) :
    a ^ p = algebraMap K HF.Coord ((Coalgebra.counit (R := K) a) ^ p) := by
  have hz := congrArg (fun f => f ≫ projection p (frobeniusKernelBase p E))
    (frobeniusKernel_relative_eq_zero p E)
  simp only [Category.assoc, relative_projection] at hz
  have hs := congrArg (fun f => HF.specIso.hom ≫ f) hz
  have hb : HF.specIso.hom ≫ frobeniusKernelBase p E =
      Spec.map (CommRingCat.ofHom (algebraMap K HF.Coord)) := by
    rw [← frobeniusKernelInclusion_over]
    exact HF.specIso_over
  rw [← spec_absolute, ← Category.assoc HF.specIso.hom, hb,
    ← HF.counit_spec, Category.assoc, ← HF.spec_absolute] at hs
  rw [← Category.assoc, ← Category.assoc] at hs
  have he := (cancel_mono HF.specIso.hom).mp hs
  rw [← Spec.map_comp, ← Spec.map_comp] at he
  have hr := Spec.map_injective he
  have ha := congrArg (fun f : CommRingCat.of HF.Coord ⟶ CommRingCat.of HF.Coord => f a) hr
  change a ^ p = algebraMap K HF.Coord
    ((Bialgebra.counitAlgHom K HF.Coord) (a ^ p)) at ha
  rw [map_pow] at ha
  exact ha

/-- Every augmentation element of actual ker(F) has pth power zero. -/
theorem pow_eq_zero_of_counit_eq_zero (a : HF.Coord)
    (ha : Coalgebra.counit (R := K) a = 0) : a ^ p = 0 := by
  rw [HF.pow_eq_counit_pow, ha, zero_pow (Fact.out : p.Prime).ne_zero, map_zero]

end SupersingularCurves.Geometry.EllipticTorsionRealization.FrobeniusKernelHopf
