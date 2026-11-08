/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.EllipticTorsionLiftingResidualKernel
import SupersingularCurves.Geometry.EllipticTorsionLiftingScalarBound

/-! # Actual coordinates of the semilinear residual kernel automorphism -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.EllipticTorsionRealization.FrobeniusKernelHopf
open CategoryTheory AlgebraicGeometry SchemeFrobenius Coalgebra
variable {K : Type u} [Field K] [IsAlgClosed K]
  {p : ℕ} [Fact p.Prime] [CharP K p] {E : AbelianVariety K 1}
  (HF : FrobeniusKernelHopf p E)

def coordinateHom (f : frobeniusKernel p E ⟶ frobeniusKernel p E) : HF.Coord →+* HF.Coord :=
  (Spec.preimage (HF.specIso.hom ≫ f ≫ HF.specIso.inv)).hom

theorem coordinateHom_spec (f : frobeniusKernel p E ⟶ frobeniusKernel p E) :
    Spec.map (CommRingCat.ofHom (HF.coordinateHom f)) =
      HF.specIso.hom ≫ f ≫ HF.specIso.inv := Spec.map_preimage _

theorem coordinateHom_id : HF.coordinateHom (𝟙 _) = RingHom.id HF.Coord := by
  have h : CommRingCat.ofHom (HF.coordinateHom (𝟙 _)) = 𝟙 _ := by
    apply Spec.map_injective
    rw [HF.coordinateHom_spec, Spec.map_id]
    simp
  exact congrArg CommRingCat.Hom.hom h

theorem coordinateHom_comp (f g : frobeniusKernel p E ⟶ frobeniusKernel p E) :
    HF.coordinateHom (f ≫ g) = (HF.coordinateHom f).comp (HF.coordinateHom g) := by
  have h : CommRingCat.ofHom (HF.coordinateHom (f ≫ g)) =
      CommRingCat.ofHom ((HF.coordinateHom f).comp (HF.coordinateHom g)) := by
    apply Spec.map_injective
    rw [CommRingCat.ofHom_comp, Spec.map_comp, HF.coordinateHom_spec,
      HF.coordinateHom_spec, HF.coordinateHom_spec]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg CommRingCat.Hom.hom h

def coordinateEquiv (e : frobeniusKernel p E ≅ frobeniusKernel p E) :
    HF.Coord ≃+* HF.Coord :=
  RingEquiv.ofRingHom (HF.coordinateHom e.hom) (HF.coordinateHom e.inv)
    (by rw [← HF.coordinateHom_comp, e.hom_inv_id, HF.coordinateHom_id])
    (by rw [← HF.coordinateHom_comp, e.inv_hom_id, HF.coordinateHom_id])

theorem specIso_base : HF.specIso.hom ≫ frobeniusKernelBase p E =
    Spec.map (CommRingCat.ofHom (algebraMap K HF.Coord)) := by
  rw [← frobeniusKernelInclusion_over]
  exact HF.specIso_over

theorem coordinateHom_algebraMap
    (f : frobeniusKernel p E ⟶ frobeniusKernel p E) (σ : K →+* K)
    (hf : f ≫ frobeniusKernelBase p E =
      frobeniusKernelBase p E ≫ Spec.map (CommRingCat.ofHom σ)) (c : K) :
    HF.coordinateHom f (algebraMap K HF.Coord c) = algebraMap K HF.Coord (σ c) := by
  have h : CommRingCat.ofHom ((HF.coordinateHom f).comp (algebraMap K HF.Coord)) =
      CommRingCat.ofHom ((algebraMap K HF.Coord).comp σ) := by
    apply Spec.map_injective
    rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp,
      HF.coordinateHom_spec, ← HF.specIso_base]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, hf]
  exact congrArg (fun f : CommRingCat.of K ⟶ CommRingCat.of HF.Coord => f c) h

theorem coordinateHom_counit
    (f : frobeniusKernel p E ⟶ frobeniusKernel p E) (σ : K →+* K)
    (hf : (frobeniusKernelZero p E).1 ≫ f =
      Spec.map (CommRingCat.ofHom σ) ≫ (frobeniusKernelZero p E).1) (a : HF.Coord) :
    counit (R := K) (HF.coordinateHom f a) = σ (counit (R := K) a) := by
  have h : CommRingCat.ofHom
      ((Bialgebra.counitAlgHom K HF.Coord).toRingHom.comp (HF.coordinateHom f)) =
      CommRingCat.ofHom (σ.comp (Bialgebra.counitAlgHom K HF.Coord).toRingHom) := by
    apply Spec.map_injective
    rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp,
      HF.coordinateHom_spec]
    apply (cancel_mono HF.specIso.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [HF.counit_spec, ← Category.assoc, HF.counit_spec, hf]
  exact congrArg (fun f : CommRingCat.of HF.Coord ⟶ CommRingCat.of K => f a) h

def endScheme (φ : HF.Coord →ₐc[K] HF.Coord) :
    frobeniusKernel p E ⟶ frobeniusKernel p E :=
  HF.specIso.inv ≫ Spec.map (CommRingCat.ofHom φ.toAlgHom.toRingHom) ≫ HF.specIso.hom

theorem coordinateHom_endScheme (φ : HF.Coord →ₐc[K] HF.Coord) :
    HF.coordinateHom (HF.endScheme φ) = φ.toAlgHom.toRingHom := by
  have h : CommRingCat.ofHom (HF.coordinateHom (HF.endScheme φ)) =
      CommRingCat.ofHom φ.toAlgHom.toRingHom := by
    apply Spec.map_injective
    rw [HF.coordinateHom_spec]
    simp only [endScheme, Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
      Category.comp_id]
  exact congrArg CommRingCat.Hom.hom h

def inverseSquareFrobenius : K ≃+* K :=
  (frobeniusEquiv K p).symm.trans (frobeniusEquiv K p).symm

theorem inverseSquareFrobenius_spec :
    Spec.map (CommRingCat.ofHom (inverseSquareFrobenius (K := K) (p := p)).toRingHom) =
      inv (baseMap p K) ≫ inv (baseMap p K) := by
  rw [inverse_baseMap, ← Spec.map_comp]
  rfl

variable (hV : GroupScheme.verschiebungCotangent p E.group E.groupScheme_law_commutative = 0)

/-- The actual residual automorphism induces a genuine semilinear
automorphism of the actual Frobenius-kernel coordinate ring. -/
def residualCoordinateEquiv : HF.Coord ≃+* HF.Coord :=
  HF.coordinateEquiv (residualKernelIso p E hV)

theorem residualCoordinateEquiv_algebraMap (c : K) :
    HF.residualCoordinateEquiv hV (algebraMap K HF.Coord c) =
      algebraMap K HF.Coord (inverseSquareFrobenius (K := K) (p := p) c) := by
  change HF.coordinateHom (residualKernelIso p E hV).hom (algebraMap K HF.Coord c) = _
  apply HF.coordinateHom_algebraMap _
    (inverseSquareFrobenius (K := K) (p := p)).toRingHom
  rw [inverseSquareFrobenius_spec]
  exact residualKernelIso_over p E hV

theorem residualCoordinateEquiv_counit (a : HF.Coord) :
    counit (R := K) (HF.residualCoordinateEquiv hV a) =
      inverseSquareFrobenius (K := K) (p := p) (counit (R := K) a) := by
  change counit (R := K) (HF.coordinateHom (residualKernelIso p E hV).hom a) = _
  apply HF.coordinateHom_counit _
    (inverseSquareFrobenius (K := K) (p := p)).toRingHom
  rw [inverseSquareFrobenius_spec]
  exact residualKernelIso_zero p E hV

/-- An actual ker(F) map commuting with the actually constructed residual
automorphism has scalar in F_{p²}. The geometric commutation premise remains
explicit, for use after cancellation of the actual torsion Frobenius map. -/
theorem cotangentScalar_pow_sq_of_residual_commute
    (φ : HF.Coord →ₐc[K] HF.Coord)
    (hcomm : HF.endScheme φ ≫ (residualKernelIso p E hV).hom =
      (residualKernelIso p E hV).hom ≫ HF.endScheme φ) :
    (HF.cotangentScalar φ) ^ (p ^ 2) = HF.cotangentScalar φ := by
  have hr : ∀ a, φ (HF.residualCoordinateEquiv hV a) =
      HF.residualCoordinateEquiv hV (φ a) := by
    have he := congrArg HF.coordinateHom hcomm
    rw [HF.coordinateHom_comp, HF.coordinateHom_comp, HF.coordinateHom_endScheme] at he
    intro a
    exact DFunLike.congr_fun he a
  have h := HF.cotangentScalar_fixed_of_commute
    (inverseSquareFrobenius (K := K) (p := p)) (HF.residualCoordinateEquiv hV)
    (HF.residualCoordinateEquiv_algebraMap hV) (HF.residualCoordinateEquiv_counit hV) φ hr
  have hh := congrArg (fun c : K => (frobeniusEquiv K p) ((frobeniusEquiv K p) c)) h
  change (frobeniusEquiv K p) ((frobeniusEquiv K p)
    ((frobeniusEquiv K p).symm ((frobeniusEquiv K p).symm (HF.cotangentScalar φ)))) =
    (frobeniusEquiv K p) ((frobeniusEquiv K p) (HF.cotangentScalar φ)) at hh
  simp only [RingEquiv.apply_symm_apply] at hh
  change HF.cotangentScalar φ = (HF.cotangentScalar φ ^ p) ^ p at hh
  simpa only [← pow_mul, pow_two] using hh.symm

end SupersingularCurves.Geometry.EllipticTorsionRealization.FrobeniusKernelHopf
