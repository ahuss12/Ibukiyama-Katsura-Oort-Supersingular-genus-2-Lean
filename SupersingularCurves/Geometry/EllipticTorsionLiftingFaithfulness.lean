/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.EllipticTorsionLiftingCotangent

/-! # Faithfulness of the cotangent action for actual height-one finite groups -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

namespace SupersingularCurves.Geometry.HeightOneHopf
open Coalgebra
variable {K : Type u} [Field K]
  {H D : Type v} [CommRing H] [HopfAlgebra K H] [Module.Finite K H]
  [Coalgebra.IsCocomm K H]
  [CommRing D] [HopfAlgebra K D] [Module.Finite K D]

/-- Postcomposition of test-algebra points respects their actual group law. -/
def postcompose {T T' : Type v} [CommRing T] [Algebra K T]
    [CommRing T'] [Algebra K T'] (q : T →ₐ[K] T') :
    WithConv (H →ₐ[K] T) →* WithConv (H →ₐ[K] T') where
  toFun f := .toConv (q.comp f.ofConv)
  map_one' := by apply WithConv.ext; ext a; simp
  map_mul' f g := congrArg WithConv.toConv (AlgHom.comp_convMul_distrib q f g)

/-- Convolution points form a group for every test algebra; no coalgebra
structure on the test algebra is required. -/
private instance pointInv (T : Type v) [CommRing T] [Algebra K T] :
    Inv (WithConv (H →ₐ[K] T)) where
  inv f := .toConv (f.ofConv.comp (HopfAlgebra.antipodeAlgHom K H))

private instance pointGroup (T : Type v) [CommRing T] [Algebra K T] :
    CommGroup (WithConv (H →ₐ[K] T)) where
  inv_mul_cancel f := by
    change WithConv.toConv (f.ofConv.comp (HopfAlgebra.antipodeAlgHom K H)) * f = 1
    have h := congrArg (fun x : WithConv (H →ₐ[K] H) => postcompose f.ofConv x)
      (AlgHom.antipode_id_cancel (R := K) (A := H))
    rw [map_mul, map_one] at h
    simpa only [postcompose, MonoidHom.coe_mk, OneHom.coe_mk,
      WithConv.ofConv_toConv, WithConv.toConv_ofConv, AlgHom.comp_id] using h

/-- The inverse natural transformation is represented by an actual Hopf map. -/
def inverseBialg : H →ₐc[K] H := by
  have hn : ∀ (T T' : Type v) [CommRing T] [Algebra K T]
      [CommRing T'] [Algebra K T'] (q : T →ₐ[K] T')
      (f : WithConv (H →ₐ[K] T)),
      ((WithConv.toConv (q.comp f.ofConv))⁻¹).ofConv = q.comp (f⁻¹).ofConv := by
    intro T T' _ _ _ _ q f
    exact congrArg WithConv.ofConv ((postcompose q).map_inv f).symm
  exact Classical.choose (BialgHom.exists_comp_eq_of_natural_of_map_mul
    (fun T _ _ (f : WithConv (H →ₐ[K] T)) => f⁻¹) hn
    (fun T _ _ f g => mul_inv f g) (fun T _ _ => inv_one))

theorem inverseBialg_toAlgHom :
    (inverseBialg (K := K) (H := H)).toAlgHom = HopfAlgebra.antipodeAlgHom K H := by
  have h := Classical.choose_spec (BialgHom.exists_comp_eq_of_natural_of_map_mul
    (fun T _ _ (f : WithConv (H →ₐ[K] T)) => f⁻¹)
    (fun T T' _ _ _ _ q f =>
      congrArg WithConv.ofConv ((postcompose q).map_inv f).symm)
    (fun T _ _ f g => mul_inv f g) (fun T _ _ => inv_one)) H
      (.toConv (AlgHom.id K H))
  change (AlgHom.id K H).comp (HopfAlgebra.antipodeAlgHom K H) =
    (AlgHom.id K H).comp (inverseBialg (K := K) (H := H)).toAlgHom at h
  simpa only [AlgHom.id_comp] using h.symm

variable (p : ℕ) [Fact p.Prime] [CharP K p]

/-- The coordinate differential is faithful on maps from a height-one
finite group scheme. This applies to the actual elliptic Frobenius kernel. -/
theorem cotangentMap_injective
    (hD : ∀ x : D, counit (R := K) x = 0 → x ^ p = 0) :
    Function.Injective (cotangentMap : (H →ₐc[K] D) → _) := by
  intro φ ψ hφψ
  let I : Ideal D := RingHom.ker (Bialgebra.counitAlgHom K D)
  let q : D →ₐ[K] D ⧸ I ^ 2 := Ideal.Quotient.mkₐ K (I ^ 2)
  have hq : q.comp φ.toAlgHom = q.comp ψ.toAlgHom := by
    ext a
    let a₀ : H := a - algebraMap K H (counit (R := K) a)
    have ha : counit (R := K) a₀ = 0 := by
      change (Bialgebra.counitAlgHom K H)
        (a - algebraMap K H ((Bialgebra.counitAlgHom K H) a)) = 0
      simp
    have hh := LinearMap.congr_fun hφψ
      ((RingHom.ker (Bialgebra.counitAlgHom K H)).toCotangent ⟨a₀, ha⟩)
    change I.toCotangent ⟨φ a₀, _⟩ = I.toCotangent ⟨ψ a₀, _⟩ at hh
    have hm : φ a₀ - ψ a₀ ∈ I ^ 2 := (Ideal.toCotangent_eq I).mp hh
    have heq : φ a₀ - ψ a₀ = φ a - ψ a := by
      simp only [a₀, map_sub, AlgHomClass.commutes]
      abel
    rw [heq] at hm
    exact Ideal.Quotient.eq.mpr hm
  let δ : H →ₐc[K] D :=
    (WithConv.toConv φ * WithConv.toConv (ψ.comp (inverseBialg (K := K)))).ofConv
  have hδ : δ.toAlgHom =
      (WithConv.toConv φ.toAlgHom * (WithConv.toConv ψ.toAlgHom)⁻¹).ofConv := by
    change ((WithConv.toConv φ * WithConv.toConv
      (ψ.comp (inverseBialg (K := K)))).ofConv).toAlgHom = _
    have he := BialgHom.toAlgHom_convMul (WithConv.toConv φ)
      (WithConv.toConv (ψ.comp (inverseBialg (K := K))))
    apply WithConv.toConv_injective
    rw [he]
    congr 2
    change ψ.toAlgHom.comp (inverseBialg (K := K)).toAlgHom =
      ψ.toAlgHom.comp (HopfAlgebra.antipodeAlgHom K H)
    rw [inverseBialg_toAlgHom]
  have hqd : q.comp δ.toAlgHom = (1 : WithConv (H →ₐ[K] D ⧸ I ^ 2)).ofConv := by
    apply WithConv.toConv_injective
    rw [hδ]
    change postcompose q (WithConv.toConv φ.toAlgHom *
      (WithConv.toConv ψ.toAlgHom)⁻¹) = 1
    rw [map_mul, map_inv]
    have hq' : postcompose q (WithConv.toConv φ.toAlgHom) =
        postcompose q (WithConv.toConv ψ.toAlgHom) := congrArg WithConv.toConv hq
    rw [hq', mul_inv_cancel]
  have hzero := eq_counit_of_augmentation_mem_sq p hD δ (by
    intro a ha
    have he := congrArg (fun f : H →ₐ[K] D ⧸ I ^ 2 => f a) hqd
    change q (δ a) = algebraMap K (D ⧸ I ^ 2) (counit (R := K) a) at he
    rw [ha, map_zero] at he
    exact (Ideal.Quotient.eq_zero_iff_mem).mp he)
  have hh : WithConv.toConv φ.toAlgHom * (WithConv.toConv ψ.toAlgHom)⁻¹ = 1 := by
    apply WithConv.ext
    ext a
    change (WithConv.toConv φ.toAlgHom * (WithConv.toConv ψ.toAlgHom)⁻¹).ofConv a = _
    rw [← hδ]
    exact hzero a
  have he := congrArg WithConv.ofConv (mul_inv_eq_one.mp hh)
  ext a
  exact congrArg (fun f : H →ₐ[K] D => f a) he

end SupersingularCurves.Geometry.HeightOneHopf

namespace SupersingularCurves.Geometry.EllipticTorsionRealization.FrobeniusKernelHopf
variable {K : Type u} [Field K] [IsAlgClosed K]
  {p : ℕ} [Fact p.Prime] [CharP K p] {E : AbelianVariety K 1}
  (HF : FrobeniusKernelHopf p E)

/-- Actual endomorphisms of ker(F) are determined by their differential. -/
theorem cotangentMap_injective :
    Function.Injective
      (HeightOneHopf.cotangentMap : (HF.Coord →ₐc[K] HF.Coord) → _) :=
  HeightOneHopf.cotangentMap_injective p HF.pow_eq_zero_of_counit_eq_zero

/-- The scalar by which an actual Frobenius-kernel endomorphism acts on
its one-dimensional cotangent space. -/
def cotangentScalar (φ : HF.Coord →ₐc[K] HF.Coord) : K :=
  (LinearEquiv.smul_id_of_finrank_eq_one HF.cotangent_finrank).symm
    (HeightOneHopf.cotangentMap φ)

theorem cotangentMap_eq_scalar (φ : HF.Coord →ₐc[K] HF.Coord) :
    HeightOneHopf.cotangentMap φ = HF.cotangentScalar φ • LinearMap.id := by
  exact ((LinearEquiv.smul_id_of_finrank_eq_one HF.cotangent_finrank).apply_symm_apply
    (HeightOneHopf.cotangentMap φ)).symm

/-- Genuine morphisms of the actual elliptic Frobenius kernel are faithfully
encoded by scalars, with no alpha-p identification supplied. -/
theorem cotangentScalar_injective : Function.Injective HF.cotangentScalar := by
  intro φ ψ h
  apply HF.cotangentMap_injective
  rw [HF.cotangentMap_eq_scalar, HF.cotangentMap_eq_scalar, h]

end SupersingularCurves.Geometry.EllipticTorsionRealization.FrobeniusKernelHopf
