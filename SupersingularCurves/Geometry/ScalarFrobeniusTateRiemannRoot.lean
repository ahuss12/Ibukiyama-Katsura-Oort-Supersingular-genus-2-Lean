/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusLineBundle
import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Theorems.Thm_AlgebraicGeometry_RiemannForm_exists_iso_tensorPow_tensor_of_forall_dvd_of_two_ne_zero
import Theorems.Thm_AlgebraicGeometry_RiemannForm_isRiemannForm_add_of_iso_tensor
import Theorems.Thm_AlgebraicGeometry_RiemannForm_isRiemannForm_tensorUnit_zero
import Theorems.Thm_AlgebraicGeometry_RiemannForm_existsUnique_isRiemannForm
import Theorems.Thm_AlgebraicGeometry_RiemannForm_isRiemannForm_unique
import Theorems.Thm_AlgebraicGeometry_RiemannForm_eq_zero_iff_forall_nonempty_pullback_translation_iso
import Theorems.Thm_AlgebraicGeometry_Polarisation_InPicZero_tensor

/-!
# Iterated extraction of actual line bundle roots from Tate divisibility

The actual line bundle, its Pic0 error, and its divided Tate pairing are
constructed for arbitrary invertible input bundles. Applying this result to the
Tate quotient family requires its geometric divisibility theorem. Converting
fixed Euler characteristic into a uniform closed projective embedding remains
a separate cohomological step, including for nonprincipal polarizations.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SupersingularCurves.Geometry.ScalarFrobeniusTateRiemannRoot
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open RiemannForm Polarisation

/-- Regrouping genuine tensor powers, with no assertion about their sections. -/
def tensorPowMulIso {X : Scheme.{0}} (M : X.Modules) (a : ℕ) :
    (b : ℕ) → (M.tensorPow a).tensorPow b ≅ M.tensorPow (a * b)
  | 0 => Iso.refl _
  | b + 1 =>
    tensorIso (tensorPowMulIso M a b) (Iso.refl _) ≪≫
      Scheme.Modules.tensorPowAdd M (a * b) a ≪≫
      eqToIso (congrArg M.tensorPow (Nat.mul_succ a b).symm)

/-- Distributing genuine tensor powers over tensor products. -/
def tensorPowTensorIso {X : Scheme.{0}} (M N : X.Modules) :
    (b : ℕ) → (M ⊗ N).tensorPow b ≅ M.tensorPow b ⊗ N.tensorPow b
  | 0 => (λ_ (𝟙_ X.Modules)).symm
  | b + 1 =>
    tensorIso (tensorPowTensorIso M N b) (Iso.refl _) ≪≫
      ⟨tensorμ (M.tensorPow b) (N.tensorPow b) M N,
        tensorδ (M.tensorPow b) (N.tensorPow b) M N,
        tensorμ_tensorδ _ _ _ _, tensorδ_tensorμ _ _ _ _⟩

variable (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}}
  (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
  (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
  (g : ℕ) (hdim : ∀ s : Spec (CommRingCat.of k), topologicalKrullDim (f.base ⁻¹' {s}) = g)
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
  (ζ : ℕ → k) (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ n))
  (hζℓ : ∀ n, ζ (n + 1) ^ ℓ = ζ n)

/-- Geometric translation invariance is the actual Pic0 condition. -/
theorem inPicZero_of_algPoint_invariant (P : A.Modules)
    (hP : Scheme.Modules.IsInvertible P)
    (htrans : ∀ Q : L.AlgPoints hc k,
      Nonempty ((Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))).obj P ≅ P)) :
    InPicZero f L P := by
  refine ⟨hP, fun x => ?_⟩
  exact htrans (RelativeGroupLaw.AlgPoints.ofPoint (ofUnitPt f x))

include hA hdim hℓ hζ hζℓ in
/-- Pic0 gives zero for the actual Riemann form. -/
theorem riemannForm_picZero_eq_zero (P : A.Modules) (hP : InPicZero f L P)
    (e : TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]]
      TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] ℤ_[ℓ])
    (he : IsRiemannForm f L hc P ℓ ζ e) : e = 0 := by
  apply (eq_zero_iff_forall_nonempty_pullback_translation_iso k f L hc hA P hP.1
    g hdim ℓ hℓ ζ hζ hζℓ e he).mpr
  intro Q
  exact hP.2 (toUnitPt f (RelativeGroupLaw.AlgPoints.toPoint Q))

include hA hℓ hζ hζℓ in
/-- Tensor power scaling for actual Tate Riemann forms. -/
theorem isRiemannForm_tensorPow (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    (e : TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]]
      TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] ℤ_[ℓ])
    (he : IsRiemannForm f L hc M ℓ ζ e) (n : ℕ) :
    IsRiemannForm f L hc (M.tensorPow n) ℓ ζ ((n : ℤ_[ℓ]) • e) := by
  induction n with
  | zero =>
    simpa only [Nat.cast_zero, zero_smul, Scheme.Modules.tensorPow_zero] using
      isRiemannForm_tensorUnit_zero k f L hc hA ℓ hℓ ζ hζ hζℓ
  | succ n ih =>
    have h := isRiemannForm_add_of_iso_tensor k f L hc hA (M.tensorPow n)
      (FrobeniusLineBundle.tensorPower_invertible hM n) ℓ hℓ ζ hζ hζℓ _ ih M hM e he
      (M.tensorPow (n + 1)) ⟨Iso.refl _⟩
    simpa only [Nat.cast_add, Nat.cast_one, add_smul, one_smul] using h

include hA hdim hℓ hζ hζℓ in
/-- One genuine root together with its divided Riemann form and its Pic0 error. -/
theorem exists_root_with_riemannForm
    (h2 : (2 : k) ≠ 0) (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    (e : TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]]
      TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] ℤ_[ℓ])
    (he : IsRiemannForm f L hc M ℓ ζ e)
    (hdiv : ∀ a b, (ℓ : ℤ_[ℓ]) ∣ e a b) :
    ∃ (R P : A.Modules)
      (eR : TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]]
        TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] ℤ_[ℓ]),
      Scheme.Modules.IsInvertible R ∧ InPicZero f L P ∧
      Nonempty (M ≅ R.tensorPow ℓ ⊗ P) ∧ IsRiemannForm f L hc R ℓ ζ eR ∧
      e = (ℓ : ℤ_[ℓ]) • eR := by
  obtain ⟨R, P, hR, hP, htrans, hiso⟩ :=
    exists_iso_tensorPow_tensor_of_forall_dvd_of_two_ne_zero k f L hc hA M hM
      g hdim h2 ℓ hℓ ζ hζ hζℓ e he hdiv
  have hP0 := inPicZero_of_algPoint_invariant k f L hc P hP htrans
  obtain ⟨eR, heR, _⟩ := existsUnique_isRiemannForm k f L hc hA R hR ℓ hℓ ζ hζ hζℓ
  obtain ⟨eP, heP, _⟩ := existsUnique_isRiemannForm k f L hc hA P hP ℓ hℓ ζ hζ hζℓ
  have heP0 := riemannForm_picZero_eq_zero k f L hc hA g hdim ℓ hℓ ζ hζ hζℓ P hP0 eP heP
  have hpow := isRiemannForm_tensorPow k f L hc hA ℓ hℓ ζ hζ hζℓ R hR eR heR ℓ
  have hsum := isRiemannForm_add_of_iso_tensor k f L hc hA (R.tensorPow ℓ)
    (FrobeniusLineBundle.tensorPower_invertible hR ℓ) ℓ hℓ ζ hζ hζℓ _ hpow P hP eP heP M hiso
  rw [heP0, add_zero] at hsum
  exact ⟨R, P, eR, hR, hP0, hiso, heR,
    isRiemannForm_unique k f L hc hA M hM ℓ hℓ ζ hζ hζℓ e he _ hsum⟩

/-- Powers of an actual Pic0 line remain in Pic0. -/
theorem inPicZero_tensorPow (P : A.Modules) (hP : InPicZero f L P) (n : ℕ) :
    InPicZero f L (P.tensorPow n) := by
  induction n with
  | zero =>
    exact ⟨Scheme.Modules.isInvertible_unit A, fun x => ⟨Scheme.Modules.pullbackUnitIso _⟩⟩
  | succ n ih => exact InPicZero.tensor k f L ih hP

include hA hdim hℓ hζ hζℓ in
/-- Integral divisibility of the actual Tate Riemann form constructs an actual
ℓ^n-th root line bundle modulo Pic0, together with its exact divided pairing. -/
theorem exists_iterated_root_with_riemannForm
    (h2 : (2 : k) ≠ 0) (n : ℕ) (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    (e : TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]]
      TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] ℤ_[ℓ])
    (he : IsRiemannForm f L hc M ℓ ζ e)
    (hdiv : ∀ a b, (ℓ : ℤ_[ℓ]) ^ n ∣ e a b) :
    ∃ (R P : A.Modules)
      (eR : TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]]
        TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] ℤ_[ℓ]),
      Scheme.Modules.IsInvertible R ∧ InPicZero f L P ∧
      Nonempty (M ≅ R.tensorPow (ℓ ^ n) ⊗ P) ∧ IsRiemannForm f L hc R ℓ ζ eR ∧
      e = ((ℓ : ℤ_[ℓ]) ^ n) • eR := by
  induction n generalizing M e with
  | zero =>
    refine ⟨M, 𝟙_ A.Modules, e, hM, ?_, ?_, he, ?_⟩
    · exact ⟨Scheme.Modules.isInvertible_unit A, fun x => ⟨Scheme.Modules.pullbackUnitIso _⟩⟩
    · exact ⟨(Scheme.Modules.tensorPowOneIso M).symm ≪≫ (ρ_ (M.tensorPow 1)).symm⟩
    · simp only [pow_zero, one_smul]
  | succ n ih =>
    have hdiv₁ (a b : TateModule ℓ (L.AlgPoints hc k)) : (ℓ : ℤ_[ℓ]) ∣ e a b :=
      dvd_trans ⟨(ℓ : ℤ_[ℓ]) ^ n, by rw [pow_succ']⟩ (hdiv a b)
    obtain ⟨R₁, P₁, e₁, hR₁, hP₁, ⟨i₁⟩, he₁, heq₁⟩ :=
      exists_root_with_riemannForm k f L hc hA g hdim ℓ hℓ ζ hζ hζℓ h2 M hM e he hdiv₁
    have hdivR (a b : TateModule ℓ (L.AlgPoints hc k)) : (ℓ : ℤ_[ℓ]) ^ n ∣ e₁ a b := by
      have h := hdiv a b
      rw [heq₁] at h
      change (ℓ : ℤ_[ℓ]) ^ (n + 1) ∣ (ℓ : ℤ_[ℓ]) * e₁ a b at h
      rw [pow_succ'] at h
      exact (mul_dvd_mul_iff_left (show (ℓ : ℤ_[ℓ]) ≠ 0 from
        Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero)).mp h
    obtain ⟨R, P, eR, hR, hP, ⟨iR⟩, heR, heqR⟩ := ih R₁ hR₁ e₁ he₁ hdivR
    refine ⟨R, P.tensorPow ℓ ⊗ P₁, eR, hR,
      InPicZero.tensor k f L (inPicZero_tensorPow k f L P hP ℓ) hP₁, ?_, heR, ?_⟩
    · refine ⟨i₁ ≪≫ tensorIso (Scheme.Modules.tensorPowMapIso iR ℓ) (Iso.refl P₁) ≪≫
        tensorIso (tensorPowTensorIso (R.tensorPow (ℓ ^ n)) P ℓ) (Iso.refl P₁) ≪≫
        tensorIso (tensorIso (tensorPowMulIso R (ℓ ^ n) ℓ) (Iso.refl (P.tensorPow ℓ)))
          (Iso.refl P₁) ≪≫
        (α_ (R.tensorPow (ℓ ^ n * ℓ)) (P.tensorPow ℓ) P₁) ≪≫ ?_⟩
      exact tensorIso (eqToIso (congrArg R.tensorPow (pow_succ ℓ n).symm)) (Iso.refl _)
    · rw [heq₁, heqR, smul_smul, ← pow_succ']

end SupersingularCurves.Geometry.ScalarFrobeniusTateRiemannRoot
