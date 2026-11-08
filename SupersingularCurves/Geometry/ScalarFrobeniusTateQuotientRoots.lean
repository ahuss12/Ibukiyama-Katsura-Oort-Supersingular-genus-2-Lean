/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.ScalarFrobeniusTateQuotientPairing
import SupersingularCurves.Geometry.AbelianIsogenyRootNumerics
import SupersingularCurves.Geometry.AbelianTateRiemannPullback
import SupersingularCurves.Geometry.ScalarFrobeniusTateRiemannRoot

/-!
# Actual roots and uniform numerical bounds on isotropic lattice quotients

Isotropy makes the pulled-back Riemann form divisible by ell^n. The geometric
root theorem then constructs the root sheaf; exact finite-flat degrees cancel
its numerical scaling. No root, positivity, or bounded H0 is supplied as an
extra assumption. A cube finite by sections is produced, not a closed immersion.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SupersingularCurves.Geometry.ScalarFrobeniusTate
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry GoodReductionJacobian AbelianTate
open AlgebraicGeometry.Polarisation


variable {K : Type} [Field K] [IsAlgClosed K] {g : ℕ}
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0)
  (ζ : ℕ → K) (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ n))
  (hζℓ : ∀ n, ζ (n + 1) ^ ℓ = ζ n) (h2 : (2 : K) ≠ 0)

/-- Divisibility of the actual pulled-back Riemann pairing constructs a genuine
root modulo Pic0 on the domain of the given morphism. -/
theorem exists_root_of_tate_pullback_divisible
    (A B : AbelianVariety K g) (φ : B.group ⟶ A.group)
    (M : A.group.X.left.Modules) (hM : Scheme.Modules.IsInvertible M)
    (e : Pairing ℓ A) (he : IsRiemannPairing A M ℓ ζ e)
    (n : ℕ) (hdiv : ∀ x y : Integral ℓ B,
      (ℓ : ℤ_[ℓ]) ^ n ∣ e (integralMap ℓ φ x) (integralMap ℓ φ y)) :
    ∃ R P : B.group.X.left.Modules,
      Scheme.Modules.IsInvertible R ∧ InPicZero B.group.X.hom (GroupScheme.law B.group) P ∧
      Nonempty ((Scheme.Modules.pullback (underlyingScheme.map φ)).obj M ≅
        R.tensorPow (ℓ ^ n) ⊗ P) := by
  have hdim (s : Spec (CommRingCat.of K)) :
      topologicalKrullDim (B.group.X.hom.base ⁻¹' {s}) = g :=
    SmoothOfRelativeDimension.topologicalKrullDim_preimage_singleton_eq B.group.X.hom g s
      (B.abelianSchemePropertyBundle.connectedFibres s).nonempty
  let ep := e.compl₁₂ (integralMap ℓ φ) (integralMap ℓ φ)
  have hep : IsRiemannPairing B ((Scheme.Modules.pullback (underlyingScheme.map φ)).obj M)
      ℓ ζ ep := he.pullback φ
  have hdiv' : ∀ a b,
      (ℓ : ℤ_[ℓ]) ^ n ∣
        (ep.compl₁₂ (integralGeometricEquiv ℓ B).symm.toLinearMap
          (integralGeometricEquiv ℓ B).symm.toLinearMap) a b := by
    intro a b
    exact hdiv _ _
  obtain ⟨R, P, _, hR, hP, hroot, _, _⟩ :=
    ScalarFrobeniusTateRiemannRoot.exists_iterated_root_with_riemannForm K B.group.X.hom
      (GroupScheme.law B.group) B.groupScheme_law_commutative B.abelianSchemePropertyBundle
      g hdim ℓ hℓ ζ hζ hζℓ h2 n _ (hM.pullback (underlyingScheme.map φ)) _ hep hdiv'
  exact ⟨R, P, hR, hP, hroot⟩

/-- An actual morphism with isotropic lattice image has a genuine polarization
root modulo Pic0. The divisibility hypothesis is derived from its Tate image. -/
theorem exists_root_of_isotropic_tate_image
    (A B : AbelianVariety K g) (φ : B.group ⟶ A.group)
    (M : A.group.X.left.Modules) (hM : Scheme.Modules.IsInvertible M)
    (e : Pairing ℓ A) (he : IsRiemannPairing A M ℓ ζ e)
    (U : Submodule ℤ_[ℓ] (Integral ℓ A))
    (hU : ∀ x ∈ U, ∀ y ∈ U, e x y = 0) (n : ℕ)
    (himage : LinearMap.range (integralMap ℓ φ) ≤
      U ⊔ (IsLocalRing.maximalIdeal ℤ_[ℓ] ^ n) •
        (⊤ : Submodule ℤ_[ℓ] (Integral ℓ A))) :
    ∃ R P : B.group.X.left.Modules,
      Scheme.Modules.IsInvertible R ∧ InPicZero B.group.X.hom (GroupScheme.law B.group) P ∧
      Nonempty ((Scheme.Modules.pullback (underlyingScheme.map φ)).obj M ≅
        R.tensorPow (ℓ ^ n) ⊗ P) := by
  apply exists_root_of_tate_pullback_divisible ℓ hℓ ζ hζ hζℓ h2 A B φ M hM e he n
  intro x y
  exact pairing_dvd_of_mem_isotropic_lattice ℓ e U hU n _ _
    (himage ⟨x, rfl⟩) (himage ⟨y, rfl⟩)

/-- Construct the actual quotient, root, finite-kernel positivity, finite cube,
and its level-independent section counts from a half-rank isotropic summand. -/
theorem exists_quotient_root_with_uniform_numerics
    (A : AbelianVariety K g) (𝒰 : A.group.X.left.OrderedAffineCover)
    (M : A.group.X.left.Modules) (hM : Scheme.Modules.IsInvertible M)
    (hfs : M.FiniteBySections A.group.X.hom)
    (e : Pairing ℓ A) (he : IsRiemannPairing A M ℓ ζ e)
    (U V : Submodule ℤ_[ℓ] (Integral ℓ A)) (hUV : IsCompl U V)
    [Module.Free ℤ_[ℓ] U] [Module.Finite ℤ_[ℓ] U]
    (hUrank : Module.finrank ℤ_[ℓ] U = g)
    (hUiso : ∀ x ∈ U, ∀ y ∈ U, e x y = 0) (n : ℕ) :
    ∃ H : FiniteSubgroup A, ∃ D : Quotient A H,
      ∃ hk : H.inclusion ≫ (GroupScheme.law A.group).schemeNsmul (ℓ ^ n) =
        (H.inclusion ≫ A.group.X.hom) ≫ ((GroupScheme.law A.group).one (𝟙 _)).1,
      ∃ R P : D.variety.group.X.left.Modules,
        Scheme.Modules.IsInvertible R ∧
        InPicZero D.variety.group.X.hom (GroupScheme.law D.variety.group) P ∧
        Nonempty ((Scheme.Modules.pullback
          (underlyingScheme.map (D.multiplicationFactor (ℓ ^ n) hk))).obj M ≅
            R.tensorPow (ℓ ^ n) ⊗ P) ∧
        LinearMap.range (integralMap ℓ (D.multiplicationFactor (ℓ ^ n) hk)) =
          U ⊔ (IsLocalRing.maximalIdeal ℤ_[ℓ] ^ n) •
            (⊤ : Submodule ℤ_[ℓ] (Integral ℓ A)) ∧
        (kernelPts D.variety.group.X.hom (GroupScheme.law D.variety.group) R).Finite ∧
        (∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : K →+* k'),
          0 < Scheme.Modules.geomFibreH0Finrank D.variety.group.X.hom R k' sk) ∧
        (R.tensorPow 3).FiniteBySections D.variety.group.X.hom ∧
        ∀ (r : ℕ), 0 < r → ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : K →+* k'),
          Scheme.Modules.geomFibreH0Finrank D.variety.group.X.hom (R.tensorPow r) k' sk =
            r ^ g * Scheme.Modules.geomFibreH0Finrank A.group.X.hom M k' sk := by
  obtain ⟨H, D, hk, hi, himage, hdegree⟩ :=
    exists_quotient_with_prescribed_lattice_and_degree A ℓ n U V hUV hUrank
  let φ := D.multiplicationFactor (ℓ ^ n) hk
  obtain ⟨R, P, hR, hP, ⟨hr⟩⟩ :=
    exists_root_of_isotropic_tate_image ℓ hℓ ζ hζ hζℓ h2 A D.variety φ
      M hM e he U hUiso n himage.le
  letI : IsFinite (underlyingScheme.map φ) := hi.1
  letI : Flat (underlyingScheme.map (multiplication A (ℓ ^ n))) :=
    (A.multiplication_finite_flat_degree (ℓ ^ n) (pow_ne_zero n (Fact.out : ℓ.Prime).ne_zero)).2.2.2.1
  letI : Flat (underlyingScheme.map φ) := D.desc_flat (multiplication A (ℓ ^ n)) hk
  refine ⟨H, D, hk, R, P, hR, hP, ⟨hr⟩, himage, ?_⟩
  exact AbelianIsogenyRootNumerics.root_uniform_numerics A D.variety (underlyingScheme.map φ)
    φ.hom.hom.w 𝒰 M hM hfs (ℓ ^ n) (pow_pos (Fact.out : ℓ.Prime).pos n)
    hdegree R P hR hP hr

end SupersingularCurves.Geometry.ScalarFrobeniusTate
