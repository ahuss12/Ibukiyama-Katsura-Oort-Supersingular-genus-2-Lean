/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.AbelianTateRiemannPoints
import Theorems.Thm_AlgebraicGeometry_RiemannForm_exists_isRiemannForm
import Theorems.Thm_AlgebraicGeometry_RiemannForm_isRiemannForm_unique
import Theorems.Thm_AlgebraicGeometry_RiemannForm_isRiemannForm_add_of_iso_tensor
import Theorems.Thm_AlgebraicGeometry_RiemannForm_perfect_of_forall_torsion_kernelPts_eq_zero
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_preimage_singleton_eq
import Theorems.Thm_IsAlgClosed_exists_isPrimitiveRoot_pow_and_pow_succ_eq

/-! # Riemann forms on the genuine Tate module of an abelian variety -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SupersingularCurves.Geometry.AbelianTate
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open RelativeGroupLaw
open CategoryTheory.MonoidalCategory

variable {K : Type} [Field K] {g : ℕ}

/-- Integral bilinear forms on the inverse limit of the actual point group. -/
abbrev Pairing (ℓ : ℕ) [Fact ℓ.Prime] (A : AbelianVariety K g) :=
  Integral ℓ A →ₗ[ℤ_[ℓ]] Integral ℓ A →ₗ[ℤ_[ℓ]] ℤ_[ℓ]

/-- The geometric level-pairing condition, expressed on the categorical Tate
module via the proved comparison of the two point presentations. -/
def IsRiemannPairing (A : AbelianVariety K g) (M : A.group.X.left.Modules)
    (ℓ : ℕ) [Fact ℓ.Prime] (ζ : ℕ → K) (e : Pairing ℓ A) : Prop :=
  RiemannForm.IsRiemannForm A.group.X.hom (GroupScheme.law A.group)
    A.groupScheme_law_commutative M ℓ ζ
    (e.compl₁₂ (integralGeometricEquiv ℓ A).symm.toLinearMap
      (integralGeometricEquiv ℓ A).symm.toLinearMap)

/-- Every genuine invertible line bundle supplies its Riemann pairing on the
actual Tate module. The pairing is constructed from the line bundle. -/
theorem exists_isRiemannPairing [IsAlgClosed K] (A : AbelianVariety K g)
    (M : A.group.X.left.Modules) (hM : Scheme.Modules.IsInvertible M)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0)
    (ζ : ℕ → K) (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ n))
    (hζℓ : ∀ n, ζ (n + 1) ^ ℓ = ζ n) :
    ∃ e : Pairing ℓ A, IsRiemannPairing A M ℓ ζ e := by
  obtain ⟨e, he⟩ := RiemannForm.exists_isRiemannForm K A.group.X.hom
    (GroupScheme.law A.group) A.groupScheme_law_commutative A.abelianSchemePropertyBundle
    M hM ℓ hℓ ζ hζ hζℓ
  refine ⟨e.compl₁₂ (integralGeometricEquiv ℓ A).toLinearMap
    (integralGeometricEquiv ℓ A).toLinearMap, ?_⟩
  intro n a b
  simpa only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] using he n a b

/-- The pairing gives the genuine level-pairing values on the underlying
scheme points of every compatible torsion sequence. -/
theorem IsRiemannPairing.level {A : AbelianVariety K g}
    {M : A.group.X.left.Modules} {ℓ : ℕ} [Fact ℓ.Prime] {ζ : ℕ → K}
    {e : Pairing ℓ A} (he : IsRiemannPairing A M ℓ ζ e)
    (n : ℕ) (a b : Integral ℓ A) :
    RiemannForm.IsLevelPairingValue A.group.X.hom (GroupScheme.law A.group) M (ℓ ^ n)
      (AlgPoints.toPoint (pointsGeometricEquiv A (a.1 n)))
      (AlgPoints.toPoint (pointsGeometricEquiv A (b.1 n)))
      (ζ n ^ (e a b).appr n) := by
  have h := he n (integralGeometricEquiv ℓ A a) (integralGeometricEquiv ℓ A b)
  simpa only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, integralGeometricEquiv_apply] using h

/-- Tensor products of genuine line bundles add their actual Tate pairings,
using the same compatible roots of unity. -/
theorem IsRiemannPairing.add_of_iso_tensor [IsAlgClosed K]
    (A : AbelianVariety K g) (M N : A.group.X.left.Modules)
    (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0)
    (ζ : ℕ → K) (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ n))
    (hζℓ : ∀ n, ζ (n + 1) ^ ℓ = ζ n) {e e' : Pairing ℓ A}
    (he : IsRiemannPairing A M ℓ ζ e) (he' : IsRiemannPairing A N ℓ ζ e')
    (P : A.group.X.left.Modules) (hP : Nonempty (P ≅ M ⊗ N)) :
    IsRiemannPairing A P ℓ ζ (e + e') := by
  let α := (integralGeometricEquiv ℓ A).symm.toLinearMap
  have hadd : (e + e').compl₁₂ α α = e.compl₁₂ α α + e'.compl₁₂ α α := by
    ext a b
    rfl
  change RiemannForm.IsRiemannForm A.group.X.hom (GroupScheme.law A.group)
    A.groupScheme_law_commutative P ℓ ζ ((e + e').compl₁₂ α α)
  rw [hadd]
  exact RiemannForm.isRiemannForm_add_of_iso_tensor K A.group.X.hom
    (GroupScheme.law A.group) A.groupScheme_law_commutative A.abelianSchemePropertyBundle
    M hM ℓ hℓ ζ hζ hζℓ _ he N hN _ he' P hP

/-- The geometric definition determines the integral pairing uniquely. -/
theorem IsRiemannPairing.unique [IsAlgClosed K] (A : AbelianVariety K g)
    (M : A.group.X.left.Modules) (hM : Scheme.Modules.IsInvertible M)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0)
    (ζ : ℕ → K) (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ n))
    (hζℓ : ∀ n, ζ (n + 1) ^ ℓ = ζ n) {e e' : Pairing ℓ A}
    (he : IsRiemannPairing A M ℓ ζ e) (he' : IsRiemannPairing A M ℓ ζ e') : e = e' := by
  have h := RiemannForm.isRiemannForm_unique K A.group.X.hom
    (GroupScheme.law A.group) A.groupScheme_law_commutative A.abelianSchemePropertyBundle
    M hM ℓ hℓ ζ hζ hζℓ _ he _ he'
  ext a b
  have hab := congrArg (fun q => q (integralGeometricEquiv ℓ A a)
    (integralGeometricEquiv ℓ A b)) h
  simpa only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply] using hab

/-- Riemann pairings from actual line bundles are alternating. -/
theorem IsRiemannPairing.isAlt [IsAlgClosed K] (A : AbelianVariety K g)
    (M : A.group.X.left.Modules) (hM : Scheme.Modules.IsInvertible M)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0)
    (ζ : ℕ → K) (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ n))
    (hζℓ : ∀ n, ζ (n + 1) ^ ℓ = ζ n) {e : Pairing ℓ A}
    (he : IsRiemannPairing A M ℓ ζ e) : e.IsAlt := by
  have h := (RiemannForm.isRiemannForm_swap_eq_neg_and_self_eq_zero K A.group.X.hom
    (GroupScheme.law A.group) A.groupScheme_law_commutative A.abelianSchemePropertyBundle
    M hM ℓ hℓ ζ hζ hζℓ _ he).2
  intro a
  simpa only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply] using h (integralGeometricEquiv ℓ A a)

/-- A line bundle whose translation kernel has no ℓ-primary points gives a
perfect pairing on the genuine Tate module. -/
theorem IsRiemannPairing.perfect [IsAlgClosed K] (A : AbelianVariety K g)
    (M : A.group.X.left.Modules) (hM : Scheme.Modules.IsInvertible M)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0)
    (ζ : ℕ → K) (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ n))
    (hζℓ : ∀ n, ζ (n + 1) ^ ℓ = ζ n) (e : Pairing ℓ A)
    (he : IsRiemannPairing A M ℓ ζ e)
    (hK : ∀ (n : ℕ) (Q : GeometricPoints A K), ℓ ^ n • Q = 0 →
      Nonempty ((Scheme.Modules.pullback (RiemannForm.translation A.group.X.hom
        (GroupScheme.law A.group) (AlgPoints.toPoint Q))).obj M ≅ M) → Q = 0) :
    e.IsPerfPair := by
  have hdim (s : Spec (CommRingCat.of K)) :
      topologicalKrullDim (A.group.X.hom.base ⁻¹' {s}) = g :=
    SmoothOfRelativeDimension.topologicalKrullDim_preimage_singleton_eq A.group.X.hom g s
      (A.abelianSchemePropertyBundle.connectedFibres s).nonempty
  let e' := e.compl₁₂ (integralGeometricEquiv ℓ A).symm.toLinearMap
    (integralGeometricEquiv ℓ A).symm.toLinearMap
  haveI : e'.IsPerfPair := RiemannForm.perfect_of_forall_torsion_kernelPts_eq_zero K
    A.group.X.hom (GroupScheme.law A.group) A.groupScheme_law_commutative
    A.abelianSchemePropertyBundle M hM g hdim ℓ hℓ ζ hζ hζℓ e' he hK
  exact LinearMap.IsPerfPair.congr (p := e') (integralGeometricEquiv ℓ A)
    (integralGeometricEquiv ℓ A) e rfl

/-- Construction of a perfect geometric pairing from the actual line bundle
and its prime-to-ℓ translation kernel. No pairing is supplied as input. -/
theorem exists_perfect_riemannPairing [IsAlgClosed K] (A : AbelianVariety K g)
    (M : A.group.X.left.Modules) (hM : Scheme.Modules.IsInvertible M)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0)
    (ζ : ℕ → K) (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ n))
    (hζℓ : ∀ n, ζ (n + 1) ^ ℓ = ζ n)
    (hK : ∀ (n : ℕ) (Q : GeometricPoints A K), ℓ ^ n • Q = 0 →
      Nonempty ((Scheme.Modules.pullback (RiemannForm.translation A.group.X.hom
        (GroupScheme.law A.group) (AlgPoints.toPoint Q))).obj M ≅ M) → Q = 0) :
    ∃ e : Pairing ℓ A, IsRiemannPairing A M ℓ ζ e ∧ e.IsPerfPair := by
  obtain ⟨e, he⟩ := exists_isRiemannPairing A M hM ℓ hℓ ζ hζ hζℓ
  exact ⟨e, he, IsRiemannPairing.perfect A M hM ℓ hℓ ζ hζ hζℓ e he hK⟩

/-- The normalization and the alternating Riemann form are both constructed
from the actual invertible line bundle. -/
theorem exists_riemannPairing [IsAlgClosed K] (A : AbelianVariety K g)
    (M : A.group.X.left.Modules) (hM : Scheme.Modules.IsInvertible M)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0) :
    ∃ (ζ : ℕ → K) (e : Pairing ℓ A),
      (∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ n)) ∧ (∀ n, ζ (n + 1) ^ ℓ = ζ n) ∧
        IsRiemannPairing A M ℓ ζ e ∧ e.IsAlt := by
  obtain ⟨ζ, hζ, hζℓ⟩ := IsAlgClosed.exists_isPrimitiveRoot_pow_and_pow_succ_eq K ℓ hℓ
  obtain ⟨e, he⟩ := exists_isRiemannPairing A M hM ℓ hℓ ζ hζ hζℓ
  exact ⟨ζ, e, hζ, hζℓ, he, IsRiemannPairing.isAlt A M hM ℓ hℓ ζ hζ hζℓ he⟩

end SupersingularCurves.Geometry.AbelianTate
