/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentGroupIso
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_coeff_eq_endDegree_mul_coeff_of_forall_eulerChar_tensorPow_eq
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_forall_eulerChar_tensorPow_eq_mul_pow

/-! # Euler characteristics under actual finite flat maps between abelian varieties

The leading-coefficient argument applies across two different abelian varieties.
Its degree is the actual scheme-theoretic finite-flat rank. The pushforward and
projection-formula proof is adapted from the source-pinned endomorphism theorem.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SupersingularCurves.Geometry.AbelianIsogenyEuler
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open GoodReductionJacobian NeronModelInfra AlgebraicGeometry.OModulePresheaf
open P2MW.S_GoodReductionJacobian_RelativeGroupLaw_coeff_eq_endDegree_mul_coeff_of_forall_eulerChar_tensorPow_eq.P2mDegLead

section Projection
variable {K : Type u} [Field K] {X Y : Scheme.{u}}
variable (cx : X ⟶ Spec (CommRingCat.of K)) (cy : Y ⟶ Spec (CommRingCat.of K))
variable (ψ : Y ⟶ X) (hover : ψ ≫ cx = cy) [IsAffineHom ψ] [hcx : IsSeparated cx]
variable (𝒦 : X.OrderedAffineCover) (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)

include hover hL hcx in
/-- Actual finite pushforward and projection formula, on the pulled-back affine cover. -/
theorem cross_eulerChar_twist_eq (m : ℕ) :
    ((pushforwardUnit cx ψ).twist (L.tensorPow m)).eulerChar 𝒦 =
      (ofModules cy (((Scheme.Modules.pullback ψ).obj L).tensorPow m)).eulerChar (𝒦.comap ψ) := by
  have hN : Scheme.Modules.IsInvertible (L.tensorPow m) := isInvertible_tensorPow hL m
  have e1 : ((pushforwardUnit cx ψ).twist (L.tensorPow m)).eulerChar 𝒦 =
      (ofModules (ψ ≫ cx) ((Scheme.Modules.pullback ψ).obj (L.tensorPow m))).eulerChar (𝒦.comap ψ) := by
    obtain ⟨h0, hs⟩ := nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit
      cx ψ 𝒦 (L.tensorPow m) hN.1
    exact (eulerChar_eq_of_equiv
      (ofModules (ψ ≫ cx) ((Scheme.Modules.pullback ψ).obj (L.tensorPow m)))
      ((pushforwardUnit cx ψ).twist (L.tensorPow m)) (𝒦.comap ψ) 𝒦 rfl h0 hs).symm
  have e2 := eulerChar_ofModules_congr hover
    ((Scheme.Modules.pullback ψ).obj (L.tensorPow m)) (𝒦.comap ψ)
  have e3 : (ofModules cy ((Scheme.Modules.pullback ψ).obj (L.tensorPow m))).eulerChar (𝒦.comap ψ) =
      (ofModules cy (((Scheme.Modules.pullback ψ).obj L).tensorPow m)).eulerChar (𝒦.comap ψ) := by
    obtain ⟨e⟩ := Scheme.Modules.nonempty_pullback_tensorPow_iso ψ L m
    obtain ⟨h0, hs, -⟩ := nonempty_cechEquiv_ofModules_of_iso cy e (𝒦.comap ψ)
    exact eulerChar_eq_of_equiv
      (ofModules cy ((Scheme.Modules.pullback ψ).obj (L.tensorPow m)))
      (ofModules cy (((Scheme.Modules.pullback ψ).obj L).tensorPow m))
      (𝒦.comap ψ) (𝒦.comap ψ) rfl h0 hs
  exact e1.trans (e2.trans e3)
end Projection

section Coefficients
variable {K : Type u} [Field K] [IsAlgClosed K] {g : ℕ}
variable (A B : AbelianVariety K g)
variable (ψ : B.group.X.left ⟶ A.group.X.left)
variable (hover : ψ ≫ A.group.X.hom = B.group.X.hom) [IsFinite ψ] [hflat : Flat ψ]
variable (d : ℕ) (hdegree : ∀ y, Scheme.Hom.finrank ψ y = d)
variable (𝒦 : A.group.X.left.OrderedAffineCover)
variable (L : A.group.X.left.Modules) (hL : Scheme.Modules.IsInvertible L)

include hover hdegree hL hflat in
/-- The top Hilbert coefficient is multiplied by the actual degree, also for
maps between different abelian varieties. -/
theorem cross_coeff_eq_degree_mul (P Q : Polynomial ℚ)
    (hP : ∀ m : ℕ, ((ofModules B.group.X.hom
      (((Scheme.Modules.pullback ψ).obj L).tensorPow m)).eulerChar (𝒦.comap ψ) : ℚ) = P.eval (m : ℚ))
    (hQ : ∀ m : ℕ, ((ofModules A.group.X.hom (L.tensorPow m)).eulerChar 𝒦 : ℚ) = Q.eval (m : ℚ)) :
    P.coeff g = (d : ℚ) * Q.coeff g := by
  letI : ConnectedSpace A.group.X.left := connectedSpace A.abelianSchemePropertyBundle
  letI : IsIntegral A.group.X.left :=
    AbelianSchemePropertyBundle.isIntegral_of_field A.abelianSchemePropertyBundle
  let F := pushforwardUnit A.group.X.hom ψ
  have hFc : F.IsCoherent := isCoherent A.group.X.hom ψ
  have hFq : F.IsQuasicoherent := isQuasicoherent A.group.X.hom ψ
  have hFP : ∀ m : ℕ, ((F.twist (L.tensorPow m)).eulerChar 𝒦 : ℚ) = P.eval (m : ℚ) := by
    intro m
    rw [cross_eulerChar_twist_eq A.group.X.hom B.group.X.hom ψ hover 𝒦 L hL m]
    exact hP m
  obtain ⟨U₀, 𝔭, -, h𝔭⟩ := exists_chart_prime 𝒦
  have hlead := coeff_eq_rankAtStalk_mul_coeff_of_forall_eulerChar_twist_tensorPow_eq
    A.group.X.hom 𝒦 L hL.1 g
    (SmoothOfRelativeDimension.topologicalKrullDim_le A.group.X.hom g)
    Q hQ F hFc hFq P hFP U₀ 𝔭 h𝔭
  have hrk : Module.rankAtStalk (R := Γ(A.group.X.left, U₀.1)) (F.obj U₀.1) 𝔭 = d :=
    rankAtStalk_pushforwardUnit_obj A.group.X.hom ψ U₀ d hdegree 𝔭
  simpa only [hrk] using hlead
include hover hdegree hL hflat in
/-- Every tensor-power Euler characteristic is multiplied by the actual finite-flat degree. -/
theorem cross_eulerChar_tensorPow_eq_degree_mul (m : ℕ) :
    (ofModules B.group.X.hom (((Scheme.Modules.pullback ψ).obj L).tensorPow m)).eulerChar
        (𝒦.comap ψ) =
      (d : ℤ) * (ofModules A.group.X.hom (L.tensorPow m)).eulerChar 𝒦 := by
  obtain ⟨χA, hχA⟩ := AbelianSchemePropertyBundle.exists_forall_eulerChar_tensorPow_eq_mul_pow
    K A.group.X.hom (GroupScheme.law A.group) A.groupScheme_law_commutative
    A.abelianSchemePropertyBundle g 𝒦 L hL
  obtain ⟨χB, hχB⟩ := AbelianSchemePropertyBundle.exists_forall_eulerChar_tensorPow_eq_mul_pow
    K B.group.X.hom (GroupScheme.law B.group) B.groupScheme_law_commutative
    B.abelianSchemePropertyBundle g (𝒦.comap ψ) ((Scheme.Modules.pullback ψ).obj L) (hL.pullback ψ)
  let PA : Polynomial ℚ := Polynomial.C (χA : ℚ) * Polynomial.X ^ g
  let PB : Polynomial ℚ := Polynomial.C (χB : ℚ) * Polynomial.X ^ g
  have hPA : ∀ n : ℕ, ((ofModules A.group.X.hom (L.tensorPow n)).eulerChar 𝒦 : ℚ) = PA.eval (n : ℚ) := by
    intro n
    simpa [PA] using congrArg (fun z : ℤ => (z : ℚ)) (hχA n)
  have hPB : ∀ n : ℕ, ((ofModules B.group.X.hom
      (((Scheme.Modules.pullback ψ).obj L).tensorPow n)).eulerChar (𝒦.comap ψ) : ℚ) = PB.eval (n : ℚ) := by
    intro n
    simpa [PB] using congrArg (fun z : ℤ => (z : ℚ)) (hχB n)
  have hc := cross_coeff_eq_degree_mul A B ψ hover d hdegree 𝒦 L hL PB PA hPB hPA
  have hcast : (χB : ℚ) = (d : ℚ) * (χA : ℚ) := by
    simpa [PA, PB] using hc
  have hχ : χB = (d : ℤ) * χA := by exact_mod_cast hcast
  rw [hχB, hχA, hχ, mul_assoc]

/-- Tensor power one has the same actual Euler characteristic as the sheaf. -/
theorem eulerChar_tensorPow_one {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of K))
    (𝒰 : X.OrderedAffineCover) (M : X.Modules) :
    (ofModules c (M.tensorPow 1)).eulerChar 𝒰 = (ofModules c M).eulerChar 𝒰 := by
  let e : M.tensorPow 1 ≅ M := λ_ M
  obtain ⟨h0, hs, -⟩ := nonempty_cechEquiv_ofModules_of_iso c e 𝒰
  exact eulerChar_eq_of_equiv (ofModules c (M.tensorPow 1)) (ofModules c M) 𝒰 𝒰 rfl h0 hs

include hover hdegree hL hflat in
/-- Actual finite-flat degree scales the Euler characteristic of a pulled-back line bundle. -/
theorem cross_eulerChar_pullback_eq_degree_mul :
    (ofModules B.group.X.hom ((Scheme.Modules.pullback ψ).obj L)).eulerChar (𝒦.comap ψ) =
      (d : ℤ) * (ofModules A.group.X.hom L).eulerChar 𝒦 := by
  have h := cross_eulerChar_tensorPow_eq_degree_mul A B ψ hover d hdegree 𝒦 L hL 1
  simpa only [eulerChar_tensorPow_one] using h

end Coefficients

end SupersingularCurves.Geometry.AbelianIsogenyEuler
