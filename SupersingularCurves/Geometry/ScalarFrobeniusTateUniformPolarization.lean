/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.AbelianTateProductPolarization
import SupersingularCurves.Geometry.ScalarFrobeniusTateQuotientRoots
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isInvertible_finiteBySections
import Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_nonempty_of_compactSpace

/-!
# Uniform symmetric polarizations on the actual graph quotients

The quotient sequence, its Riemann-divisible pullbacks, and its exact degrees
construct symmetric line bundles finite by sections with one uniform H0 rank.
This is a numerical bound on actual line bundles on the actual quotient
varieties. Closed immersions and finitely many models are separate conclusions.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SupersingularCurves.Geometry.ScalarFrobeniusTate
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry GoodReductionJacobian
open AbelianTate AlgebraicGeometry.Polarisation

variable {K : Type} [Field K] [IsAlgClosed K] {g : ℕ}

/-- The exact quotient degrees cancel the root scaling on the given sequence,
so every quotient has a symmetric finite bundle of the same section rank. -/
theorem PrescribedLatticeQuotients.exists_symmetric_bundles_with_uniform_rank
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0) (h2 : (2 : K) ≠ 0)
    (A : AbelianVariety K g) (𝒰 : A.group.X.left.OrderedAffineCover)
    (U : Submodule ℤ_[ℓ] (Integral ℓ A)) (F : PrescribedLatticeQuotients ℓ A U)
    (M : A.group.X.left.Modules) (hM : Scheme.Modules.IsInvertible M)
    (hfs : M.FiniteBySections A.group.X.hom)
    (ζ : ℕ → K) (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ n))
    (hζℓ : ∀ n, ζ (n + 1) ^ ℓ = ζ n)
    (b : Pairing ℓ A) (hb : IsRiemannPairing A M ℓ ζ b)
    (hdeg : ∀ n x, (underlyingScheme.map
      ((F.quotient n).multiplicationFactor (ℓ ^ n) (F.killed n))).finrank x = (ℓ ^ n) ^ g)
    (hdiv : ∀ n (x y : Integral ℓ (F.quotient n).variety), (ℓ : ℤ_[ℓ]) ^ n ∣
      b (integralMap ℓ ((F.quotient n).multiplicationFactor (ℓ ^ n) (F.killed n)) x)
        (integralMap ℓ ((F.quotient n).multiplicationFactor (ℓ ^ n) (F.killed n)) y)) :
    ∀ n, ∃ N : (F.quotient n).variety.group.X.left.Modules,
      Scheme.Modules.IsInvertible N ∧
      Nonempty ((Scheme.Modules.pullback (negMor (F.quotient n).variety.group.X.hom
        (GroupScheme.law (F.quotient n).variety.group))).obj N ≅ N) ∧
      N.FiniteBySections (F.quotient n).variety.group.X.hom ∧
      ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : K →+* k'),
        Scheme.Modules.geomFibreH0Finrank (F.quotient n).variety.group.X.hom N k' sk =
          3 ^ g * Scheme.Modules.geomFibreH0Finrank A.group.X.hom M k' sk := by
  intro n
  let D := F.quotient n
  let φ := D.multiplicationFactor (ℓ ^ n) (F.killed n)
  have hn : ℓ ^ n ≠ 0 := pow_ne_zero n (Fact.out : ℓ.Prime).ne_zero
  letI : IsFinite (underlyingScheme.map φ) :=
    (D.multiplicationFactor_isIsogeny (ℓ ^ n) (F.killed n) hn).1
  letI : Flat (underlyingScheme.map (multiplication A (ℓ ^ n))) :=
    (A.multiplication_finite_flat_degree (ℓ ^ n) hn).2.2.2.1
  letI : Flat (underlyingScheme.map φ) :=
    D.desc_flat (multiplication A (ℓ ^ n)) (F.killed n)
  obtain ⟨R, P, hR, hP, ⟨hr⟩⟩ := exists_root_of_tate_pullback_divisible
    ℓ hℓ ζ hζ hζℓ h2 A D.variety φ M hM b hb n (hdiv n)
  exact AbelianIsogenyRootNumerics.exists_symmetric_bundle_with_uniform_rank
    A D.variety (underlyingScheme.map φ) φ.hom.hom.w 𝒰 M hM hfs
    (ℓ ^ n) (pow_pos (Fact.out : ℓ.Prime).pos n) (hdeg n) R P hR hP hr

/-- Actual zero-dV surfaces and actual finite polarizations construct a graph
quotient family carrying symmetric finite polarizations with uniform rank.
No roots, anti-isometry or numerical bounds on the quotient are assumed. -/
theorem exists_zeroDV_graph_quotients_with_uniform_symmetric_polarizations
    (p : ℕ) [Fact p.Prime] [CharP K p] (h2 : (2 : K) ≠ 0)
    (A B : AbelianVariety K 2)
    (hA : GroupScheme.verschiebungCotangent p A.group A.groupScheme_law_commutative = 0)
    (hB : GroupScheme.verschiebungCotangent p B.group B.groupScheme_law_commutative = 0)
    (𝒰 : (A.prod B).group.X.left.OrderedAffineCover)
    (M : A.group.X.left.Modules) (N : B.group.X.left.Modules)
    (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N)
    (hMfs : M.FiniteBySections A.group.X.hom) (hNfs : N.FiniteBySections B.group.X.hom) :
    ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], n₀ < ℓ → (ℓ : K) ≠ 0 →
      ∃ (e : Rational ℓ A ≃ₗ[ℚ_[ℓ]] Rational ℓ B)
        (F : PrescribedLatticeQuotients ℓ (A.prod B)
          (integralIntersection ℓ (A.prod B) (productGraph ℓ A B e))),
        (∀ n x, (underlyingScheme.map
          ((F.quotient n).multiplicationFactor (ℓ ^ n) (F.killed n))).finrank x = (ℓ ^ n) ^ 4) ∧
        (∀ n, GroupScheme.verschiebungCotangent p (F.quotient n).variety.group
          (F.quotient n).variety.groupScheme_law_commutative = 0) ∧
        ∀ n, ∃ L : (F.quotient n).variety.group.X.left.Modules,
          Scheme.Modules.IsInvertible L ∧
          Nonempty ((Scheme.Modules.pullback (negMor (F.quotient n).variety.group.X.hom
            (GroupScheme.law (F.quotient n).variety.group))).obj L ≅ L) ∧
          L.FiniteBySections (F.quotient n).variety.group.X.hom ∧
          ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : K →+* k'),
            Scheme.Modules.geomFibreH0Finrank (F.quotient n).variety.group.X.hom L k' sk =
              3 ^ 4 * Scheme.Modules.geomFibreH0Finrank (A.prod B).group.X.hom
                (productLineBundle A B M N) k' sk := by
  obtain ⟨n₀, hn₀, hfamily⟩ := exists_polarized_zeroDV_graph_quotients_bound
    p A B hA hB M N hM hN hMfs hNfs
  refine ⟨n₀, hn₀, ?_⟩
  intro ℓ _ hn hℓ
  obtain ⟨ζ, b, e, F, hζ, hζℓ, hb, hdeg, hV, hdiv⟩ := hfamily ℓ hn hℓ
  refine ⟨e, F, hdeg, hV, ?_⟩
  exact F.exists_symmetric_bundles_with_uniform_rank ℓ hℓ h2 (A.prod B) 𝒰 _
    (productLineBundle A B M N) (productLineBundle_isInvertible A B M N hM hN)
    (productLineBundle_finiteBySections A B M N hMfs hNfs) ζ hζ hζℓ b hb hdeg hdiv

/-- The uniform numerical polarization construction needs only the two actual
zero-dV surfaces (and odd characteristic), not any supplied line bundles. -/
theorem exists_uniform_polarized_zeroDV_graph_quotients
    (p : ℕ) [Fact p.Prime] [CharP K p] (h2 : (2 : K) ≠ 0)
    (A B : AbelianVariety K 2)
    (hA : GroupScheme.verschiebungCotangent p A.group A.groupScheme_law_commutative = 0)
    (hB : GroupScheme.verschiebungCotangent p B.group B.groupScheme_law_commutative = 0) :
    ∃ d n₀ : ℕ, 0 < d ∧ 0 < n₀ ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], n₀ < ℓ → (ℓ : K) ≠ 0 →
      ∃ (e : Rational ℓ A ≃ₗ[ℚ_[ℓ]] Rational ℓ B)
        (F : PrescribedLatticeQuotients ℓ (A.prod B)
          (integralIntersection ℓ (A.prod B) (productGraph ℓ A B e))),
        (∀ n x, (underlyingScheme.map
          ((F.quotient n).multiplicationFactor (ℓ ^ n) (F.killed n))).finrank x = (ℓ ^ n) ^ 4) ∧
        (∀ n, GroupScheme.verschiebungCotangent p (F.quotient n).variety.group
          (F.quotient n).variety.groupScheme_law_commutative = 0) ∧
        ∀ n, ∃ L : (F.quotient n).variety.group.X.left.Modules,
          Scheme.Modules.IsInvertible L ∧
          Nonempty ((Scheme.Modules.pullback (negMor (F.quotient n).variety.group.X.hom
            (GroupScheme.law (F.quotient n).variety.group))).obj L ≅ L) ∧
          L.FiniteBySections (F.quotient n).variety.group.X.hom ∧
          Scheme.Modules.geomFibreH0Finrank (F.quotient n).variety.group.X.hom L
            K (RingHom.id K) = d := by
  obtain ⟨M, hM, hMfs⟩ :=
    AbelianSchemePropertyBundle.exists_isInvertible_finiteBySections K A.group.X.hom
      A.abelianSchemePropertyBundle
  obtain ⟨N, hN, hNfs⟩ :=
    AbelianSchemePropertyBundle.exists_isInvertible_finiteBySections K B.group.X.hom
      B.abelianSchemePropertyBundle
  obtain ⟨𝒰⟩ := Scheme.OrderedAffineCover.nonempty_of_compactSpace (A.prod B).group.X.left
  have hdim (s : Spec (CommRingCat.of K)) :
      topologicalKrullDim ((A.prod B).group.X.hom.base ⁻¹' {s}) = 4 :=
    SmoothOfRelativeDimension.topologicalKrullDim_preimage_singleton_eq (A.prod B).group.X.hom 4 s
      ((A.prod B).abelianSchemePropertyBundle.connectedFibres s).nonempty
  have hpos := (kernelPts_finite_and_geomFibreH0Finrank_pos_of_finiteBySections
    K (A.prod B).group.X.hom (GroupScheme.law (A.prod B).group)
    (A.prod B).groupScheme_law_commutative (A.prod B).abelianSchemePropertyBundle 4 hdim
    (productLineBundle A B M N) (productLineBundle_isInvertible A B M N hM hN)
    (productLineBundle_finiteBySections A B M N hMfs hNfs)).2 K (RingHom.id K)
  obtain ⟨n₀, hn₀, hf⟩ := exists_zeroDV_graph_quotients_with_uniform_symmetric_polarizations
    p h2 A B hA hB 𝒰 M N hM hN hMfs hNfs
  refine ⟨_, n₀, Nat.mul_pos (by decide : 0 < 3 ^ 4) hpos, hn₀, ?_⟩
  intro ℓ _ hn hℓ
  obtain ⟨e, F, hdeg, hV, hpol⟩ := hf ℓ hn hℓ
  refine ⟨e, F, hdeg, hV, ?_⟩
  intro n
  obtain ⟨L, hL, hs, hfs, hrank⟩ := hpol n
  exact ⟨L, hL, hs, hfs, hrank K (RingHom.id K)⟩

end SupersingularCurves.Geometry.ScalarFrobeniusTate
