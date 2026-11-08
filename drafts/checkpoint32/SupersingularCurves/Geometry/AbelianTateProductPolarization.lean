/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.AbelianProductLineBundle
import SupersingularCurves.Geometry.AbelianTateRiemannFiniteKernel
import SupersingularCurves.Geometry.AbelianTateRiemannPullback
import SupersingularCurves.Geometry.ScalarFrobeniusTatePolarizedGraph
import SupersingularCurves.Geometry.AbelianVerschiebungBinaryProducts

/-!
# Actual product polarizations and their isotropic graph quotients

The product bundle and its Riemann pairing are constructed from the bundles
on the two factors. At every sufficiently large auxiliary prime, common roots
of unity give perfect alternating pairings, hence the actual isotropic graph.
Its quotient family has exact degrees, zero dV and the Riemann divisibility
needed for polarization roots. No finite-model hypothesis is proved here.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SupersingularCurves.Geometry.AbelianTate
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry GoodReductionJacobian
open ScalarFrobeniusTate

variable {K : Type} [Field K] [IsAlgClosed K] {g h : ℕ}

local instance {d : ℕ} (A : AbelianVariety K d) : Smooth A.group.X.hom :=
  SmoothOfRelativeDimension.smooth d A.group.X.hom

/-- The sum of the actual projected pairings is the Riemann pairing of the
actual product line bundle, with one common normalization. -/
theorem productLineBundle_isRiemannPairing
    (A : AbelianVariety K g) (B : AbelianVariety K h)
    (M : A.group.X.left.Modules) (N : B.group.X.left.Modules)
    (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0)
    (ζ : ℕ → K) (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ n))
    (hζℓ : ∀ n, ζ (n + 1) ^ ℓ = ζ n)
    (b : Pairing ℓ A) (c : Pairing ℓ B)
    (hb : IsRiemannPairing A M ℓ ζ b) (hc : IsRiemannPairing B N ℓ ζ c) :
    IsRiemannPairing (A.prod B) (productLineBundle A B M N) ℓ ζ
      (integralProductPairing ℓ A B b c) := by
  exact IsRiemannPairing.add_of_iso_tensor (A.prod B) _ _
    (hM.pullback (A.prodFst B).hom.hom.left) (hN.pullback (A.prodSnd B).hom.hom.left)
    ℓ hℓ ζ hζ hζℓ (hb.pullback (A.prodFst B)) (hc.pullback (A.prodSnd B))
    (productLineBundle A B M N) ⟨Iso.refl _⟩

/-- Actual finite polarizations give simultaneously perfect pairings with
common roots of unity at every sufficiently large auxiliary prime. -/
theorem exists_common_perfect_pairings_bound
    (A : AbelianVariety K g) (B : AbelianVariety K h)
    (M : A.group.X.left.Modules) (N : B.group.X.left.Modules)
    (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N)
    (hMfs : M.FiniteBySections A.group.X.hom) (hNfs : N.FiniteBySections B.group.X.hom) :
    ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], n₀ < ℓ → (ℓ : K) ≠ 0 →
      ∃ (ζ : ℕ → K) (b : Pairing ℓ A) (c : Pairing ℓ B),
        (∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ n)) ∧ (∀ n, ζ (n + 1) ^ ℓ = ζ n) ∧
        IsRiemannPairing A M ℓ ζ b ∧ b.IsAlt ∧ b.IsPerfPair ∧
        IsRiemannPairing B N ℓ ζ c ∧ c.IsAlt ∧ c.IsPerfPair := by
  obtain ⟨nA, hnA, hA⟩ := exists_bound_translation_kernel A M hM hMfs
  obtain ⟨nB, _, hB⟩ := exists_bound_translation_kernel B N hN hNfs
  refine ⟨max nA nB, hnA.trans_le (le_max_left _ _), ?_⟩
  intro ℓ _ hn hℓ
  obtain ⟨ζ, hζ, hζℓ⟩ := IsAlgClosed.exists_isPrimitiveRoot_pow_and_pow_succ_eq K ℓ hℓ
  obtain ⟨b, hb, hbperf⟩ := exists_perfect_riemannPairing A M hM ℓ hℓ ζ hζ hζℓ
    (hA ℓ Fact.out (lt_of_le_of_lt (le_max_left _ _) hn))
  obtain ⟨c, hc, hcperf⟩ := exists_perfect_riemannPairing B N hN ℓ hℓ ζ hζ hζℓ
    (hB ℓ Fact.out (lt_of_le_of_lt (le_max_right _ _) hn))
  exact ⟨ζ, b, c, hζ, hζℓ, hb, IsRiemannPairing.isAlt A M hM ℓ hℓ ζ hζ hζℓ hb,
    hbperf, hc, IsRiemannPairing.isAlt B N hN ℓ hℓ ζ hζ hζℓ hc, hcperf⟩

/-- Actual line bundles and zero dV on the factors construct the product
Riemann pairing, anti-isometry, graph and quotient family. Neither an abstract
pairing nor an anti-isometry nor vanishing on the product is a premise. -/
theorem exists_polarized_zeroDV_graph_quotients_bound
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (A B : AbelianVariety K 2)
    (hA : GroupScheme.verschiebungCotangent p A.group A.groupScheme_law_commutative = 0)
    (hB : GroupScheme.verschiebungCotangent p B.group B.groupScheme_law_commutative = 0)
    (M : A.group.X.left.Modules) (N : B.group.X.left.Modules)
    (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N)
    (hMfs : M.FiniteBySections A.group.X.hom) (hNfs : N.FiniteBySections B.group.X.hom) :
    ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], n₀ < ℓ → (ℓ : K) ≠ 0 →
      ∃ (ζ : ℕ → K) (b : Pairing ℓ (A.prod B))
        (e : Rational ℓ A ≃ₗ[ℚ_[ℓ]] Rational ℓ B)
        (F : PrescribedLatticeQuotients ℓ (A.prod B)
          (integralIntersection ℓ (A.prod B) (productGraph ℓ A B e))),
        (∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ n)) ∧ (∀ n, ζ (n + 1) ^ ℓ = ζ n) ∧
        IsRiemannPairing (A.prod B) (productLineBundle A B M N) ℓ ζ b ∧
        (∀ n x, (underlyingScheme.map
          ((F.quotient n).multiplicationFactor (ℓ ^ n) (F.killed n))).finrank x = (ℓ ^ n) ^ 4) ∧
        (∀ n, GroupScheme.verschiebungCotangent p (F.quotient n).variety.group
          (F.quotient n).variety.groupScheme_law_commutative = 0) ∧
        ∀ n (x y : Integral ℓ (F.quotient n).variety), (ℓ : ℤ_[ℓ]) ^ n ∣
          b (integralMap ℓ ((F.quotient n).multiplicationFactor (ℓ ^ n) (F.killed n)) x)
            (integralMap ℓ ((F.quotient n).multiplicationFactor (ℓ ^ n) (F.killed n)) y) := by
  obtain ⟨n₀, hn₀, hpair⟩ := exists_common_perfect_pairings_bound A B M N hM hN hMfs hNfs
  refine ⟨n₀, hn₀, ?_⟩
  intro ℓ _ hn hℓ
  obtain ⟨ζ, b, c, hζ, hζℓ, hb, hbalt, hbperf, hc, hcalt, hcperf⟩ := hpair ℓ hn hℓ
  letI := hbperf
  letI := hcperf
  obtain ⟨e, F, hd, hV, hdiv⟩ :=
    exists_isotropic_graph_quotients_with_degree_and_zeroDV ℓ A B hℓ b c hbalt hcalt p
      (A.verschiebungCotangent_prod_eq_zero p B hA hB)
  exact ⟨ζ, integralProductPairing ℓ A B b c, e, F, hζ, hζℓ,
    productLineBundle_isRiemannPairing A B M N hM hN ℓ hℓ ζ hζ hζℓ b c hb hc,
    hd, hV, hdiv⟩

end SupersingularCurves.Geometry.AbelianTate
