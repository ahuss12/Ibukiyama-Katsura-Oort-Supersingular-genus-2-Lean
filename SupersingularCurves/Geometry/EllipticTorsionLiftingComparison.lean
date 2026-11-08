/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.EllipticTorsionLiftingVerschiebung

/-!
# Detecting canonical Verschiebung from the next torsion level

The identities FV=VF=[p] on a single killed-by-p Hopf algebra do not
characterize Verschiebung. This file proves the precise two-level comparison:
compatibility with the next torsion level and its multiplication-by-p image
identifies a proposed ambient restriction with Cartier-dual Frobenius.
The image identification is an explicit hypothesis here, not a construction
of the elliptic p-divisible group or the Oort lifting theorem.
-/

set_option autoImplicit false
noncomputable section
universe u v w

namespace SupersingularCurves.Geometry.PerfectHopfVerschiebung

variable {K : Type u} [Field K] (p : ℕ) [Fact p.Prime]
  [CharP K p] [PerfectRing K p]
variable {A : Type v} [CommRing A] [HopfAlgebra K A]
  [Coalgebra.IsCocomm K A] [Module.Finite K A]
variable {B : Type w} [CommRing B] [HopfAlgebra K B]
  [Coalgebra.IsCocomm K B] [Module.Finite K B]

/-- The next level removes the nonuniqueness of the equation FV=[p]. -/
theorem eq_canonical_of_two_levels
    (t : B →ₐc[K] A) (ht : Function.Surjective t)
    (e : A ≃ₐ[K] ↥(PDivisibleGroup.Hopf.nsmulAlgHom K B p).range)
    (he : ∀ b : B, ((e (t b) : ↥(PDivisibleGroup.Hopf.nsmulAlgHom K B p).range) : B) =
      PDivisibleGroup.Hopf.nsmulAlgHom K B p b)
    (V₀ : A → A) (V₁ : B → B)
    (htrans : ∀ b : B, t (V₁ b) = V₀ (t b))
    (hcomm : ∀ b : B,
      PDivisibleGroup.Hopf.nsmulAlgHom K B p (V₁ b) =
        V₁ (PDivisibleGroup.Hopf.nsmulAlgHom K B p b))
    (hVF : ∀ b : B, V₁ (b ^ p) = PDivisibleGroup.Hopf.nsmulAlgHom K B p b) :
    V₀ = verschiebung (K := K) p A := by
  funext a
  obtain ⟨b, rfl⟩ := ht a
  apply e.injective
  apply Subtype.ext
  change ((e (V₀ (t b)) : ↥(PDivisibleGroup.Hopf.nsmulAlgHom K B p).range) : B) =
    ((e (verschiebung (K := K) p A (t b)) :
      ↥(PDivisibleGroup.Hopf.nsmulAlgHom K B p).range) : B)
  rw [← htrans b, he, hcomm b, ← verschiebung_pow (K := K) p B b,
    hVF, ← naturality p t b, he]

/-- In particular the proposed restriction has the canonical Cartier pairing.
All scalar twists remain visible over the perfect base field. -/
theorem pairing_of_two_levels
    (t : B →ₐc[K] A) (ht : Function.Surjective t)
    (e : A ≃ₐ[K] ↥(PDivisibleGroup.Hopf.nsmulAlgHom K B p).range)
    (he : ∀ b : B, ((e (t b) : ↥(PDivisibleGroup.Hopf.nsmulAlgHom K B p).range) : B) =
      PDivisibleGroup.Hopf.nsmulAlgHom K B p b)
    (V₀ : A → A) (V₁ : B → B)
    (htrans : ∀ b : B, t (V₁ b) = V₀ (t b))
    (hcomm : ∀ b : B,
      PDivisibleGroup.Hopf.nsmulAlgHom K B p (V₁ b) =
        V₁ (PDivisibleGroup.Hopf.nsmulAlgHom K B p b))
    (hVF : ∀ b : B, V₁ (b ^ p) = PDivisibleGroup.Hopf.nsmulAlgHom K B p b)
    (φ : CartierDual K A) (a : A) :
    φ (V₀ a) ^ p = (φ ^ p) a := by
  rw [eq_canonical_of_two_levels p t ht e he V₀ V₁ htrans hcomm hVF]
  exact pairing (K := K) p A φ a

end SupersingularCurves.Geometry.PerfectHopfVerschiebung
