/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentFixedComponents
import SupersingularCurves.Geometry.GradedFixedSubalgebra
import SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentProjBaseChange

/-!
# Proj of the actual fixed graded algebra

For a degree-preserving Frobenius-semilinear action, the fixed subalgebra has
its genuine inherited grading. Each finite-dimensional component satisfies
scalar extension. Consequently its Proj is an actual model over the finite
fixed field, with a geometric base-change square to the original Proj.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FrobeniusDescent
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FrobeniusFiniteFieldDescentSectionProj

variable {K : Type u} [Field K] [IsAlgClosed K]
variable (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)
variable {R : Type u} [CommRing R] [Algebra K R]
variable (θ : R →+* R) (hθ : ∀ (c : K) (x : R), θ (c • x) = c ^ (p ^ s) • θ x)
variable (𝓡 : ℕ → Submodule K R) [GradedAlgebra 𝓡]
variable (hdeg : ∀ n, ∀ x ∈ 𝓡 n, θ x ∈ 𝓡 n)

/-- The actual grading of the fixed coefficient algebra. -/
abbrev fixedGrading : ℕ → Submodule (fixedField K p s) (fixedAlgebra p s θ hθ) :=
  GradedFixedSubalgebra.grade 𝓡 (fixedCoefficientAction p s θ hθ)

/-- No grading is assumed on the fixed algebra: it is constructed from the
ambient homogeneous decomposition. -/
abbrev fixedGradedAlgebra : GradedAlgebra (fixedGrading p s θ hθ 𝓡) :=
  GradedFixedSubalgebra.gradedAlgebra 𝓡 (fixedCoefficientAction p s θ hθ) hdeg

include hθ hdeg in
/-- The actual Proj of a Frobenius-stable graded algebra descends to the
finite fixed field; the assertion is the genuine scheme base-change square. -/
theorem exists_fixedField_proj_model (hs : s ≠ 0) (hinj : Function.Injective θ)
    (hfinite : ∀ n, FiniteDimensional K (𝓡 n)) :
    ∃ (X₀ : Scheme.{u}) (c₀ : X₀ ⟶ Spec (CommRingCat.of (fixedField K p s)))
      (d : Proj 𝓡 ⟶ X₀),
      IsPullback d
        (Proj.toSpecZero 𝓡 ≫ Spec.map (CommRingCat.ofHom
          ((GradedRing.projZeroRingHom' 𝓡).comp (algebraMap K R)))) c₀
        (Spec.map (CommRingCat.ofHom (algebraMap (fixedField K p s) K))) := by
  let R₀ := fixedAlgebra p s θ hθ
  let 𝓡₀ := fixedGrading p s θ hθ 𝓡
  let := fixedGradedAlgebra p s θ hθ 𝓡 hdeg
  let ϑ : R₀ →ₐ[fixedField K p s] R := (fixedAlgebra p s θ hθ).val
  have hd : ∀ n, ∀ x ∈ 𝓡₀ n, ϑ x ∈ 𝓡 n := fun _ _ hx => hx
  have hbc : ∀ n, IsBaseChange K (pieceMap K R₀ 𝓡₀ R 𝓡 ϑ hd n) := by
    intro n
    let := hfinite n
    change IsBaseChange K (fixedComponentMap p s θ hθ 𝓡 n)
    exact fixedComponent_isBaseChange p s θ hθ 𝓡 hdeg hs hinj n
  exact ⟨Proj 𝓡₀, _, _, isPullback_projMap_of_piece_baseChange K R₀ 𝓡₀ R 𝓡 ϑ hd hbc⟩

end SupersingularCurves.Geometry.FrobeniusDescent
