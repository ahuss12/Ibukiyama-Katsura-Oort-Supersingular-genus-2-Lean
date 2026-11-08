/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import Mathlib.RingTheory.GradedAlgebra.RingHom

/-!
# The grading on a fixed subalgebra

A degree-preserving algebra endomorphism over a smaller coefficient ring has a
graded equalizer, even when it is not linear over the original coefficient ring.
The decomposition is the actual componentwise decomposition of the ambient ring.
-/

set_option autoImplicit false
noncomputable section
open scoped DirectSum

namespace SupersingularCurves.Geometry.GradedFixedSubalgebra

variable {k K A : Type*} [CommRing k] [CommRing K] [CommRing A]
  [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A]
  (𝓡 : ℕ → Submodule K A) [GradedAlgebra 𝓡] (θ : A →ₐ[k] A)

/-- The fixed algebra is literally the algebra-homomorphism equalizer. -/
abbrev fixed : Subalgebra k A := θ.equalizer (AlgHom.id k A)

/-- Homogeneous fixed elements, retaining the original ambient grading. -/
def grade (n : ℕ) : Submodule k (fixed θ) :=
  ((𝓡 n).restrictScalars k).comap (fixed θ).val.toLinearMap

omit [GradedAlgebra 𝓡] in
@[simp] theorem mem_grade (n : ℕ) (x : fixed θ) :
    x ∈ grade 𝓡 θ n ↔ (x : A) ∈ 𝓡 n := Iff.rfl

instance grade_gradedMonoid : SetLike.GradedMonoid (grade 𝓡 θ) where
  one_mem := SetLike.GradedOne.one_mem (A := 𝓡)
  mul_mem i j x y hx hy := by
    change (x : A) * (y : A) ∈ 𝓡 (i + j)
    exact SetLike.GradedMul.mul_mem hx hy

variable (hθ : ∀ n x, x ∈ 𝓡 n → θ x ∈ 𝓡 n)

/-- The action is a graded ring homomorphism; no `K`-linearity is required. -/
def gradedMap : 𝓡 →+*ᵍ 𝓡 where
  __ := θ.toRingHom
  map_mem := hθ _ _

include hθ in
omit [Algebra k K] [IsScalarTower k K A] in
theorem map_component (x : A) (n : ℕ) :
    θ (DirectSum.decompose 𝓡 x n) = DirectSum.decompose 𝓡 (θ x) n :=
  (gradedMap 𝓡 θ hθ).map_directSumDecompose

include hθ in
omit [Algebra k K] [IsScalarTower k K A] in
theorem component_fixed (x : fixed θ) (n : ℕ) :
    θ (DirectSum.decompose 𝓡 (x : A) n) = DirectSum.decompose 𝓡 (x : A) n := by
  rw [map_component 𝓡 θ hθ]
  exact congrArg (fun a : A => (DirectSum.decompose 𝓡 a n : A)) x.property

/-- Each ambient homogeneous component of a fixed element is fixed. -/
def component (x : fixed θ) (n : ℕ) : grade 𝓡 θ n :=
  ⟨⟨DirectSum.decompose 𝓡 (x : A) n, component_fixed 𝓡 θ hθ x n⟩,
    (DirectSum.decompose 𝓡 (x : A) n).property⟩

/-- Inclusion of a fixed component in the original homogeneous component. -/
def inclusion (n : ℕ) : grade 𝓡 θ n →+ 𝓡 n where
  toFun x := ⟨(x.1 : A), x.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

omit [GradedAlgebra 𝓡] in
theorem inclusion_injective (n : ℕ) : Function.Injective (inclusion 𝓡 θ n) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : 𝓡 n => (z : A)) h

private def includeSum : (⨁ n, grade 𝓡 θ n) →+ ⨁ n, 𝓡 n :=
  DirectSum.map (inclusion 𝓡 θ)

private theorem includeSum_injective : Function.Injective (includeSum 𝓡 θ) :=
  (DirectSum.map_injective (inclusion 𝓡 θ)).mpr (inclusion_injective 𝓡 θ)

/-- The actual finite component decomposition of a fixed element. -/
def decomposeFixed (x : fixed θ) : ⨁ n, grade 𝓡 θ n := by
  classical
  exact DFinsupp.mk (DirectSum.decompose 𝓡 (x : A)).support
    (fun n => component 𝓡 θ hθ x n)

private theorem includeSum_decomposeFixed (x : fixed θ) :
    includeSum 𝓡 θ (decomposeFixed 𝓡 θ hθ x) = DirectSum.decompose 𝓡 (x : A) := by
  classical
  apply DFinsupp.ext
  intro n
  change (inclusion 𝓡 θ n) (decomposeFixed 𝓡 θ hθ x n) = _
  by_cases hn : n ∈ (DirectSum.decompose 𝓡 (x : A)).support
  · simp only [decomposeFixed, DFinsupp.mk_of_mem hn]
    rfl
  · rw [decomposeFixed, DFinsupp.mk_of_notMem hn, map_zero,
      DFinsupp.notMem_support_iff.mp hn]

private theorem includeSum_recompose (z : ⨁ n, grade 𝓡 θ n) :
    ((DirectSum.coeAddMonoidHom (grade 𝓡 θ) z : fixed θ) : A) =
      DirectSum.coeAddMonoidHom 𝓡 (includeSum 𝓡 θ z) := by
  induction z using DirectSum.induction_on with
  | zero => simp only [map_zero, ZeroMemClass.coe_zero]
  | of n x =>
    simp only [includeSum, DirectSum.map_of, DirectSum.coeAddMonoidHom_of]
    rfl
  | add x y hx hy => simp only [map_add, AddMemClass.coe_add, hx, hy]

/-- The fixed equalizer inherits a grading over the smaller coefficient ring. -/
@[instance_reducible]
def gradedAlgebra : GradedAlgebra (grade 𝓡 θ) where
  __ := grade_gradedMonoid 𝓡 θ
  decompose' := decomposeFixed 𝓡 θ hθ
  left_inv x := by
    apply Subtype.ext
    rw [includeSum_recompose, includeSum_decomposeFixed]
    exact (DirectSum.decompose 𝓡).symm_apply_apply (x : A)
  right_inv z := by
    apply includeSum_injective 𝓡 θ
    rw [includeSum_decomposeFixed, includeSum_recompose]
    exact (DirectSum.decompose 𝓡).apply_symm_apply (includeSum 𝓡 θ z)

/-- The induced grading has exactly the ambient homogeneous components. -/
theorem decompose_coe (x : fixed θ) (n : ℕ) :
    letI := gradedAlgebra 𝓡 θ hθ
    ((DirectSum.decompose (grade 𝓡 θ) x n : fixed θ) : A) =
      DirectSum.decompose 𝓡 (x : A) n := by
  let := gradedAlgebra 𝓡 θ hθ
  have h := congrArg (fun z : ⨁ n, 𝓡 n => (z n : A))
    (includeSum_decomposeFixed 𝓡 θ hθ x)
  exact h

end SupersingularCurves.Geometry.GradedFixedSubalgebra
