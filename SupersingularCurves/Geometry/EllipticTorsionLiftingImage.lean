/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.EllipticTorsionLiftingLevels

/-!
# The actual p-multiplication image in p-squared torsion

The coordinate ring of A[p] is constructed as the image of [p]* in the
coordinate ring of A[p²]. The injectivity and surjectivity needed for this
identification follow from the actual faithfully flat projection and closed
kernel inclusion. No supplied image identification is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.TorsionLevels
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian

variable {K : Type u} [Field K] {g : ℕ} (A : AbelianVariety K g)

instance inclusion_isClosedImmersion (n : ℕ) : IsClosedImmersion (inclusion A n) := by
  letI : IsClosedImmersion (GroupScheme.zero A.group).1 :=
    isClosedImmersion_of_comp_eq_id A.group.X.hom (GroupScheme.zero A.group).1
      (GroupScheme.zero A.group).2
  infer_instance

instance smallerToLarger_isClosedImmersion (n m : ℕ) :
    IsClosedImmersion (smallerToLarger A n m) := by
  letI : IsClosedImmersion (smallerToLarger A n m ≫ inclusion A (n * m)) := by
    rw [smallerToLarger_inclusion]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion
    (smallerToLarger A n m) (inclusion A (n * m))

/-- Actual multiplication on the p-squared torsion, through its p-torsion image. -/
def squareMultiplication (p : ℕ) : kernel A (p * p) ⟶ kernel A (p * p) :=
  multiplication A p p ≫ smallerToLarger A p p

/-- The constructed endomorphism really is the restriction of ambient [p]. -/
@[reassoc]
theorem squareMultiplication_inclusion (p : ℕ) :
    squareMultiplication A p ≫ inclusion A (p * p) =
      inclusion A (p * p) ≫ (GroupScheme.law A.group).schemeNsmul p := by
  rw [squareMultiplication, Category.assoc, smallerToLarger_inclusion,
    multiplication_inclusion]

variable [IsAlgClosed K]

theorem kernel_isAffine (n : ℕ) (hn : n ≠ 0) : IsAffine (kernel A n) := by
  letI : IsFinite (base A n) := (A.multiplication_finite_flat_degree n hn).1
  exact isAffine_of_isAffineHom (base A n)

/-- Actual pullback of functions along the torsion projection is injective. -/
theorem multiplication_appTop_injective (n m : ℕ) (hn : n ≠ 0) (hm : m ≠ 0) :
    Function.Injective (multiplication A n m).appTop.hom := by
  letI := kernel_isAffine A n hn
  letI := kernel_isAffine A (n * m) (Nat.mul_ne_zero hn hm)
  exact ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine
    (multiplication A n m)).mp
      ⟨multiplication_flat A n m hm, multiplication_surjective A n m hm⟩).injective

/-- Restriction to the smaller actual torsion scheme is surjective on functions. -/
theorem smallerToLarger_appTop_surjective (n m : ℕ) (hn : n ≠ 0) (hm : m ≠ 0) :
    Function.Surjective (smallerToLarger A n m).appTop.hom := by
  letI := kernel_isAffine A (n * m) (Nat.mul_ne_zero hn hm)
  exact (IsClosedImmersion.isAffine_surjective_of_isAffine
    (smallerToLarger A n m)).2

/-- The actual coordinate algebra of A[p] is the image of [p]* on A[p²]. -/
def coordinateImageEquiv (p : ℕ) (hp : p ≠ 0) :
    Γ(kernel A p, ⊤) ≃+* (squareMultiplication A p).appTop.hom.range := by
  let q := (multiplication A p p).appTop.hom
  let j := (smallerToLarger A p p).appTop.hom
  have heq : (squareMultiplication A p).appTop.hom = q.comp j := by
    simp only [squareMultiplication, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
    rfl
  have hmem : ∀ x : Γ(kernel A p, ⊤), q x ∈ (squareMultiplication A p).appTop.hom.range := by
    intro x
    obtain ⟨y, hy⟩ := smallerToLarger_appTop_surjective A p p hp hp x
    refine ⟨y, ?_⟩
    rw [heq]
    exact congrArg q hy
  let e := q.codRestrict (squareMultiplication A p).appTop.hom.range hmem
  exact RingEquiv.ofBijective e ⟨
    fun x y h => multiplication_appTop_injective A p p hp hp (congrArg Subtype.val h),
    fun z => by
      obtain ⟨y, hy⟩ := z.property
      refine ⟨j y, Subtype.ext ?_⟩
      change q (j y) = (z : Γ(kernel A (p * p), ⊤))
      rw [← RingHom.comp_apply, ← heq]
      exact hy⟩

/-- The identification sends restriction of a function to its [p]* pullback. -/
theorem coordinateImageEquiv_restriction (p : ℕ) (hp : p ≠ 0)
    (a : Γ(kernel A (p * p), ⊤)) :
    ((coordinateImageEquiv A p hp ((smallerToLarger A p p).appTop a) :
      (squareMultiplication A p).appTop.hom.range) : Γ(kernel A (p * p), ⊤)) =
      (squareMultiplication A p).appTop a := by
  change (multiplication A p p).appTop ((smallerToLarger A p p).appTop a) = _
  simp only [squareMultiplication, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    RingHom.comp_apply]

end SupersingularCurves.Geometry.TorsionLevels
