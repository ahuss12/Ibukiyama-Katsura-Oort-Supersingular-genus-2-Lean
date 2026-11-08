/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.GroupTranslationCotangent
import Mathlib.RingTheory.Derivation.Basic

/-! # Invariant derivations from actual affine group laws -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.AffineInvariantDerivation
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

variable (K : Type u) [Field K]
variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra K A] [Algebra K B] [Algebra K C]

abbrev dual (A : Type u) [CommRing A] := TrivSqZeroExt A A

/-- Extension of both components of a dual number along an algebra map. -/
def dualMap (f : A →ₐ[K] B) : dual A →ₐ[K] dual B where
  toFun x := ⟨f x.fst, f x.snd⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_mul' x y := by
    ext <;> simp [TrivSqZeroExt.snd_mul, smul_eq_mul, mul_comm]
  commutes' r := by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl']

abbrev toBase (A : Type u) [CommRing A] [Algebra K A] :
    Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K A))

/-- An actual affine test point from its coordinate algebra map. -/
def point (f : A →ₐ[K] B) : SchemeHomOver (toBase K B) (toBase K A) :=
  ⟨Spec.map (CommRingCat.ofHom f.toRingHom), by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext r
    exact f.commutes r⟩

/-- The coordinate algebra map of an actual affine test point. -/
def coordinates (q : SchemeHomOver (toBase K B) (toBase K A)) : A →ₐ[K] B := by
  let r := (Spec.preimage q.1).hom
  have hr : r.comp (algebraMap K A) = algebraMap K B := by
    have hh : CommRingCat.ofHom (algebraMap K A) ≫ Spec.preimage q.1 =
        CommRingCat.ofHom (algebraMap K B) := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage]
      exact q.2
    exact congrArg CommRingCat.Hom.hom hh
  exact { r with commutes' := fun a => DFunLike.congr_fun hr a }

@[simp] theorem point_coordinates (q : SchemeHomOver (toBase K B) (toBase K A)) :
    point K (coordinates K q) = q := by
  apply Subtype.ext
  exact Spec.map_preimage q.1

@[simp] theorem coordinates_point (f : A →ₐ[K] B) : coordinates K (point K f) = f := by
  have h := congrArg CommRingCat.Hom.hom
    (Spec.preimage_map (CommRingCat.ofHom f.toRingHom))
  ext x
  exact DFunLike.congr_fun h x

theorem point_injective : Function.Injective (point K (A := A) (B := B)) := by
  intro f g h
  simpa only [coordinates_point] using congrArg (coordinates K) h

@[simp] theorem point_comp (f : A →ₐ[K] B) (g : B →ₐ[K] C) :
    (point K (g.comp f)).1 = (point K g).1 ≫ (point K f).1 := by
  dsimp only [point]
  rw [← Spec.map_comp]
  rfl

variable (L : RelativeGroupLaw K (toBase K A))

/-- Multiplication of affine test points, expressed on their actual coordinate maps. -/
def pointMul (f g : A →ₐ[K] B) : A →ₐ[K] B :=
  coordinates K (L.mul (toBase K B) (point K f) (point K g))

@[simp] theorem point_pointMul (f g : A →ₐ[K] B) :
    point K (pointMul K L f g) = L.mul (toBase K B) (point K f) (point K g) :=
  point_coordinates K _

/-- The given group law is natural under every coefficient-algebra map. -/
theorem pointMul_natural (f g : A →ₐ[K] B) (j : B →ₐ[K] C) :
    j.comp (pointMul K L f g) = pointMul K L (j.comp f) (j.comp g) := by
  apply point_injective K
  apply Subtype.ext
  rw [point_comp]
  have h := L.mul_natural (toBase K B) (toBase K C)
    (point K j).1 (point K j).2 (point K f) (point K g)
  have hcomp (a : A →ₐ[K] B) :
      schemeHomOverComp (point K j).1 (point K j).2 (point K a) = point K (j.comp a) := by
    apply Subtype.ext
    exact (point_comp K a j).symm
  rw [hcomp, hcomp] at h
  simpa only [point_pointMul, schemeHomOverComp_coe] using congrArg Subtype.val h

variable (ε : A →ₐ[K] K)
  (hε : (L.one (𝟙 (Spec (CommRingCat.of K)))).1 = Spec.map (CommRingCat.ofHom ε.toRingHom))

include hε in
/-- The supplied augmentation is the identity on every affine test scheme. -/
theorem point_unit :
    point K ((Algebra.ofId K B).comp ε) = L.one (toBase K B) := by
  apply Subtype.ext
  rw [point_comp]
  have h := congrArg Subtype.val
    (L.one_natural (𝟙 _) (toBase K B) (toBase K B) (Category.comp_id _))
  simpa only [schemeHomOverComp_coe, hε, point, Algebra.ofId] using h

include hε in
theorem pointMul_one_left (f : A →ₐ[K] B) :
    pointMul K L ((Algebra.ofId K B).comp ε) f = f := by
  apply point_injective K
  rw [point_pointMul, point_unit K L ε hε, L.one_mul]

include hε in
theorem pointMul_one_right (f : A →ₐ[K] B) :
    pointMul K L f ((Algebra.ofId K B).comp ε) = f := by
  apply point_injective K
  rw [point_pointMul, point_unit K L ε hε, L.mul_one]

variable (τ : A →ₐ[K] dual K)
  (hτ : (TrivSqZeroExt.fstHom K K K).comp τ = ε)

/-- Translation of the universal dual-number point by the supplied identity tangent. -/
def translationLift : A →ₐ[K] dual A :=
  pointMul K L ((dualMap K (Algebra.ofId K A)).comp τ)
    (TrivSqZeroExt.inlAlgHom K A A)

include hε hτ in
/-- Infinitesimal translation reduces to the universal point. -/
theorem translationLift_fst :
    (TrivSqZeroExt.fstHom K A A).comp (translationLift K L τ) = AlgHom.id K A := by
  rw [translationLift, pointMul_natural]
  have hleft : (TrivSqZeroExt.fstHom K A A).comp
      ((dualMap K (Algebra.ofId K A)).comp τ) = (Algebra.ofId K A).comp ε := by
    ext x
    change algebraMap K A (τ x).fst = algebraMap K A (ε x)
    exact congrArg (algebraMap K A) (DFunLike.congr_fun hτ x)
  have hright : (TrivSqZeroExt.fstHom K A A).comp
      (TrivSqZeroExt.inlAlgHom K A A) = AlgHom.id K A := by ext; rfl
  rw [hleft, hright, pointMul_one_left K L ε hε]

include hε in
/-- Evaluation at the identity recovers the original tangent point. -/
theorem translationLift_augmentation :
    (dualMap K ε).comp (translationLift K L τ) = τ := by
  rw [translationLift, pointMul_natural]
  have hleft : (dualMap K ε).comp ((dualMap K (Algebra.ofId K A)).comp τ) = τ := by
    ext x <;> simp [dualMap]
  have hright : (dualMap K ε).comp (TrivSqZeroExt.inlAlgHom K A A) =
      (Algebra.ofId K (dual K)).comp ε := by
    ext x <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  rw [hleft, hright, pointMul_one_right K L ε hε]

/-- The second component of a genuine first-order lift of the identity
is a derivation of the original coordinate algebra. -/
def derivationOfLift (r : A →ₐ[K] dual A)
    (hr : (TrivSqZeroExt.fstHom K A A).comp r = AlgHom.id K A) :
    Derivation K A A where
  toLinearMap := ((TrivSqZeroExt.sndHom A A).restrictScalars K).comp r.toLinearMap
  map_one_eq_zero' := by simp
  leibniz' a b := by
    have hfst (x : A) : (r x).fst = x := DFunLike.congr_fun hr x
    change (r (a * b)).snd = a * (r b).snd + b * (r a).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, hfst, hfst]
    simp [smul_eq_mul, mul_comm]

include hε hτ in
/-- Every tangent to the identity of an actual affine group extends to
a derivation of its coordinate algebra, with exactly the prescribed value
at the identity. This uses the given geometric group law on all test schemes. -/
theorem exists_derivation :
    ∃ D : Derivation K A A, ∀ x, ε (D x) = (τ x).snd := by
  let D := derivationOfLift K (translationLift K L τ)
    (translationLift_fst K L ε hε τ hτ)
  refine ⟨D, fun x => ?_⟩
  have h := DFunLike.congr_fun (translationLift_augmentation K L ε hε τ) x
  exact congrArg TrivSqZeroExt.snd h

include hε hτ in
/-- A nonzero identity tangent value becomes a unit derivative in a local
coordinate algebra whose augmentation kernel is its maximal ideal. -/
theorem exists_derivation_isUnit [IsLocalRing A]
    (hker : RingHom.ker ε.toRingHom = IsLocalRing.maximalIdeal A)
    (x : A) (hx : (τ x).snd ≠ 0) :
    ∃ D : Derivation K A A, IsUnit (D x) := by
  obtain ⟨D, hD⟩ := exists_derivation K L ε hε τ hτ
  refine ⟨D, ?_⟩
  by_contra hn
  have hm : D x ∈ IsLocalRing.maximalIdeal A := by
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hn
  rw [← hker, RingHom.mem_ker] at hm
  exact hx ((hD x).symm.trans hm)

end SupersingularCurves.Geometry.AffineInvariantDerivation
