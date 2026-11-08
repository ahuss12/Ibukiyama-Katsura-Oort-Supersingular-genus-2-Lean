/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import Mathlib

/-!
# Finiteness of rational points over finite fields

Finite-type coordinate rings have only finitely many homomorphisms to a
finite field. A finite affine cover then proves finiteness for every actual
quasicompact finite-type scheme. The application to bounded polarized
abelian varieties is in `ScalarFrobeniusIsogenyModuli`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FiniteFieldPoints
open CategoryTheory AlgebraicGeometry

/-- Finitely many choices for the images of algebra generators determine the map. -/
theorem finite_algHom_of_finiteType
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.FiniteType R A] [Finite B] :
    Finite (A →ₐ[R] B) := by
  classical
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out (R := R) (A := A))
  apply Finite.of_injective (fun f : A →ₐ[R] B => fun x : s => f x)
  intro f g h
  apply AlgHom.ext_of_adjoin_eq_top hs
  intro x hx
  exact congrFun h ⟨x, hx⟩


/-- Ring maps out of a finitely generated ring into a finite ring form a finite type. -/
theorem finite_ringHom_of_finiteType
    {A B : Type u} [CommRing A] [CommRing B]
    [Algebra.FiniteType ℤ A] [Finite B] : Finite (A →+* B) := by
  let := finite_algHom_of_finiteType (R := ℤ) (A := A) (B := B)
  exact Finite.of_injective (fun f : A →+* B => f.toIntAlgHom)
    (fun _ _ h => congrArg AlgHom.toRingHom h)

/-- An actual affine scheme of finite type over a finite field has finitely many field points. -/
theorem finite_affine_points {K : Type u} [Field K] [Finite K]
    {X : Scheme.{u}} [IsAffine X]
    (c : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType c] :
    Finite ((Spec (CommRingCat.of K)) ⟶ X) := by
  let : Finite Γ(Spec (CommRingCat.of K), ⊤) :=
    Finite.of_equiv K (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.toEquiv
  let := c.appTop.hom.toAlgebra
  let : Algebra.FiniteType Γ(Spec (CommRingCat.of K), ⊤) Γ(X, ⊤) := by
    change c.appTop.hom.FiniteType
    simpa only [Scheme.Hom.appLE_eq_app] using
      c.finiteType_appLE (isAffineOpen_top _)
        (show IsAffineOpen (c ⁻¹ᵁ ⊤) by simpa using isAffineOpen_top X) le_rfl
  let : Module.Finite ℤ Γ(Spec (CommRingCat.of K), ⊤) := Module.Finite.of_finite
  let : Algebra.FiniteType ℤ Γ(X, ⊤) :=
    Algebra.FiniteType.trans (R := ℤ) (S := Γ(Spec (CommRingCat.of K), ⊤))
      (A := Γ(X, ⊤)) inferInstance inferInstance
  let := finite_ringHom_of_finiteType (A := Γ(X, ⊤))
    (B := Γ(Spec (CommRingCat.of K), ⊤))
  exact Finite.of_injective (fun f : Spec (CommRingCat.of K) ⟶ X => f.appTop.hom)
    (fun f g h => ext_of_isAffine (CommRingCat.hom_ext h))


/-- Finiteness for actual quasicompact finite-type schemes over a finite field. -/
theorem finite_scheme_points {K : Type u} [Field K] [Finite K]
    {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType c] [QuasiCompact c] :
    Finite ((Spec (CommRingCat.of K)) ⟶ X) := by
  classical
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace c
  let U := X.affineCover.finiteSubcover
  let : ∀ i : U.I₀, Finite (Spec (CommRingCat.of K) ⟶ U.X i) :=
    fun i => finite_affine_points (U.f i ≫ c)
  let F : (Σ i : U.I₀, Spec (CommRingCat.of K) ⟶ U.X i) →
      (Spec (CommRingCat.of K) ⟶ X) := fun z => z.2 ≫ U.f z.1
  apply Finite.of_surjective F
  intro x
  obtain ⟨i, y, hy⟩ := U.exists_eq (x (IsLocalRing.closedPoint K))
  have hx : Set.range x ⊆ Set.range (U.f i) := by
    rintro _ ⟨s, rfl⟩
    have hs : s = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    exact ⟨y, by simpa only [hs] using hy⟩
  exact ⟨⟨i, IsOpenImmersion.lift (U.f i) x hx⟩, IsOpenImmersion.lift_fac _ _ _⟩

end SupersingularCurves.Geometry.FiniteFieldPoints

