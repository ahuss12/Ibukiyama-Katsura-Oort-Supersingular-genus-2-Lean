/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentSections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_app_pullbackTensorPowIso_tensorPowMapIso_tensorPowAdd_tensorSections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_app_pullbackTensorPowIso_tensorPowMapIso_unitSection

/-!
# The coherent action on the actual full section ring

An actual scheme automorphism and a pullback isomorphism of a sheaf act on its
full section ring. The action uses the canonical tensor powers of that single
isomorphism, so multiplication and the unit follow from pullback coherence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FrobeniusFiniteFieldDescent
open CategoryTheory MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.GradedOAlgebra

variable {X : Scheme.{u}} (τ : X ≅ X) (L : X.Modules)
  (eL : (Scheme.Modules.pullback τ.hom).obj L ≅ L)

/-- Tensor powers of one pullback isomorphism, with the canonical coherence. -/
def sectionTensorPowerIso (n : ℕ) :
    (Scheme.Modules.pullback τ.hom).obj (L.tensorPow n) ≅ L.tensorPow n :=
  pullbackTensorPowIso τ.hom L n ≪≫ tensorPowMapIso eL n

variable {S : Type u} [CommRing S] (f : X ⟶ Spec (CommRingCat.of S))
  (R : Type u) [CommRing R] [Algebra S R]
  (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
  (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤))
  (hR : IsSectionRing f L R 𝓡 ι)

/-- The defining bijection of a genuine section ring, as an additive equivalence. -/
def sectionRingDegreeEquiv (n : ℕ) : 𝓡 n ≃+ Γ(L.tensorPow n, ⊤) :=
  { Equiv.ofBijective (ι n) (hR.bijective n) with map_add' := hR.map_add n }

/-- The actual pullback action on each homogeneous component. -/
def sectionRingDegreeAction (n : ℕ) : 𝓡 n →+ 𝓡 n :=
  (sectionRingDegreeEquiv L f R 𝓡 ι hR n).symm.toAddMonoidHom.comp
    ((actionAddHom τ (L.tensorPow n) (sectionTensorPowerIso τ L eL n)).comp
      (sectionRingDegreeEquiv L f R 𝓡 ι hR n).toAddMonoidHom)

theorem sectionRingDegreeAction_formula (n : ℕ) (x : 𝓡 n) :
    ι n (sectionRingDegreeAction τ L eL f R 𝓡 ι hR n x) =
      actionAddHom τ (L.tensorPow n) (sectionTensorPowerIso τ L eL n) (ι n x) :=
  (sectionRingDegreeEquiv L f R 𝓡 ι hR n).apply_symm_apply _

theorem sectionRingDegreeAction_bijective (n : ℕ) :
    Function.Bijective (sectionRingDegreeAction τ L eL f R 𝓡 ι hR n) :=
  (sectionRingDegreeEquiv L f R 𝓡 ι hR n).symm.bijective.comp
    ((actionAddHom_bijective τ (L.tensorPow n) (sectionTensorPowerIso τ L eL n)).comp
      (sectionRingDegreeEquiv L f R 𝓡 ι hR n).bijective)

theorem sectionRingDegreeAction_mul (m n : ℕ) (x : 𝓡 m) (y : 𝓡 n) :
    (sectionRingDegreeAction τ L eL f R 𝓡 ι hR (m + n)
      ⟨(x : R) * y, SetLike.GradedMul.mul_mem x.2 y.2⟩ : R) =
      (sectionRingDegreeAction τ L eL f R 𝓡 ι hR m x : R) *
        sectionRingDegreeAction τ L eL f R 𝓡 ι hR n y := by
  have h : sectionRingDegreeAction τ L eL f R 𝓡 ι hR (m + n)
      ⟨(x : R) * y, SetLike.GradedMul.mul_mem x.2 y.2⟩ =
      ⟨(sectionRingDegreeAction τ L eL f R 𝓡 ι hR m x : R) *
        sectionRingDegreeAction τ L eL f R 𝓡 ι hR n y,
        SetLike.GradedMul.mul_mem
          (sectionRingDegreeAction τ L eL f R 𝓡 ι hR m x).2
          (sectionRingDegreeAction τ L eL f R 𝓡 ι hR n y).2⟩ := by
    apply (hR.bijective (m + n)).1
    rw [sectionRingDegreeAction_formula τ L eL f R 𝓡 ι hR,
      hR.map_mul, hR.map_mul,
      sectionRingDegreeAction_formula τ L eL f R 𝓡 ι hR,
      sectionRingDegreeAction_formula τ L eL f R 𝓡 ι hR]
    simp only [actionAddHom_apply, sectionTensorPowerIso]
    exact app_pullbackTensorPowIso_tensorPowMapIso_tensorPowAdd_tensorSections
      τ.hom L L eL m n (ι m x) (ι n y)
  exact congrArg Subtype.val h

theorem sectionRingDegreeAction_one :
    sectionRingDegreeAction τ L eL f R 𝓡 ι hR 0
      ⟨1, SetLike.GradedOne.one_mem⟩ = ⟨1, SetLike.GradedOne.one_mem⟩ := by
  apply (hR.bijective 0).1
  rw [sectionRingDegreeAction_formula τ L eL f R 𝓡 ι hR, hR.map_one]
  simp only [actionAddHom_apply, sectionTensorPowerIso]
  exact app_pullbackTensorPowIso_tensorPowMapIso_unitSection τ.hom L L eL

/-- Extension of the homogeneous action by the actual direct-sum decomposition. -/
def sectionRingAddAction : R →+ R :=
  (DirectSum.toAddMonoid (fun n =>
    (𝓡 n).subtype.toAddMonoidHom.comp (sectionRingDegreeAction τ L eL f R 𝓡 ι hR n))).comp
      (DirectSum.decomposeAddEquiv 𝓡).toAddMonoidHom

theorem sectionRingAddAction_homogeneous (n : ℕ) (x : 𝓡 n) :
    sectionRingAddAction τ L eL f R 𝓡 ι hR (x : R) =
      (sectionRingDegreeAction τ L eL f R 𝓡 ι hR n x : R) := by
  change DirectSum.toAddMonoid _ (DirectSum.decompose 𝓡 (x : R)) = _
  rw [DirectSum.decompose_coe, DirectSum.toAddMonoid_of]
  rfl

private theorem sectionRingAddAction_one :
    sectionRingAddAction τ L eL f R 𝓡 ι hR 1 = 1 := by
  change sectionRingAddAction τ L eL f R 𝓡 ι hR
    ((⟨1, SetLike.GradedOne.one_mem⟩ : 𝓡 0) : R) = 1
  rw [sectionRingAddAction_homogeneous, sectionRingDegreeAction_one]

private theorem sectionRingAddAction_mul (x y : R) :
    sectionRingAddAction τ L eL f R 𝓡 ι hR (x * y) =
      sectionRingAddAction τ L eL f R 𝓡 ι hR x *
        sectionRingAddAction τ L eL f R 𝓡 ι hR y := by
  refine DirectSum.Decomposition.inductionOn 𝓡 ?_ (fun {m} x' => ?_) ?_ x
  · simp only [zero_mul, map_zero]
  · refine DirectSum.Decomposition.inductionOn 𝓡 ?_ (fun {n} y' => ?_) ?_ y
    · simp only [mul_zero, map_zero]
    · change sectionRingAddAction τ L eL f R 𝓡 ι hR
        ((⟨(x' : R) * y', SetLike.GradedMul.mul_mem x'.2 y'.2⟩ : 𝓡 (m + n)) : R) = _
      rw [sectionRingAddAction_homogeneous, sectionRingAddAction_homogeneous,
        sectionRingAddAction_homogeneous]
      exact sectionRingDegreeAction_mul τ L eL f R 𝓡 ι hR m n x' y'
    · intro y₁ y₂ h₁ h₂
      simp only [mul_add, map_add, h₁, h₂]
  · intro x₁ x₂ h₁ h₂
    simp only [add_mul, map_add, h₁, h₂]

/-- The coherent action on the actual section ring as a ring homomorphism. -/
def sectionRingAction : R →+* R where
  toFun := sectionRingAddAction τ L eL f R 𝓡 ι hR
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := sectionRingAddAction_one τ L eL f R 𝓡 ι hR
  map_mul' := sectionRingAddAction_mul τ L eL f R 𝓡 ι hR

theorem sectionRingAction_homogeneous (n : ℕ) (x : 𝓡 n) :
    sectionRingAction τ L eL f R 𝓡 ι hR (x : R) =
      (sectionRingDegreeAction τ L eL f R 𝓡 ι hR n x : R) :=
  sectionRingAddAction_homogeneous τ L eL f R 𝓡 ι hR n x

/-- The ring action preserves each genuine homogeneous component. -/
theorem sectionRingAction_mem (n : ℕ) (x : R) (hx : x ∈ 𝓡 n) :
    sectionRingAction τ L eL f R 𝓡 ι hR x ∈ 𝓡 n := by
  rw [show x = ((⟨x, hx⟩ : 𝓡 n) : R) from rfl, sectionRingAction_homogeneous]
  exact (sectionRingDegreeAction τ L eL f R 𝓡 ι hR n ⟨x, hx⟩).2

/-- The homogeneous action formula specifies the ring map on actual sections. -/
theorem sectionRingAction_formula (n : ℕ) (x : 𝓡 n) :
    ι n ⟨sectionRingAction τ L eL f R 𝓡 ι hR x,
      sectionRingAction_mem τ L eL f R 𝓡 ι hR n x x.2⟩ =
      actionAddHom τ (L.tensorPow n) (sectionTensorPowerIso τ L eL n) (ι n x) := by
  have hx : (⟨sectionRingAction τ L eL f R 𝓡 ι hR x,
      sectionRingAction_mem τ L eL f R 𝓡 ι hR n x x.2⟩ : 𝓡 n) =
      sectionRingDegreeAction τ L eL f R 𝓡 ι hR n x :=
    Subtype.ext (sectionRingAction_homogeneous τ L eL f R 𝓡 ι hR n x)
  rw [hx, sectionRingDegreeAction_formula τ L eL f R 𝓡 ι hR]

/-- The action on arbitrary elements is componentwise under the genuine grading. -/
theorem sectionRingAction_decompose (x : R) :
    DirectSum.decompose 𝓡 (sectionRingAction τ L eL f R 𝓡 ι hR x) =
      DirectSum.map (sectionRingDegreeAction τ L eL f R 𝓡 ι hR)
        (DirectSum.decompose 𝓡 x) := by
  refine DirectSum.Decomposition.inductionOn 𝓡 ?_ (fun {n} y => ?_) ?_ x
  · simp only [map_zero, DirectSum.decompose_zero]
  · rw [sectionRingAction_homogeneous, DirectSum.decompose_coe,
      DirectSum.decompose_coe, DirectSum.map_of]
  · intro x y hx hy
    simp only [map_add, DirectSum.decompose_add, hx, hy]

/-- The coherent action is injective on the full ring, not just on its degrees. -/
theorem sectionRingAction_injective :
    Function.Injective (sectionRingAction τ L eL f R 𝓡 ι hR) := by
  intro x y hxy
  apply (DirectSum.decompose 𝓡).injective
  apply ((DirectSum.map_injective (sectionRingDegreeAction τ L eL f R 𝓡 ι hR)).mpr
    (fun n => (sectionRingDegreeAction_bijective τ L eL f R 𝓡 ι hR n).1))
  rw [← sectionRingAction_decompose, ← sectionRingAction_decompose, hxy]

/-- An actual automorphism of the scheme and sheaf gives a bijective ring action. -/
theorem sectionRingAction_bijective :
    Function.Bijective (sectionRingAction τ L eL f R 𝓡 ι hR) := by
  refine ⟨sectionRingAction_injective τ L eL f R 𝓡 ι hR, ?_⟩
  intro y
  obtain ⟨a, ha⟩ := ((DirectSum.map_surjective
    (sectionRingDegreeAction τ L eL f R 𝓡 ι hR)).mpr
    (fun n => (sectionRingDegreeAction_bijective τ L eL f R 𝓡 ι hR n).2))
      (DirectSum.decompose 𝓡 y)
  refine ⟨(DirectSum.decompose 𝓡).symm a, ?_⟩
  apply (DirectSum.decompose 𝓡).injective
  rw [sectionRingAction_decompose, Equiv.apply_symm_apply, ha]

section Scalars
variable {K : Type u} [Field K] (c : X ⟶ Spec (CommRingCat.of K))
  (T : Type u) [CommRing T] [Algebra K T]
  (𝓣 : ℕ → Submodule K T) [GradedAlgebra 𝓣]
  (κ : ∀ n : ℕ, 𝓣 n → Γ(L.tensorPow n, ⊤))
  (hT : IsSectionRing c L T 𝓣 κ)
  (σ : K →+* K)
  (hτ : τ.hom ≫ c = c ≫ Spec.map (CommRingCat.ofHom σ))

/-- The grading piece is the actual K-vector space of sections of the tensor power. -/
def sectionRingDegreeLinearEquiv (n : ℕ) :
    letI := sectionsModule (L.tensorPow n) c
    𝓣 n ≃ₗ[K] Γ(L.tensorPow n, ⊤) :=
  letI := sectionsModule (L.tensorPow n) c
  { sectionRingDegreeEquiv L c T 𝓣 κ hT n with map_smul' := hT.map_smul n }

include hτ in
/-- Homogeneous semilinearity is derived from the actual map on the base. -/
theorem sectionRingDegreeAction_smul (n : ℕ) (a : K) (x : 𝓣 n) :
    sectionRingDegreeAction τ L eL c T 𝓣 κ hT n (a • x) =
      σ a • sectionRingDegreeAction τ L eL c T 𝓣 κ hT n x := by
  apply (hT.bijective n).1
  rw [sectionRingDegreeAction_formula τ L eL c T 𝓣 κ hT,
    hT.map_smul, hT.map_smul, sectionRingDegreeAction_formula τ L eL c T 𝓣 κ hT]
  exact actionAddHom_smul τ (L.tensorPow n) (sectionTensorPowerIso τ L eL n)
    c σ hτ a (κ n x)

include hτ in
/-- The coherent ring action is semilinear on every section-ring element. -/
theorem sectionRingAction_smul (a : K) (x : T) :
    sectionRingAction τ L eL c T 𝓣 κ hT (a • x) =
      σ a • sectionRingAction τ L eL c T 𝓣 κ hT x := by
  refine DirectSum.Decomposition.inductionOn 𝓣 ?_ (fun {n} y => ?_) ?_ x
  · simp only [smul_zero, map_zero]
  · change sectionRingAction τ L eL c T 𝓣 κ hT ((a • y : 𝓣 n) : T) = _
    rw [sectionRingAction_homogeneous, sectionRingAction_homogeneous,
      sectionRingDegreeAction_smul τ L eL c T 𝓣 κ hT σ hτ]
    rfl
  · intro x y hx hy
    simp only [smul_add, map_add, hx, hy]

include hτ in
/-- The action on the coefficient field is precisely the given base action. -/
theorem sectionRingAction_algebraMap (a : K) :
    sectionRingAction τ L eL c T 𝓣 κ hT (algebraMap K T a) =
      algebraMap K T (σ a) := by
  simpa only [Algebra.smul_def, mul_one, map_one] using
    sectionRingAction_smul τ L eL c T 𝓣 κ hT σ hτ a (1 : T)

variable (p : ℕ) [Fact p.Prime] [CharP K p]

/-- The actual degreewise action for a Frobenius-square-compatible automorphism. -/
theorem sectionRingDegreeAction_frobeniusSquare_smul
    (hτp : τ.hom ≫ c = c ≫ (SchemeFrobenius.baseMap p K ≫ SchemeFrobenius.baseMap p K))
    (n : ℕ) (a : K) (x : 𝓣 n) :
    sectionRingDegreeAction τ L eL c T 𝓣 κ hT n (a • x) =
      a ^ (p ^ 2) • sectionRingDegreeAction τ L eL c T 𝓣 κ hT n x := by
  have hτ' : τ.hom ≫ c = c ≫
      Spec.map (CommRingCat.ofHom ((frobenius K p).comp (frobenius K p))) := by
    rw [← baseMap_square]
    exact hτp
  simpa only [RingHom.comp_apply, frobenius_def, ← pow_mul, ← pow_two] using
    sectionRingDegreeAction_smul τ L eL c T 𝓣 κ hT
      ((frobenius K p).comp (frobenius K p)) hτ' n a x

/-- The actual full section-ring action has p²-semilinearity. -/
theorem sectionRingAction_frobeniusSquare_smul
    (hτp : τ.hom ≫ c = c ≫ (SchemeFrobenius.baseMap p K ≫ SchemeFrobenius.baseMap p K))
    (a : K) (x : T) :
    sectionRingAction τ L eL c T 𝓣 κ hT (a • x) =
      a ^ (p ^ 2) • sectionRingAction τ L eL c T 𝓣 κ hT x := by
  have hτ' : τ.hom ≫ c = c ≫
      Spec.map (CommRingCat.ofHom ((frobenius K p).comp (frobenius K p))) := by
    rw [← baseMap_square]
    exact hτp
  simpa only [RingHom.comp_apply, frobenius_def, ← pow_mul, ← pow_two] using
    sectionRingAction_smul τ L eL c T 𝓣 κ hT
      ((frobenius K p).comp (frobenius K p)) hτ' a x

end Scalars

end SupersingularCurves.Geometry.FrobeniusFiniteFieldDescent
