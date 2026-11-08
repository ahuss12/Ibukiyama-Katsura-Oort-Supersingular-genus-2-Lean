/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.AbelianVariety
import SupersingularCurves.Geometry.Superspecial

/-!
# Finite kernels and geometric p-torsion

These are ingredients for geometric isogeny invariance of p-rank zero.
The group argument uses the finite p-primary subgroup. The scheme argument
derives finiteness of the kernel on actual K-points from a finite morphism.
The independent Jacobian divisibility theorem is supplied in
`JacobianIsogenyTorsion`; the group and scheme ingredients alone make no
classification assertion.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry

/-- Trivial p-torsion implies trivial p-power torsion. -/
theorem pow_prime_power_eq_one_imp_eq_one
    {G : Type*} [Monoid G] (p : ℕ)
    (ht : ∀ x : G, x ^ p = 1 → x = 1) (n : ℕ)
    (x : G) (hx : x ^ (p ^ n) = 1) : x = 1 := by
  induction n generalizing x with
  | zero => simpa using hx
  | succ n ih =>
    apply ht
    apply ih
    simpa only [pow_succ', pow_mul] using hx

/-- A finite-kernel homomorphism from a p-divisible commutative group to a
group with trivial p-torsion forces trivial p-torsion in the domain.
Finiteness is essential: divisibility alone does not make an arbitrary
homomorphism injective on p-torsion. -/
theorem torsion_trivial_of_finite_kernel_of_pow_surjective
    {G H : Type*} [CommGroup G] [Group H] (p : ℕ)
    (f : G →* H) [Finite f.ker]
    (hdiv : Function.Surjective (fun x : G => x ^ p))
    (ht : ∀ y : H, y ^ p = 1 → y = 1)
    (x : G) (hx : x ^ p = 1) : x = 1 := by
  let T := CommGroup.primaryComponent G p
  have hT : T ≤ f.ker := by
    intro y hy
    obtain ⟨n, hn⟩ := CommGroup.mem_primaryComponent.mp hy
    apply MonoidHom.mem_ker.mpr
    exact pow_prime_power_eq_one_imp_eq_one p ht n (f y)
      (by rw [← map_pow, hn, map_one])
  let : Finite T := Finite.of_injective
    (fun y : T => (⟨y.val, hT y.property⟩ : f.ker))
    (by intro y z h; exact Subtype.ext (congrArg (fun q : f.ker => q.val) h))
  have hsurj : Function.Surjective (fun y : T => y ^ p) := by
    intro y
    obtain ⟨z, hz⟩ := hdiv y.val
    change z ^ p = y.val at hz
    obtain ⟨n, hn⟩ := CommGroup.mem_primaryComponent.mp y.property
    have hzT : z ∈ T := by
      apply CommGroup.mem_primaryComponent.mpr
      refine ⟨n + 1, ?_⟩
      rw [pow_succ', pow_mul, hz, hn]
    exact ⟨⟨z, hzT⟩, Subtype.ext hz⟩
  have hinj := (Finite.injective_iff_surjective).mpr hsurj
  have hxT : x ∈ T := CommGroup.mem_primaryComponent.mpr ⟨1, by simpa using hx⟩
  have he : (⟨x, hxT⟩ : T) ^ p = 1 ^ p := by
    apply Subtype.ext
    simpa using hx
  exact congrArg Subtype.val (hinj he)

/-- Composing a finite-kernel homomorphism with an injective homomorphism
still gives a finite kernel. This will be applied to faithful scalar extension
followed by the geometric isogeny. -/
theorem finite_ker_comp_of_injective
    {G H I : Type*} [Group G] [Group H] [Group I]
    (f : H →* I) (q : G →* H) [Finite f.ker]
    (hq : Function.Injective q) : Finite (f.comp q).ker := by
  apply Finite.of_injective
    (fun P : (f.comp q).ker => (⟨q P.val, P.property⟩ : f.ker))
  intro P Q h
  apply Subtype.ext
  apply hq
  exact congrArg (fun T : f.ker => T.val) h

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

/-- A homomorphism of actual group schemes induces a homomorphism of their
K-valued point groups by composition. -/
def groupSchemePointsHom {K : Type u} [Field K]
    {G H : GroupScheme K} (f : G ⟶ H) :
    (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) →*
      (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X) :=
  IsMonHom.monoidHom f.hom.hom _

/-- Finiteness of the point kernel follows from finite geometric fibres,
using injectivity of the map from K-points to underlying closed points. -/
theorem finite_groupSchemePointsHom_ker {K : Type u} [Field K] [IsAlgClosed K]
    {G H : GroupScheme K} [LocallyOfFiniteType G.X.hom]
    (f : G ⟶ H) [IsFinite (underlyingScheme.map f)] :
    Finite (groupSchemePointsHom f).ker := by
  let c := IsLocalRing.closedPoint K
  let z : H.X.left :=
    (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X).left c
  let S := (underlyingScheme.map f) ⁻¹' ({z} : Set H.X.left)
  have hS : S.Finite := (underlyingScheme.map f).finite_preimage_singleton z
  let : Finite S := hS.to_subtype
  let q : (groupSchemePointsHom f).ker → S := fun P =>
    ⟨P.val.left c, by
      change (underlyingScheme.map f) (P.val.left c) = z
      have h := congrArg (fun Q : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X =>
        Q.left c) (MonoidHom.mem_ker.mp P.property)
      exact h⟩
  apply Finite.of_injective q
  intro P Q h
  apply Subtype.ext
  apply Over.OverMorphism.ext
  apply ext_of_apply_closedPoint_eq G.X.hom P.val.w Q.val.w
  exact congrArg Subtype.val h

/-- The actual product of supersingular elliptic group schemes has no
nonidentity p-torsion points. Product projections jointly detect identity. -/
theorem ellipticProduct_torsion_trivial {K : Type u} [Field K] [IsAlgClosed K]
    {g p : ℕ} [Fact p.Prime] [CharP K p]
    (E : Fin g → AbelianVariety K 1)
    (hE : ∀ i, (E i).IsSupersingularElliptic p)
    (P : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (ellipticProduct E).X)
    (hP : P ^ p = 1) : P = 1 := by
  have hproj (i : Fin g) :
      P ≫ (Pi.π (fun j => (E j).group) i).hom.hom = 1 := by
    let q := groupSchemePointsHom (Pi.π (fun j => (E j).group) i)
    exact hE i (q P) (by rw [← map_pow, hP, map_one])
  apply (isLimitOfPreserves (Grp.forget (Over (Spec (CommRingCat.of K))))
    (limit.isLimit (Discrete.functor (fun i => (E i).group)))).hom_ext
  intro i
  cases i with
  | mk i =>
    change P ≫ (Pi.π (fun j => (E j).group) i).hom.hom =
      1 ≫ (Pi.π (fun j => (E j).group) i).hom.hom
    rw [MonObj.one_comp]
    exact hproj i

end SupersingularCurves.Geometry
