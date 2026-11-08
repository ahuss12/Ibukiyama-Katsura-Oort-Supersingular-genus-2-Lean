/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.PointedCotangent

/-!
# Finite schemes with a unique geometric point

For a finite scheme over an algebraically closed field, every underlying
point is supplied by a rational point. Uniqueness of the rational point
therefore makes the space a singleton, even if the scheme is nonreduced.
The actual global germ map then identifies its coordinate ring with its
actual local stalk, and that stalk is finite over the ground field.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FiniteGeometricPoints
open CategoryTheory AlgebraicGeometry NeronModelInfra

variable {K : Type u} [Field K] {X : Scheme.{u}}
variable (c : X ⟶ Spec (CommRingCat.of K))

/-- A finite scheme over a field has discrete underlying topology. -/
theorem discreteTopology [IsFinite c] : DiscreteTopology X := by
  let : IsLocallyArtinian X := IsLocallyArtinian.of_locallyQuasiFinite c
  infer_instance

/-- Every underlying point of a finite scheme over an algebraically closed
field is the image of an actual rational point. -/
theorem exists_rationalPoint [IsAlgClosed K] [IsFinite c] (x : X) :
    ∃ s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c,
      s.1 (IsLocalRing.closedPoint K) = x := by
  let := discreteTopology c
  exact ⟨⟨pointOfClosedPoint c x (isClosed_singleton),
    pointOfClosedPoint_comp c x (isClosed_singleton)⟩,
    pointOfClosedPoint_apply c x (isClosed_singleton) _⟩

/-- The scheme may retain nilpotents: only its underlying space is shown
to be a singleton from uniqueness of its rational point. -/
theorem subsingleton_of_unique_point [IsAlgClosed K] [IsFinite c]
    (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
    (h : ∀ q : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c, q = s) :
    Subsingleton X := by
  constructor
  intro x y
  obtain ⟨q, hq⟩ := exists_rationalPoint c x
  obtain ⟨r, hr⟩ := exists_rationalPoint c y
  rw [h q] at hq
  rw [h r] at hr
  exact hq.symm.trans hr

variable (X) in
/-- On an actual one-point scheme, the global germ map is bijective. -/
theorem globalGerm_bijective [Subsingleton X] (x : X) :
    Function.Bijective (X.presheaf.germ ⊤ x trivial).hom := by
  have htop (U : X.Opens) (hx : x ∈ U) : U = ⊤ := by
    apply top_unique
    intro y _
    simpa only [Subsingleton.elim y x] using hx
  constructor
  · intro a b hab
    obtain ⟨U, hx, i, j, h⟩ := X.presheaf.germ_eq (U := ⊤) (V := ⊤) x trivial trivial a b hab
    have hU := htop U hx
    subst U
    have hi : i = 𝟙 ⊤ := Subsingleton.elim _ _
    have hj : j = 𝟙 ⊤ := Subsingleton.elim _ _
    simpa [hi, hj] using h
  · intro a
    obtain ⟨U, hx, b, hb⟩ := X.presheaf.exists_germ_eq a
    have hU := htop U hx
    subst U
    exact ⟨b, hb⟩

variable (X) in
/-- The categorical form of the actual global-germ isomorphism. -/
theorem globalGerm_isIso [Subsingleton X] (x : X) :
    IsIso (X.presheaf.germ ⊤ x trivial) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (globalGerm_bijective X x)

/-- The ground-field algebra structure on actual global sections. -/
@[instance_reducible] def sectionAlgebra : Algebra K Γ(X, ⊤) :=
  (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra

/-- Finiteness of the actual coordinate algebra follows from finite
scheme structure, with its natural ground-field algebra structure. -/
theorem finite_globalSections [IsFinite c] :
    letI := sectionAlgebra c
    Module.Finite K Γ(X, ⊤) := by
  let := sectionAlgebra c
  change (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).Finite
  apply RingHom.Finite.comp c.finite_appTop
  apply RingHom.Finite.of_surjective
  exact (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.surjective

variable (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)

/-- The actual global germ as a K-algebra homomorphism into the actual
stalk used by the pointed cotangent construction. -/
def globalGermAlgHom :
    letI := sectionAlgebra c
    Γ(X, ⊤) →ₐ[K] PointedCotangent.Stalk c s := by
  let := sectionAlgebra c
  exact {
    (X.presheaf.germ ⊤ (s.1 (IsLocalRing.closedPoint K)) trivial).hom with
    commutes' := fun _ => rfl }

/-- Actual coordinate algebra and actual cotangent stalk are identified
by the natural germ, not by an arbitrary vector-space equivalence. -/
def globalGermAlgEquiv [Subsingleton X] :
    letI := sectionAlgebra c
    Γ(X, ⊤) ≃ₐ[K] PointedCotangent.Stalk c s := by
  let := sectionAlgebra c
  exact AlgEquiv.ofBijective (globalGermAlgHom c s)
    (globalGerm_bijective X (s.1 (IsLocalRing.closedPoint K)))

/-- Finiteness of the actual local ring at the unique point. -/
theorem finite_stalk [IsFinite c] [Subsingleton X] :
    Module.Finite K (PointedCotangent.Stalk c s) := by
  let := sectionAlgebra c
  let := finite_globalSections c
  exact Module.Finite.of_surjective (globalGermAlgHom c s).toLinearMap
    (globalGerm_bijective X (s.1 (IsLocalRing.closedPoint K))).surjective

/-- A finite scheme over an algebraically closed field with one rational
point has a finite actual local algebra at that point. -/
theorem finite_stalk_of_unique_point [IsAlgClosed K] [IsFinite c]
    (h : ∀ q : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c, q = s) :
    Module.Finite K (PointedCotangent.Stalk c s) := by
  let := subsingleton_of_unique_point c s h
  exact finite_stalk c s

end SupersingularCurves.Geometry.FiniteGeometricPoints
