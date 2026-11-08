/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.Frobenius

/-!
# Descent of a scheme morphism from pth roots of its pulled-back sections

On a reduced source, section roots are unique. They therefore define a
natural sheaf map. Its stalk maps are local because their pth powers are
the original local stalk maps. This constructs the descended scheme map;
it does not assume its existence or any geometric classification.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FrobeniusSectionDescent
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

private theorem pow_injective (R : Type*) [CommRing R] [_root_.IsReduced R]
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) :
    Function.Injective (fun x : R => x ^ p) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply isNilpotent_iff_eq_zero.mp
  refine ⟨p, ?_⟩
  have h := (powCharRingHom R p 1 hp hR).map_sub x y
  simpa only [powCharRingHom_apply, pow_one, hxy, sub_self] using h

private def rootHom {R S : Type*} [CommRing R] [CommRing S] [_root_.IsReduced S]
    (p : ℕ) (hp : p.Prime) (hS : (p : S) = 0) (f : R →+* S)
    (h : ∀ r, ∃ s : S, s ^ p = f r) : R →+* S := by
  let g := fun r => Classical.choose (h r)
  have hg : ∀ r, g r ^ p = f r := fun r => Classical.choose_spec (h r)
  have hi := pow_injective S p hp hS
  exact
    { toFun := g
      map_one' := by apply hi; dsimp only; rw [hg, map_one, one_pow]
      map_mul' := by intro a b; apply hi; dsimp only; rw [hg, mul_pow, hg, hg, map_mul]
      map_zero' := by apply hi; dsimp only; rw [hg, map_zero, zero_pow hp.ne_zero]
      map_add' := by
        intro a b
        apply hi
        dsimp only
        have hadd := (powCharRingHom S p 1 hp hS).map_add (g a) (g b)
        simp only [powCharRingHom_apply, pow_one] at hadd
        rw [hg, hadd, hg, hg, map_add] }

private theorem rootHom_pow {R S : Type*} [CommRing R] [CommRing S] [_root_.IsReduced S]
    (p : ℕ) (hp : p.Prime) (hS : (p : S) = 0) (f : R →+* S)
    (h : ∀ r, ∃ s : S, s ^ p = f r) (r : R) :
    rootHom p hp hS f h r ^ p = f r :=
  Classical.choose_spec (h r)

variable (p : ℕ) (hp : p.Prime) {X Y : Scheme.{u}} [IsReduced X]
  (hX : (p : Γ(X, ⊤)) = 0) (f : X ⟶ Y)
  (h : ∀ (U : Y.Opens) (s : Γ(Y, U)), ∃ t : Γ(X, f ⁻¹ᵁ U), t ^ p = f.app U s)

private def rootPresheafMap : X.toPresheafedSpace ⟶ Y.toPresheafedSpace where
  base := f.base
  c :=
    { app := fun U => by
        change Γ(Y, U.unop) ⟶ Γ(X, f ⁻¹ᵁ U.unop)
        exact CommRingCat.ofHom
          (rootHom p hp (Scheme.natCast_eq_zero_sections hX (f ⁻¹ᵁ U.unop))
            (f.app U.unop).hom (h U.unop))
      naturality := by
        intro U V i
        apply CommRingCat.hom_ext
        ext s
        apply pow_injective Γ(X, f ⁻¹ᵁ V.unop) p hp
          (Scheme.natCast_eq_zero_sections hX _)
        change rootHom p hp (Scheme.natCast_eq_zero_sections hX _)
            (f.app V.unop).hom (h V.unop) (Y.presheaf.map i s) ^ p =
          (X.presheaf.map ((Opens.map f.base).map i.unop).op
            (rootHom p hp (Scheme.natCast_eq_zero_sections hX _)
              (f.app U.unop).hom (h U.unop) s)) ^ p
        rw [rootHom_pow, ← map_pow, rootHom_pow]
        exact congrArg (fun z : Γ(Y, U.unop) ⟶ Γ(X, f ⁻¹ᵁ V.unop) => z s)
          (f.naturality i) }

private theorem root_stalk_pow (x : X) (s : Y.presheaf.stalk (f x)) :
    (PresheafedSpace.Hom.stalkMap (rootPresheafMap p hp hX f h) x s) ^ p =
      f.stalkMap x s := by
  obtain ⟨U, hxU, a, rfl⟩ := Y.presheaf.exists_germ_eq s
  have hg := PresheafedSpace.stalkMap_germ_apply (C := CommRingCat)
    (X := X.toPresheafedSpace) (Y := Y.toPresheafedSpace)
    (rootPresheafMap p hp hX f h) U x hxU a
  erw [hg, Scheme.Hom.germ_stalkMap_apply]
  change (X.presheaf.germ (f ⁻¹ᵁ U) x hxU
    (rootHom p hp (Scheme.natCast_eq_zero_sections hX _)
      (f.app U).hom (h U) a)) ^ p = _
  rw [← map_pow, rootHom_pow]

/-- A genuine morphism of schemes obtained by taking the unique pth root
of each pulled-back section. -/
def factor : X ⟶ Y where
  base := f.base
  c := (rootPresheafMap p hp hX f h).c
  prop x := by
    constructor
    intro s hs
    apply (isUnit_map_iff (f.stalkMap x).hom s).mp
    rw [← root_stalk_pow p hp hX f h x s]
    exact hs.pow p

/-- Actual absolute Frobenius followed by the constructed scheme morphism
is the original morphism. -/
theorem absolute_factor :
    X.frobenius p 1 hp hX ≫ factor p hp hX f h = f := by
  apply Scheme.Hom.ext (f := X.frobenius p 1 hp hX ≫ factor p hp hX f h)
    (g := f) (by rfl)
  intro U
  simp only [eqToHom_refl, op_id]
  erw [X.presheaf.map_id, Category.comp_id]
  apply CommRingCat.hom_ext
  ext s
  change rootHom p hp (Scheme.natCast_eq_zero_sections hX _)
    (f.app U).hom (h U) s ^ p ^ 1 = f.app U s
  rw [pow_one, rootHom_pow]

section Relative
open SchemeFrobenius

variable (q : ℕ) [Fact q.Prime] {K : Type u} [Field K] [CharP K q]
  (c : X ⟶ Spec (CommRingCat.of K))
  (hr : ∀ (U : Y.Opens) (s : Γ(Y, U)), ∃ t : Γ(X, f ⁻¹ᵁ U), t ^ q = f.app U s)

/-- The descended map from the actual relative Frobenius fibre product. -/
def relativeFactor : Twist q c ⟶ Y :=
  projection q c ≫ factor q (Fact.out : q.Prime) (globalChar q c) f hr

/-- Composition with actual relative Frobenius recovers the original map. -/
theorem relative_relativeFactor :
    relative q c ≫ relativeFactor f q c hr = f := by
  rw [relativeFactor, ← Category.assoc, relative_projection]
  exact absolute_factor q (Fact.out : q.Prime) (globalChar q c) f hr

variable [PerfectField K] [Smooth c]

omit [IsReduced X] in
private theorem relative_epi : Epi (relative q c) := by
  have hh := finite_flat_surjective q c
  have : IsFinite (relative q c) := hh.1
  have : Flat (relative q c) := hh.2.1
  have : Surjective (relative q c) := hh.2.2.2
  infer_instance

/-- For a smooth source over a perfect field, the descended scheme map
lies over K. Faithfully flat relative Frobenius detects this equality. -/
theorem relativeFactor_over (d : Y ⟶ Spec (CommRingCat.of K)) (hf : f ≫ d = c) :
    relativeFactor f q c hr ≫ d = toBase q c := by
  have : Epi (relative q c) := relative_epi q c
  apply (cancel_epi (relative q c)).mp
  rw [← Category.assoc, relative_relativeFactor, hf, relative_toBase]

/-- Faithfully flat relative Frobenius also proves uniqueness of the
descended morphism, as an actual scheme morphism. -/
theorem relativeFactor_unique (g : Twist q c ⟶ Y) (hg : relative q c ≫ g = f) :
    g = relativeFactor f q c hr := by
  have : Epi (relative q c) := relative_epi q c
  apply (cancel_epi (relative q c)).mp
  rw [hg, relative_relativeFactor]

end Relative

end SupersingularCurves.Geometry.FrobeniusSectionDescent
