/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.AbelianMultiplicationDegree
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# An actual degree-one residual Frobenius factor is an isomorphism

For a factorization of actual scheme morphisms `F ≫ W = V`, the proper
residual morphism `W` is finite: its fibres are images of the finite fibres
of `V` under the surjective map `F`. Flatness descends along `F`. If `F` and
`V` have the same positive constant finite-flat rank, then `W` has rank one
and is an actual scheme isomorphism.

Applied to Verschiebung of an abelian variety, this proves that a relative
Frobenius factorization of Verschiebung identifies the double Frobenius
twist with the original variety. It does not by itself construct a product
of elliptic curves.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FiniteFlatFactor

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A proper residual factor of a finite morphism is finite if the first
factor is surjective. This uses scheme finiteness, not only rational points. -/
theorem isFinite [Surjective f] [IsFinite (f ≫ g)] [IsProper g] :
    IsFinite g := by
  have : LocallyQuasiFinite g :=
    LocallyQuasiFinite.of_finite_preimage_singleton g fun z => by
      apply ((f ≫ g).finite_preimage_singleton z).image f |>.subset
      intro y hy
      obtain ⟨x, rfl⟩ := f.surjective y
      exact ⟨x, hy, rfl⟩
  exact IsFinite.of_isProper_of_locallyQuasiFinite g

/-- Equal positive constant ranks in a finite-flat factorization force the
proper residual morphism to be a scheme isomorphism. -/
theorem isIso_of_equal_rank [IsFinite f] [Flat f] [Surjective f]
    [IsFinite (f ≫ g)] [Flat (f ≫ g)] [IsProper g]
    [LocallyOfFinitePresentation g]
    (n : ℕ) (hn : 0 < n) (hf : ∀ y, f.finrank y = n)
    (hfg : ∀ z, (f ≫ g).finrank z = n) : IsIso g := by
  have : IsFinite g := isFinite f g
  have : Flat g := Flat.of_comp_of_flat_of_surjective f g
  apply (Scheme.Hom.isIso_iff_finrank_eq g).2
  funext z
  have h := Scheme.Hom.finrank_comp_of_finrank_eq_const f g n hf z
  rw [hfg z] at h
  exact (Nat.mul_left_cancel hn (by simpa using h)).symm

end FiniteFlatFactor

namespace AbelianVariety
open SchemeFrobenius PerfectFieldVerschiebung

variable {K : Type u} [Field K] [IsAlgClosed K] {g : ℕ}
    (A : AbelianVariety K g) (p : ℕ) [Fact p.Prime] [CharP K p]

local instance : Smooth A.group.X.hom :=
  SmoothOfRelativeDimension.smooth g A.group.X.hom

/-- If actual Verschiebung factors through relative Frobenius
of the actual twist, the remaining factor is an actual scheme isomorphism.
The factorization is the sole extra input; being over the base, finiteness, flatness and degree
one of the factor are proved here. -/
theorem isIso_of_frobenius_factor_verschiebung
    (W : Twist p (toBase p A.group.X.hom) ⟶ A.group.X.left)
    (hfactor : relative p (toBase p A.group.X.hom) ≫ W =
      verschiebung p A.group.X.hom (GroupScheme.law A.group)
        A.groupScheme_law_commutative) : IsIso W := by
  have : Smooth A.group.X.hom := SmoothOfRelativeDimension.smooth g A.group.X.hom
  have : SmoothOfRelativeDimension g (toBase p A.group.X.hom) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
      (IsPullback.of_hasPullback A.group.X.hom (baseMap p K)) A.smooth
  have : Smooth (toBase p A.group.X.hom) :=
    SmoothOfRelativeDimension.smooth g (toBase p A.group.X.hom)
  have : IsLocallyNoetherian A.group.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian A.group.X.hom
  have hF := finite_flat_surjective p (toBase p A.group.X.hom)
  have : IsFinite (relative p (toBase p A.group.X.hom)) := hF.1
  have : Flat (relative p (toBase p A.group.X.hom)) := hF.2.1
  have : Surjective (relative p (toBase p A.group.X.hom)) := hF.2.2.2
  have hW : W ≫ A.group.X.hom = toBase p (toBase p A.group.X.hom) := by
    apply (cancel_epi (relative p (toBase p A.group.X.hom))).mp
    rw [← Category.assoc, hfactor, verschiebung_over, relative_toBase]
  have : IsProper (W ≫ A.group.X.hom) := by
    rw [hW]
    change IsProper (pullback.snd (pullback.snd A.group.X.hom (baseMap p K)) (baseMap p K))
    infer_instance
  have : IsProper W := IsProper.of_comp W A.group.X.hom
  have : IsFinite (relative p (toBase p A.group.X.hom) ≫ W) := by
    rw [hfactor]
    exact A.verschiebung_isFinite p
  have : Flat (relative p (toBase p A.group.X.hom) ≫ W) := by
    rw [hfactor]
    exact A.verschiebung_flat p
  apply FiniteFlatFactor.isIso_of_equal_rank (relative p (toBase p A.group.X.hom)) W
    (p ^ g) (pow_pos (Fact.out : p.Prime).pos g)
  · exact relative_finrank p (toBase p A.group.X.hom) g
  · intro z
    rw [hfactor]
    exact A.verschiebung_finrank p z

end AbelianVariety
end SupersingularCurves.Geometry
