/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.SectionPowerRoots
import SupersingularCurves.Geometry.NormalDifferentialKernel
import SupersingularCurves.Geometry.FrobeniusSectionDescent
import Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk

/-!
# Differential-zero sections on smooth schemes

Smoothness over a field supplies normal domain stalks. Over a perfect field
in characteristic p, the field and normal-domain differential-kernel theorems
produce roots in those stalks. The structure-sheaf gluing theorem then gives
roots on every open, including nonaffine and empty opens.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.SmoothDifferentialRoots
open CategoryTheory AlgebraicGeometry

variable {K : Type u} [Field K] {X : Scheme.{u}}
  (c : X ⟶ Spec (CommRingCat.of K))

/-- The ground-field algebra structure on the actual local ring at any point. -/
@[instance_reducible] def stalkAlgebra (x : X) : Algebra K (X.presheaf.stalk x) :=
  ((X.presheaf.germ ⊤ x trivial).hom.comp
    (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)).toAlgebra

/-- Smoothness supplies both hypotheses of the normal-domain kernel theorem
at each actual stalk, with no irreducibility assumption on the scheme. -/
theorem normal_stalk [Smooth c] (x : X) :
    IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) := by
  let e := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  have : IsDomain Γ(Spec (CommRingCat.of K), ⊤) := e.toMulEquiv.isDomain
  have : IsIntegrallyClosed Γ(Spec (CommRingCat.of K), ⊤) :=
    IsIntegrallyClosed.of_equiv e.symm
  exact Smooth.isDomain_and_isIntegrallyClosed_stalk c x

variable (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectRing K p]

/-- Zero universal differential in every actual stalk gives a unique global
pth root of a section on any open of a smooth scheme. -/
theorem existsUnique_pow_eq_of_stalk_D_eq_zero [Smooth c]
    (U : X.Opens) (s : Γ(X, U))
    (h : ∀ (x : X) (hx : x ∈ U), letI := stalkAlgebra c x
      KaehlerDifferential.D K (X.presheaf.stalk x) (X.presheaf.germ U x hx s) = 0) :
    ∃! r : Γ(X, U), r ^ p = s := by
  have (x : X) : IsDomain (X.presheaf.stalk x) := (normal_stalk c x).1
  have : IsReduced X := isReduced_of_isReduced_stalk X
  have hX : (p : Γ(X, ⊤)) = 0 := by
    have hchar := congrArg c.appTop
      (Scheme.natCast_eq_zero_ΓSpec (CharP.cast_eq_zero K p))
    simpa using hchar
  apply SectionPowerRoots.existsUnique_pow_eq X p hX U s
  intro x hx
  let := stalkAlgebra c x
  have : IsIntegrallyClosed (X.presheaf.stalk x) := (normal_stalk c x).2
  exact NormalDifferentialKernel.exists_pow_eq_of_D_eq_zero K (X.presheaf.stalk x) p
    (X.presheaf.germ U x hx s) (h x hx)

/-- A pullback section with zero stalkwise differential has a pth root on
its entire actual inverse-image open. -/
theorem exists_pow_eq_app_of_stalk_D_eq_zero [Smooth c]
    {Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (s : Γ(Y, U))
    (h : ∀ (x : X) (hx : x ∈ f ⁻¹ᵁ U), letI := stalkAlgebra c x
      KaehlerDifferential.D K (X.presheaf.stalk x)
        (X.presheaf.germ (f ⁻¹ᵁ U) x hx (f.app U s)) = 0) :
    ∃ r : Γ(X, f ⁻¹ᵁ U), r ^ p = f.app U s :=
  (existsUnique_pow_eq_of_stalk_D_eq_zero c p (f ⁻¹ᵁ U) (f.app U s) h).exists

omit [PerfectRing K p] in
/-- Stalkwise vanishing of the actual universal differential factors an
actual morphism uniquely through relative Frobenius, as a morphism over K. -/
theorem existsUnique_relative_factor_of_stalk_D_eq_zero [PerfectField K] [Smooth c]
    {Y : Scheme.{u}} (f : X ⟶ Y) (d : Y ⟶ Spec (CommRingCat.of K)) (hf : f ≫ d = c)
    (h : ∀ (U : Y.Opens) (s : Γ(Y, U)) (x : X) (hx : x ∈ f ⁻¹ᵁ U),
      letI := stalkAlgebra c x
      KaehlerDifferential.D K (X.presheaf.stalk x)
        (X.presheaf.germ (f ⁻¹ᵁ U) x hx (f.app U s)) = 0) :
    ∃! g : SchemeFrobenius.Twist p c ⟶ Y,
      SchemeFrobenius.relative p c ≫ g = f ∧
        g ≫ d = SchemeFrobenius.toBase p c := by
  have (x : X) : IsDomain (X.presheaf.stalk x) := (normal_stalk c x).1
  have : IsReduced X := isReduced_of_isReduced_stalk X
  have hr : ∀ (U : Y.Opens) (s : Γ(Y, U)),
      ∃ t : Γ(X, f ⁻¹ᵁ U), t ^ p = f.app U s :=
    fun U s => exists_pow_eq_app_of_stalk_D_eq_zero c p f U s (h U s)
  refine ⟨FrobeniusSectionDescent.relativeFactor f p c hr, ⟨?_, ?_⟩, ?_⟩
  · exact FrobeniusSectionDescent.relative_relativeFactor f p c hr
  · exact FrobeniusSectionDescent.relativeFactor_over f p c hr d hf
  · intro g hg
    exact FrobeniusSectionDescent.relativeFactor_unique f p c hr g hg.1

omit [PerfectRing K p] in
/-- Equivalent input phrased directly on all local-ring maps of the given
scheme morphism, rather than on germs of pulled-back sections. -/
theorem existsUnique_relative_factor_of_stalkMap_D_eq_zero [PerfectField K] [Smooth c]
    {Y : Scheme.{u}} (f : X ⟶ Y) (d : Y ⟶ Spec (CommRingCat.of K)) (hf : f ≫ d = c)
    (h : ∀ (x : X), letI := stalkAlgebra c x
      ∀ b : Y.presheaf.stalk (f x),
        KaehlerDifferential.D K (X.presheaf.stalk x) (f.stalkMap x b) = 0) :
    ∃! g : SchemeFrobenius.Twist p c ⟶ Y,
      SchemeFrobenius.relative p c ≫ g = f ∧
        g ≫ d = SchemeFrobenius.toBase p c := by
  apply existsUnique_relative_factor_of_stalk_D_eq_zero c p f d hf
  intro U s x hx
  rw [← Scheme.Hom.germ_stalkMap_apply]
  exact h x (Y.presheaf.germ U (f x) hx s)

end SupersingularCurves.Geometry.SmoothDifferentialRoots
