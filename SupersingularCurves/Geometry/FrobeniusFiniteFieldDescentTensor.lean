/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusFiniteFieldDescent

/-!
# Coherent invariant powers of the actual sheaf

The pullback isomorphism for the constructed sheaf induces actual pullback
isomorphisms for every tensor power. Positive powers retain the finite
projective presentation; no further invariance data are assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FrobeniusFiniteFieldDescent
open CategoryTheory MonoidalCategory AlgebraicGeometry

variable {X : Scheme.{u}} (τ : X ≅ X) (M : X.Modules)
variable (eM : (Scheme.Modules.pullback τ.hom).obj M ≅ M)

/-- The given pullback isomorphism induces one on each actual tensor power,
using the unit and tensor maps of the pullback functor. -/
def invariantTensorPowerIso : (n : ℕ) →
    (Scheme.Modules.pullback τ.hom).obj (M.tensorPow n) ≅ M.tensorPow n
  | 0 => (Functor.Monoidal.εIso (Scheme.Modules.pullback τ.hom)).symm
  | n + 1 =>
      (Functor.Monoidal.μIso (Scheme.Modules.pullback τ.hom) (M.tensorPow n) M).symm ≪≫
        (invariantTensorPowerIso n ⊗ᵢ eM)

include eM in
/-- Each positive tensor power is an invariant invertible sheaf with an
actual finite presentation over projective space. -/
theorem invariantTensorPower_properties
    {K : Type u} [Field K] (c : X ⟶ Spec (CommRingCat.of K)) [IsProper c]
    (hM : Scheme.Modules.IsInvertible M) (hfinite : M.FiniteBySections c)
    (n : ℕ) (hn : 0 < n) :
    Scheme.Modules.IsInvertible (M.tensorPow n) ∧
      (M.tensorPow n).FiniteBySections c ∧
      Nonempty ((Scheme.Modules.pullback τ.hom).obj (M.tensorPow n) ≅ M.tensorPow n) :=
  ⟨FrobeniusLineBundle.tensorPower_invertible hM n, hfinite.tensorPow hn,
    ⟨invariantTensorPowerIso τ M eM n⟩⟩

end SupersingularCurves.Geometry.FrobeniusFiniteFieldDescent
