/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Differentials.Cartier
import SupersingularCurves.Geometry.DifferentialTransport

/-!
# Cartier commutes with actual function-field isomorphisms

Pullback on Kähler differentials conjugates the three defining Cartier laws.
Existence and uniqueness therefore identify the previously constructed
Cartier operators on two isomorphic function fields. Restriction gives the
corresponding equality for regular differentials and their actual transport.
No arbitrary vector-space identification is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace SupersingularCurves.Geometry
open AlgebraicCurve KaehlerDifferential SupersingularCurves.Differentials

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [PerfectField K]
  [IsCurveOver K F] [IsCurveOver K F']
variable (p : ℕ) [Fact p.Prime] [CharP K p]
variable (x : F) [FiniteDimensional (IntermediateField.adjoin K {x}) F]
variable (y : F') [FiniteDimensional (IntermediateField.adjoin K {y}) F']

/-- The actual differential pullback conjugates the existing Cartier map. -/
def cartierConjugate (e : F ≃ₐ[K] F') : Ω[F'⁄K] →+ Ω[F'⁄K] :=
  (Differential.pullbackAlong e.toAlgHom).toAddMonoidHom.comp
    ((cartier (K := K) p x).comp
      (Differential.pullbackAlong e.symm.toAlgHom).toAddMonoidHom)

omit [IsCurveOver K F'] in
theorem cartierConjugate_apply (e : F ≃ₐ[K] F') (ω : Ω[F'⁄K]) :
    cartierConjugate p x e ω =
      Differential.pullbackAlong e.toAlgHom
        (cartier p x (Differential.pullbackAlong e.symm.toAlgHom ω)) := rfl

omit [IsCurveOver K F'] in
/-- Conjugation preserves the defining laws, proved on actual pullbacks. -/
theorem cartierConjugate_laws (e : F ≃ₐ[K] F') :
    CartierLaws p (cartierConjugate p x e) := by
  refine ⟨?_, ?_, ?_⟩
  · intro f ω
    simp only [cartierConjugate_apply, Differential.pullbackAlong_smul,
      map_pow, cartier_pow_smul, AlgEquiv.coe_toAlgHom,
      AlgEquiv.apply_symm_apply]
  · intro f
    simp only [cartierConjugate_apply, Differential.pullbackAlong_D,
      cartier_exact, map_zero]
  · intro f
    simp only [cartierConjugate_apply, Differential.pullbackAlong_smul,
      Differential.pullbackAlong_D, map_pow, cartier_normalization,
      AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]

/-- Uniqueness identifies the conjugated operator with the existing target
operator, even when their chosen finite coordinates differ. -/
theorem cartierConjugate_eq (e : F ≃ₐ[K] F') :
    cartierConjugate p x e = cartier (K := K) p y :=
  (existsUnique_cartier (K := K) p y).unique
    (cartierConjugate_laws p x e) (cartier_laws p y)

/-- Cartier is natural under the actual Kähler pullback of a K-algebra
isomorphism of function fields. -/
theorem cartier_pullbackAlong (e : F ≃ₐ[K] F') (ω : Ω[F⁄K]) :
    cartier p y (Differential.pullbackAlong e.toAlgHom ω) =
      Differential.pullbackAlong e.toAlgHom (cartier p x ω) := by
  rw [← cartierConjugate_eq p x y e, cartierConjugate_apply,
    pullbackAlong_symm_apply]

variable [Algebra.EssFiniteType K F] [Algebra.EssFiniteType K F']
  [∀ v : Place K F, v.DCoordGenerates]
  [∀ v : Place K F', v.DCoordGenerates]

/-- The regular-differential transport commutes with the existing Cartier
operators; the equality is inherited from rational differential pullback. -/
theorem regularDifferentialCongr_cartier (e : F ≃ₐ[K] F')
    (ω : regularDifferentials K F) :
    regularCartier p y (regularDifferentialCongr e ω) =
      regularDifferentialCongr e (regularCartier p x ω) := by
  apply Subtype.ext
  exact cartier_pullbackAlong p x y e ω.val

/-- The same compatibility for the typed inverse-Frobenius semilinear maps. -/
theorem regularDifferentialCongr_cartierSemilinear (e : F ≃ₐ[K] F')
    (ω : regularDifferentials K F) :
    regularCartierSemilinear p y (regularDifferentialCongr e ω) =
      regularDifferentialCongr e (regularCartierSemilinear p x ω) :=
  regularDifferentialCongr_cartier p x y e ω

end SupersingularCurves.Geometry
