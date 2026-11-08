/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import Theorems.Thm_AlgebraicCurve_cartierOperator_existsUnique
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_isCurveOver_ratFunc
import Theorems.Thm_AlgebraicCurve_Place_isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_of_cartierLaws_of_finiteDimensional

/-!
# Cartier operator: a checked FLT reuse interface for the direct paper route

The imported theorems construct Cartier on Kähler differentials of a function
field and prove that it preserves regular differentials. We derive the curve
interface from a transcendental element and a finite extension over K(x).
Thus the main existence theorem below has no assumed curve-instance field.

These are foundations for the Frobenius calculations in Booher--Pries §2.
This file does not identify a particular curve's cohomology, prove a genus,
or assert a Newton-polygon or supersingularity criterion.

The upstream sources are pinned in vendor/flt/upstream-manifest.json.
Compatibility proof edits are recorded separately in vendor/flt/port-manifest.json.
-/

set_option autoImplicit false

noncomputable section

open KaehlerDifferential AlgebraicCurve

namespace SupersingularCurves.Differentials

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The usual three Cartier laws on rational differentials. -/
def CartierLaws (p : ℕ) (C : Ω[F⁄K] →+ Ω[F⁄K]) : Prop :=
  (∀ (f : F) (ω : Ω[F⁄K]), C (f ^ p • ω) = f • C ω) ∧
  (∀ f : F, C (D K F f) = 0) ∧
  (∀ f : F, C (f ^ (p - 1) • D K F f) = D K F f)

section Curve

variable [IsCurveOver K F] [PerfectField K]
variable (p : ℕ) [Fact p.Prime] [CharP K p]
variable (x : F) [FiniteDimensional (IntermediateField.adjoin K {x}) F]

include x in
/-- Direct use of the imported existence-and-uniqueness proof. -/
theorem existsUnique_cartier : ∃! C : Ω[F⁄K] →+ Ω[F⁄K], CartierLaws p C :=
  AlgebraicCurve.cartierOperator_existsUnique (K := K) p x

/-- The canonical Cartier operator, initially constructed using a finite coordinate. -/
def cartier : Ω[F⁄K] →+ Ω[F⁄K] :=
  (existsUnique_cartier (K := K) p x).exists.choose

theorem cartier_laws : CartierLaws p (cartier (K := K) p x) :=
  (existsUnique_cartier (K := K) p x).exists.choose_spec

theorem cartier_pow_smul (f : F) (ω : Ω[F⁄K]) :
    cartier p x (f ^ p • ω) = f • cartier (K := K) p x ω :=
  (cartier_laws (K := K) p x).1 f ω

theorem cartier_exact (f : F) : cartier p x (D K F f) = 0 :=
  (cartier_laws (K := K) p x).2.1 f

theorem cartier_normalization (f : F) :
    cartier p x (f ^ (p - 1) • D K F f) = D K F f :=
  (cartier_laws (K := K) p x).2.2 f

/-- Cartier on all rational differentials is nonzero. This is distinct from
its restriction to regular differentials, which can vanish. -/
theorem rational_cartier_ne_zero : cartier (K := K) p x ≠ 0 := by
  intro hzero
  obtain ⟨t, ht⟩ := AlgebraicCurve.exists_D_ne_zero (K := K) (F := F)
  have h := cartier_normalization (K := K) p x t
  rw [hzero, AddMonoidHom.zero_apply] at h
  exact ht h.symm

/-- Uniqueness removes the auxiliary finite-coordinate choice. -/
theorem cartier_independent_of_coordinate (y : F)
    [FiniteDimensional (IntermediateField.adjoin K {y}) F] :
    cartier (K := K) p x = cartier p y :=
  (existsUnique_cartier (K := K) p x).unique
    (cartier_laws p x) (cartier_laws p y)

/-- The imported local regularity theorem applies to the constructed operator. -/
theorem cartier_regularAt (v : Place K F) {ω : Ω[F⁄K]} (hω : v.IsRegularAt ω) :
    v.IsRegularAt (cartier p x ω) :=
  (AlgebraicCurve.Place.isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_of_cartierLaws_of_finiteDimensional
    p x (cartier p x) (cartier_laws p x).1 (cartier_laws p x).2.1
    (cartier_laws p x).2.2 v ω).1 hω

theorem cartier_mem_regularDifferentials {ω : Ω[F⁄K]}
    (hω : ω ∈ regularDifferentials K F) :
    cartier p x ω ∈ regularDifferentials K F :=
  fun v => cartier_regularAt p x v (hω v)

/-- Cartier restricted to actual globally regular rational differentials. -/
def regularCartier : regularDifferentials K F →+ regularDifferentials K F where
  toFun ω := ⟨cartier p x ω, cartier_mem_regularDifferentials p x ω.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

theorem regularCartier_coe (ω : regularDifferentials K F) :
    (regularCartier p x ω : Ω[F⁄K]) = cartier p x ω := rfl

/-- This is inverse-Frobenius semilinearity, not ordinary K-linearity. -/
theorem regularCartier_pow_smul (c : K) (ω : regularDifferentials K F) :
    regularCartier p x (c ^ p • ω) = c • regularCartier p x ω := by
  apply Subtype.ext
  change cartier p x ((c ^ p) • (ω : Ω[F⁄K])) = c • cartier p x (ω : Ω[F⁄K])
  simpa only [← map_pow, algebraMap_smul] using
    cartier_pow_smul p x (algebraMap K F c) (ω : Ω[F⁄K])

/-- A typed semilinear map, with the inverse Frobenius scalar action explicit. -/
def regularCartierSemilinear :
    regularDifferentials K F →ₛₗ[(frobeniusEquiv K p).symm.toRingHom]
      regularDifferentials K F where
  toFun := regularCartier p x
  map_add' := map_add (regularCartier p x)
  map_smul' c ω := by
    change regularCartier p x (c • ω) =
      (frobeniusEquiv K p).symm c • regularCartier p x ω
    simpa only [frobeniusEquiv_symm_pow_p] using
      regularCartier_pow_smul p x ((frobeniusEquiv K p).symm c) ω

end Curve

/-- An existence theorem from explicit function-field hypotheses.
No `IsCurveOver` assumption, Cartier operator, or preservation law is supplied
by the caller: all are obtained from the imported proofs. -/
theorem existsUnique_regular_cartier_of_functionField [PerfectField K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (x : F) (htr : Transcendental K x)
    (hfd : FiniteDimensional (IntermediateField.adjoin K {x}) F) :
    ∃! C : Ω[F⁄K] →+ Ω[F⁄K], CartierLaws p C ∧
      ∀ ω ∈ regularDifferentials K F, C ω ∈ regularDifferentials K F := by
  let := hfd
  let := AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField htr hfd
  refine ⟨cartier p x, ⟨cartier_laws p x, fun _ hω =>
    cartier_mem_regularDifferentials p x hω⟩, ?_⟩
  intro C hC
  exact (existsUnique_cartier (K := K) p x).unique hC.1 (cartier_laws p x)

/-- A concrete family of fields inhabits the interface, including characteristic p. -/
theorem existsUnique_regular_cartier_ratFunc [PerfectField K]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    ∃! C : Ω[RatFunc K⁄K] →+ Ω[RatFunc K⁄K], CartierLaws p C ∧
      ∀ ω ∈ regularDifferentials K (RatFunc K),
        C ω ∈ regularDifferentials K (RatFunc K) := by
  apply existsUnique_regular_cartier_of_functionField p RatFunc.X RatFunc.transcendental_X
  rw [RatFunc.adjoin_X]
  apply FiniteDimensional.of_surjective
    (Algebra.linearMap (⊤ : IntermediateField K (RatFunc K)) (RatFunc K))
  intro f
  exact ⟨⟨f, trivial⟩, rfl⟩

end SupersingularCurves.Differentials
