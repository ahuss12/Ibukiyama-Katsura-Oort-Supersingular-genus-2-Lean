/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.NormalDifferentialKernel

/-!
# Frobenius factorization on normal affine coordinate rings

If the image of a ring homomorphism into a normal domain over a perfect
field has zero universal differential, its unique pth roots form an actual
ring homomorphism. This is the local algebra needed for Frobenius descent.
For a homomorphism of algebras, the root map acts on base-field constants
by inverse Frobenius, as required for the relative Frobenius twist.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.Geometry.NormalFrobeniusFactorization

variable (K A : Type*) [Field K] [CommRing A] [IsDomain A]
  [Algebra K A] [IsIntegrallyClosed A]
  (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectRing K p]
  {B : Type*} [CommRing B]

private def root (f : B →+* A) (h : ∀ b, KaehlerDifferential.D K A (f b) = 0)
    (b : B) : A :=
  Classical.choose (NormalDifferentialKernel.exists_pow_eq_of_D_eq_zero K A p (f b) (h b))

private theorem root_pow (f : B →+* A) (h : ∀ b, KaehlerDifferential.D K A (f b) = 0)
    (b : B) : root K A p f h b ^ p = f b :=
  Classical.choose_spec
    (NormalDifferentialKernel.exists_pow_eq_of_D_eq_zero K A p (f b) (h b))

/-- Unique pth roots of the image of a differential-zero homomorphism form
an actual ring homomorphism. -/
def factor (f : B →+* A) (h : ∀ b, KaehlerDifferential.D K A (f b) = 0) : B →+* A := by
  have : CharP A p := charP_of_injective_algebraMap (algebraMap K A).injective p
  exact
    { toFun := root K A p f h
      map_zero' := by
        apply frobenius_inj A p
        change root K A p f h 0 ^ p = 0 ^ p
        rw [root_pow, map_zero, zero_pow (Fact.out : p.Prime).ne_zero]
      map_one' := by
        apply frobenius_inj A p
        change root K A p f h 1 ^ p = 1 ^ p
        rw [root_pow, map_one, one_pow]
      map_add' := by
        intro x y
        apply frobenius_inj A p
        change root K A p f h (x + y) ^ p = (root K A p f h x + root K A p f h y) ^ p
        rw [root_pow, add_pow_char, root_pow, root_pow, map_add]
      map_mul' := by
        intro x y
        apply frobenius_inj A p
        change root K A p f h (x * y) ^ p = (root K A p f h x * root K A p f h y) ^ p
        rw [root_pow, mul_pow, root_pow, root_pow, map_mul] }

/-- The constructed homomorphism really is a pointwise pth root. -/
theorem factor_pow (f : B →+* A) (h : ∀ b, KaehlerDifferential.D K A (f b) = 0)
    (b : B) : factor K A p f h b ^ p = f b :=
  root_pow K A p f h b

/-- Equality with the original homomorphism after composition with Frobenius. -/
theorem frobenius_comp_factor [CharP A p] (f : B →+* A)
    (h : ∀ b, KaehlerDifferential.D K A (f b) = 0) :
    (frobenius A p).comp (factor K A p f h) = f := by
  ext b
  exact factor_pow K A p f h b

/-- The Frobenius factor is unique, which supplies compatibility on overlaps. -/
theorem factor_unique [CharP A p] (f : B →+* A)
    (h : ∀ b, KaehlerDifferential.D K A (f b) = 0)
    (g : B →+* A) (hg : (frobenius A p).comp g = f) :
    g = factor K A p f h := by
  ext b
  apply frobenius_inj A p
  exact (congrArg (fun t : B →+* A => t b) hg).trans
    (factor_pow K A p f h b).symm

/-- Differential zero is equivalent to a unique factorization through
Frobenius on the target coordinate ring. -/
theorem differential_eq_zero_iff_existsUnique_factor [CharP A p] (f : B →+* A) :
    (∀ b, KaehlerDifferential.D K A (f b) = 0) ↔
      ∃! g : B →+* A, (frobenius A p).comp g = f := by
  constructor
  · intro h
    exact ⟨factor K A p f h, frobenius_comp_factor K A p f h,
      fun g hg => factor_unique K A p f h g hg⟩
  · rintro ⟨g, hg, -⟩ b
    apply (NormalDifferentialKernel.D_eq_zero_iff_exists_pow K A p (f b)).mpr
    exact ⟨g b, congrArg (fun t : B →+* A => t b) hg⟩

/-- For an algebra homomorphism, the unique Frobenius factor has precisely
the scalar law dictated by the actual relative Frobenius twist. -/
theorem factor_algebraMap [Algebra K B] (f : B →ₐ[K] A)
    (h : ∀ b, KaehlerDifferential.D K A (f b) = 0) (a : K) :
    factor K A p f.toRingHom h (algebraMap K B a) =
      algebraMap K A ((frobeniusEquiv K p).symm a) := by
  have : CharP A p := charP_of_injective_algebraMap (algebraMap K A).injective p
  apply frobenius_inj A p
  change factor K A p f.toRingHom h (algebraMap K B a) ^ p =
    (algebraMap K A ((frobeniusEquiv K p).symm a)) ^ p
  rw [factor_pow, ← map_pow, frobeniusEquiv_symm_pow_p]
  exact f.commutes a

end SupersingularCurves.Geometry.NormalFrobeniusFactorization
