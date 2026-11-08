/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.PicardTorsion.Cartier
import Theorems.Thm_AlgebraicCurve_Pic0_range_eq_setOf_cartier_fixed_and_isRegularDiff
import Theorems.Thm_AlgebraicCurve_regularDiffs_eq_regularDifferentials_of_perfectField

/-!
# The logarithmic correspondence for actual divisor-class p-torsion

The earlier injection sends a divisor class represented by `pD = div(f)`
to `df/f`. Here we use the pinned upstream Cartier range theorem to prove
surjectivity onto all regular Cartier-fixed differentials. In particular,
the source is the independently defined divisor-class group, not a
cohomology space or a matrix kernel chosen to make the result true.

This is a statement about divisor classes. The identification with the
points of a representing Jacobian, and the supersingularity and
superspeciality criteria for that abelian variety, are separate tasks.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.PicardTorsion
open AlgebraicCurve KaehlerDifferential SupersingularCurves.Differentials

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
  [PerfectField K] [IsCurveOver K F] [Algebra.EssFiniteType K F]

/-- Relate the order-based regularity predicate in the imported range theorem
to the actual regular-differential submodule used throughout this project. -/
theorem isRegularDiff_of_mem_regular {ω : Ω[F⁄K]}
    (hω : ω ∈ regularDifferentials K F) : IsRegularDiff K F ω := by
  let : ∀ v : Place K F, v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  intro v
  rw [Place.ordDiff_eq_ordDifferential_of_perfectField v ω]
  obtain ⟨f, hf, hωf⟩ := hω v
  rw [Place.ordDifferential, v.differentialCoeff_unique hωf]
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [v.ord_zero]
  · have heq : f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f := by
      rw [Place.mem_iff_adicValuation_le_one, Place.ord, neg_nonneg,
        WithZero.log_le_iff_le_exp (v.adicValuation_ne_zero hf0), WithZero.exp_zero]
    exact heq.mp hf

variable (p : ℕ) [Fact p.Prime] [CharP K p]
  (x : F) [FiniteDimensional (IntermediateField.adjoin K {x}) F]

/-- Every regular Cartier-fixed differential is the logarithmic differential
of a genuine p-torsion divisor class. -/
theorem toRegularFixed_surjective (hC : ConstantsAreBase K F) :
    Function.Surjective (toRegularFixed p x hC) := by
  intro ω
  have hrange := Pic0.range_eq_setOf_cartier_fixed_and_isRegularDiff p x
    (cartier p x) (cartier_laws p x).1 (cartier_laws p x).2.1
    (cartier_laws p x).2.2 (logarithmHom p hC)
    (fun q E g hE hg hord => logarithm_eq p hC q E hE hg hord)
  have hmem : (ω.val : Ω[F⁄K]) ∈ Set.range (logarithmHom p hC) := by
    rw [hrange]
    exact ⟨congrArg Subtype.val ((mem_regularFixed_iff p x ω.val).mp ω.property),
      isRegularDiff_of_mem_regular ω.val.property⟩
  obtain ⟨q, hq⟩ := hmem
  exact ⟨q, Subtype.ext (Subtype.ext hq)⟩

/-- The canonical logarithmic additive equivalence for divisor-class torsion. -/
def logarithmEquiv (hC : ConstantsAreBase K F) :
    Pic0.torsion K F p ≃+ regularFixed (K := K) p x :=
  AddEquiv.ofBijective (toRegularFixed p x hC)
    ⟨toRegularFixed_injective p x hC, toRegularFixed_surjective p x hC⟩

@[simp] theorem logarithmEquiv_apply (hC : ConstantsAreBase K F)
    (q : Pic0.torsion K F p) :
    logarithmEquiv p x hC q = toRegularFixed p x hC q := rfl

/-- Trivial divisor-class p-torsion is equivalent to having no nonzero
Cartier-fixed regular differential. No Jacobian classification is used. -/
theorem torsion_eq_zero_iff_fixed_eq_zero (hC : ConstantsAreBase K F) :
    (∀ q : Pic0.torsion K F p, q = 0) ↔
      ∀ ω : regularDifferentials K F, regularCartier p x ω = ω → ω = 0 := by
  constructor
  · intro ht ω hω
    obtain ⟨q, hq⟩ := toRegularFixed_surjective p x hC
      ⟨ω, (mem_regularFixed_iff p x ω).mpr hω⟩
    rw [ht q, map_zero] at hq
    exact (congrArg (fun z : regularFixed (K := K) p x => z.val) hq).symm
  · intro hω q
    apply regularLogarithm_injective p x hC
    rw [map_zero]
    exact hω _ (regularCartier_logarithm p x hC q)

/-- Nilpotence of regular Cartier kills p-torsion divisor classes. This
does not assert that nilpotence implies superspeciality. -/
theorem torsion_eq_zero_of_regularCartierSquared_zero (hC : ConstantsAreBase K F)
    (hN : ∀ ω : regularDifferentials K F,
      regularCartier p x (regularCartier p x ω) = 0)
    (q : Pic0.torsion K F p) : q = 0 := by
  apply regularLogarithm_injective p x hC
  rw [map_zero]
  have h := hN (regularLogarithm p hC q)
  rwa [regularCartier_logarithm, regularCartier_logarithm] at h

end SupersingularCurves.PicardTorsion
