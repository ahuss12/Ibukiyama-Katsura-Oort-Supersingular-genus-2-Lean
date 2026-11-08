/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.AbelianVariety

/-! # Faithful field extension of actual global elliptic endomorphisms -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SupersingularCurves.Geometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AbelianVariety
variable {k : Type} [Field k] {g : ℕ} (A : AbelianVariety k g)
variable (K : Type) [Field K] [Algebra k K]

/-- Pull back the actual group-scheme endomorphism along the field extension. -/
def endBaseChange (f : A.group ⟶ A.group) :
    (A.baseChange K).group ⟶ (A.baseChange K).group :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).mapGrp).map f

@[simp] theorem endBaseChange_id : A.endBaseChange K (𝟙 A.group) = 𝟙 _ :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).mapGrp).map_id _

@[simp] theorem endBaseChange_comp (f h : A.group ⟶ A.group) :
    A.endBaseChange K (f ≫ h) = A.endBaseChange K f ≫ A.endBaseChange K h :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).mapGrp).map_comp f h

/-- The pulled-back map commutes with the actual projection to its source model. -/
@[reassoc] theorem endBaseChange_fst (h : A.group ⟶ A.group) :
    (A.endBaseChange K h).hom.hom.left ≫
        pullback.fst A.group.X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      pullback.fst A.group.X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫
        h.hom.hom.left := by
  change ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map h.hom.hom).left ≫ _ = _
  simp only [Over.pullback_map_left, pullback.lift_fst]

/-- Faithful flatness of the field extension gives injectivity on actual
endomorphisms, including nonreduced test-scheme behavior. -/
theorem endBaseChange_injective : Function.Injective (A.endBaseChange K) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hff : (algebraMap k K).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  have hf : Flat f ∧ Surjective f :=
    (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap k K))).mpr hff
  let : Flat f := hf.1
  let : Surjective f := hf.2
  exact ((Over.pullback f).mapGrp).map_injective

end AbelianVariety

namespace EllipticTorsionLiftingEndBaseChange
variable {k K : Type*} [Field k] [Field K] [IsAlgClosed k] [Algebra k K]

/-- Every p²-Frobenius-fixed scalar after extending an algebraically closed
field already comes from a p²-Frobenius-fixed scalar in that field. -/
theorem exists_scalar_preimage (p : ℕ) [Fact p.Prime]
    (c : K) (hc : c ^ (p ^ 2) = c) :
    ∃ a : k, algebraMap k K a = c ∧ a ^ (p ^ 2) = a := by
  let poly : Polynomial k := Polynomial.X ^ (p ^ 2) - Polynomial.X
  have hp : 1 < p ^ 2 := Nat.one_lt_pow (by decide) (Fact.out : p.Prime).one_lt
  have hpoly : poly ≠ 0 := by
    intro he
    have hd := FiniteField.X_pow_card_sub_X_natDegree_eq k hp
    change poly.natDegree = p ^ 2 at hd
    rw [he, Polynomial.natDegree_zero] at hd
    omega
  have hroot : (poly.map (algebraMap k K)).IsRoot c := by
    simpa [poly, Polynomial.IsRoot.def] using sub_eq_zero.mpr hc
  obtain ⟨a, ha⟩ := (IsAlgClosed.splits poly).mem_range_of_isRoot hpoly hroot
  refine ⟨a, ha, ?_⟩
  apply (algebraMap k K).injective
  simpa only [map_pow, ha] using hc

end EllipticTorsionLiftingEndBaseChange
end SupersingularCurves.Geometry
