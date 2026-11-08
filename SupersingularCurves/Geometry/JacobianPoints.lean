/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.Jacobian

/-!
# Torsion of actual abelian-variety points

The point group is induced by the scheme group law. The n-torsion subgroup is
its actual multiplication-by-n kernel. A divisor-class/point equivalence can be
restricted to torsion without assuming a cardinality or geometric criterion.
-/

set_option autoImplicit false
noncomputable section
universe u v

namespace SupersingularCurves.Geometry
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj

namespace AbelianVariety
variable {K : Type u} [Field K] {g : ℕ}

/-- The actual n-torsion in the group of K-valued points. -/
def torsionPoints (A : AbelianVariety K g) (n : ℕ) : Subgroup A.Points where
  carrier := {P | P ^ n = 1}
  one_mem' := one_pow n
  mul_mem' := by
    intro x y hx hy
    change (x * y) ^ n = 1
    rw [mul_pow, hx, hy, one_mul]
  inv_mem' := by
    intro x hx
    change x⁻¹ ^ n = 1
    rw [inv_pow, hx, inv_one]

@[simp] theorem mem_torsionPoints (A : AbelianVariety K g) (n : ℕ) (P : A.Points) :
    P ∈ A.torsionPoints n ↔ P ^ n = 1 := Iff.rfl

/-- The standard geometric p-rank condition, expressed by actual torsion points.
The base is algebraically closed and finiteness is included explicitly. -/
def HasPRankOver [IsAlgClosed K] (A : AbelianVariety K g)
    (p : ℕ) [Fact p.Prime] [CharP K p] (f : ℕ) : Prop :=
  Finite (A.torsionPoints p) ∧ Nat.card (A.torsionPoints p) = p ^ f

/-- An abelian variety is ordinary when its geometric p-rank is its dimension. -/
def IsOrdinaryOver [IsAlgClosed K] (A : AbelianVariety K g)
    (p : ℕ) [Fact p.Prime] [CharP K p] : Prop := A.HasPRankOver p g

theorem hasPRankOver_unique [IsAlgClosed K] (A : AbelianVariety K g)
    (p : ℕ) [Fact p.Prime] [CharP K p] {f h : ℕ}
    (hf : A.HasPRankOver p f) (hh : A.HasPRankOver p h) : f = h := by
  have he : p ^ f = p ^ h := hf.2.symm.trans hh.2
  exact (Nat.pow_right_injective (Fact.out : p.Prime).one_lt) he

theorem hasPRankOver_zero_iff [IsAlgClosed K] (A : AbelianVariety K g)
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    A.HasPRankOver p 0 ↔ ∀ P : A.Points, P ^ p = 1 → P = 1 := by
  constructor
  · rintro ⟨hfin, hcard⟩ P hP
    have hcard' : Nat.card (A.torsionPoints p) = 1 := by simpa using hcard
    have hs := (Nat.card_eq_one_iff_unique.mp hcard').1
    exact congrArg Subtype.val (hs.elim (⟨P, hP⟩ : A.torsionPoints p) 1)
  · intro h
    have hc : Nat.card (A.torsionPoints p) = 1 :=
      Nat.card_eq_one_iff_exists.mpr ⟨1, fun P => Subtype.ext (h P.val P.property)⟩
    exact ⟨Nat.finite_of_card_ne_zero (by rw [hc]; decide), by simpa using hc⟩

end AbelianVariety

namespace Jacobian
variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
  {M : AlgebraicCurve.CurveModel K F}
  {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase}

/-- Interpret the group-compatible Picard point correspondence in the actual
Mathlib group of points of the representing Jacobian. -/
def picardPointsAddEquiv (J : Jacobian M s)
    (pts : Pic0 K F ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) J.designation.toBase)
    (hadd : ∀ x y : Pic0 K F, pts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut M.toBase s)
        J.represents).mul _ (pts x) (pts y)) :
    Pic0 K F ≃+ Additive J.abelianVariety.Points where
  toFun q := Additive.ofMul (schemeHomOverToOverHom (pts q))
  invFun P := pts.symm (overHomToSchemeHomOver P.toMul)
  left_inv q := by
    change pts.symm (overHomToSchemeHomOver (schemeHomOverToOverHom (pts q))) = q
    rw [overHomToSchemeHomOver_schemeHomOverToOverHom, pts.symm_apply_apply]
  right_inv P := by
    apply Additive.toMul.injective
    change schemeHomOverToOverHom (pts (pts.symm (overHomToSchemeHomOver P.toMul))) = P.toMul
    rw [pts.apply_symm_apply]
    exact schemeHomOverToOverHom_overHomToSchemeHomOver _
  map_add' x y := by
    letI : GrpObj (Over.mk J.designation.toBase) :=
      J.represents.grpObj (P := algEquivZeroGroupCut M.toBase s)
    change schemeHomOverToOverHom (pts (x + y)) =
      schemeHomOverToOverHom (pts x) * schemeHomOverToOverHom (pts y)
    rw [hadd]
    exact schemeHomOverToOverHom_overHomToSchemeHomOver _

end Jacobian

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
  {g : ℕ} (A : AbelianVariety K g)

/-- Restrict a group-compatible divisor-class/point identification to n-torsion. -/
def picardTorsionPointsEquiv
    (e : Pic0 K F ≃+ Additive A.Points) (n : ℕ) :
    Pic0.torsion K F n ≃+ Additive (A.torsionPoints n) where
  toFun q := Additive.ofMul ⟨(e q.val).toMul, by
    have h := congrArg e (Pic0.mem_torsion.mp q.property)
    rw [map_zsmul, map_zero, natCast_zsmul] at h
    exact congrArg Additive.toMul h⟩
  invFun P := ⟨e.symm (Additive.ofMul P.toMul.val), by
    apply Pic0.mem_torsion.mpr
    apply e.injective
    rw [map_zsmul, map_zero, e.apply_symm_apply, natCast_zsmul]
    exact congrArg Additive.ofMul P.toMul.property⟩
  left_inv q := Subtype.ext (e.symm_apply_apply q.val)
  right_inv P := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg Additive.toMul (e.apply_symm_apply (Additive.ofMul P.toMul.val))
  map_add' q r := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg Additive.toMul (e.map_add q.val r.val)

/-- Equality of cardinalities concerns independently defined torsion groups. -/
theorem card_torsionPoints_eq_picard
    (e : Pic0 K F ≃+ Additive A.Points) (n : ℕ) :
    Nat.card (A.torsionPoints n) = Nat.card (Pic0.torsion K F n) := by
  exact (Nat.card_congr (picardTorsionPointsEquiv A e n).toEquiv).symm

end SupersingularCurves.Geometry
