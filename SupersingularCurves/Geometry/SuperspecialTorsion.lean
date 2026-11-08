/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.PointBaseChange
import SupersingularCurves.Geometry.JacobianPoints

/-!
# A geometric obstruction to superspeciality

A product of supersingular elliptic curves has no nonidentity p-torsion
points. This is deduced from its genuine categorical product, not postulated
as an equivalence with superspeciality. Faithful scalar extension then gives
the necessary p-rank-zero condition for geometric superspeciality.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace AbelianVariety
variable {K : Type u} [Field K] {g p : ℕ} [Fact p.Prime] [CharP K p]

/-- Product projections detect p-torsion, using their scheme group laws. -/
theorem IsSuperspecialOver.torsion_trivial [IsAlgClosed K]
    {A : AbelianVariety K g} (h : A.IsSuperspecialOver p)
    (P : A.Points) (hP : P ^ p = 1) : P = 1 := by
  obtain ⟨E, hE, ⟨e⟩⟩ := h
  have hproj (i : Fin g) :
      P ≫ e.hom.hom.hom ≫ (Pi.π (fun j => (E j).group) i).hom.hom = 1 := by
    let q := IsMonHom.monoidHom
      (e.hom ≫ Pi.π (fun j => (E j).group) i).hom.hom
      (Over.mk (𝟙 (Spec (CommRingCat.of K))))
    exact hE i (q P) (by rw [← map_pow, hP, map_one])
  have he : P ≫ e.hom.hom.hom = 1 := by
    apply (isLimitOfPreserves (Grp.forget (Over (Spec (CommRingCat.of K))))
      (limit.isLimit (Discrete.functor (fun i => (E i).group)))).hom_ext
    intro i
    cases i with
    | mk i =>
      change P ≫ e.hom.hom.hom ≫ (Pi.π (fun j => (E j).group) i).hom.hom =
        1 ≫ (Pi.π (fun j => (E j).group) i).hom.hom
      rw [MonObj.one_comp]
      exact hproj i
  have hback := congrArg (fun Q => Q ≫ e.inv.hom.hom) he
  simpa only [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id,
    Grp.id_hom_hom, Category.comp_id, MonObj.one_comp] using hback

/-- Geometric superspeciality forces trivial p-torsion over the ground field. -/
theorem IsSuperspecial.torsion_trivial {A : AbelianVariety K g}
    (h : A.IsSuperspecial p) (P : A.Points) (hP : P ^ p = 1) : P = 1 := by
  let q := A.pointsBaseChange (AlgebraicClosure K)
  apply A.pointsBaseChange_injective (AlgebraicClosure K)
  change q P = q 1
  rw [map_one]
  exact IsSuperspecialOver.torsion_trivial h (q P)
    (by rw [← map_pow, hP, map_one])

theorem IsSuperspecialOver.hasPRankOver_zero [IsAlgClosed K]
    {A : AbelianVariety K g} (h : A.IsSuperspecialOver p) : A.HasPRankOver p 0 :=
  (hasPRankOver_zero_iff A p).mpr h.torsion_trivial

/-- The conclusion refers to independently defined geometric p-rank. -/
theorem IsSuperspecial.hasPRankOver_zero [IsAlgClosed K]
    {A : AbelianVariety K g} (h : A.IsSuperspecial p) : A.HasPRankOver p 0 :=
  (hasPRankOver_zero_iff A p).mpr h.torsion_trivial

/-- A positive-dimensional ordinary abelian variety is not superspecial. -/
theorem IsOrdinaryOver.not_isSuperspecial [IsAlgClosed K]
    {A : AbelianVariety K g} (h : A.IsOrdinaryOver p) (hg : g ≠ 0) :
    ¬ A.IsSuperspecial p := by
  intro hs
  exact hg (hasPRankOver_unique A p h hs.hasPRankOver_zero)

end AbelianVariety
end SupersingularCurves.Geometry
