/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.Superspecial
import SupersingularCurves.Geometry.VerschiebungNaturality

/-!
# Verschiebung vanishing for actual abelian product decompositions

The commutativity and smoothness hypotheses in the general group-scheme
product theorem are discharged from the actual abelian varieties and an
actual product isomorphism. No elliptic vanishing or product-classification
theorem is assumed here: the factor vanishing input remains explicit.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace SupersingularCurves.Geometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj

namespace GroupScheme
variable {K : Type u} [Field K]

/-- The independently supplied commutative group object has a commutative
relative group law on every test scheme. -/
theorem law_commutative (G : GroupScheme K) [IsCommMonObj G.X] :
    (law G).IsCommutative := by
  intro T t x y
  exact relativeGroupLawOfGrpObj_mul_comm_of_isCommMonObj
    (show IsCommMonObj (Over.mk G.X.hom) by change IsCommMonObj G.X; infer_instance) t x y

/-- Commutativity of the actual categorical product is detected by its
projections, on all test-scheme points. -/
theorem law_commutative_product {g : ℕ} (E : Fin g → GroupScheme K)
    [∀ i, IsCommMonObj (E i).X] : (law (∏ᶜ E)).IsCommutative := by
  intro T t x y
  let a : Over.mk t ⟶ (∏ᶜ E).X := schemeHomOverToOverHom x
  let b : Over.mk t ⟶ (∏ᶜ E).X := schemeHomOverToOverHom y
  have h : a * b = b * a := by
    apply (isLimitOfPreserves (Grp.forget (Over (Spec (CommRingCat.of K))))
      (limit.isLimit (Discrete.functor E))).hom_ext
    intro i
    cases i with
    | mk i =>
      change (a * b) ≫ (Pi.π E i).hom.hom = (b * a) ≫ (Pi.π E i).hom.hom
      rw [MonObj.mul_comp, MonObj.mul_comp, mul_comm]
  exact congrArg overHomToSchemeHomOver h

end GroupScheme

namespace AbelianVariety
variable {K : Type u} [Field K] {g : ℕ}

/-- Smoothness of the underlying actual group scheme follows from its
specified relative dimension. -/
instance smooth_group (A : AbelianVariety K g) : Smooth A.group.X.hom :=
  SmoothOfRelativeDimension.smooth g A.group.X.hom

variable (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K]

/-- For an actual product decomposition of an abelian variety, factor
Verschiebung cotangent vanishing implies vanishing on the variety. Product
smoothness is supplied by the decomposition, and product commutativity is
proved from the factors. -/
theorem verschiebungCotangent_zero_of_product_iso
    (A : AbelianVariety K g) (E : Fin g → AbelianVariety K 1)
    (e : A.group ≅ ellipticProduct E)
    (hE : ∀ i, GroupScheme.verschiebungCotangent p (E i).group
      (GroupScheme.law_commutative (E i).group) = 0) :
    GroupScheme.verschiebungCotangent p A.group
      (GroupScheme.law_commutative A.group) = 0 := by
  let P := ellipticProduct E
  let es : A.group.X.left ≅ P.X.left := underlyingScheme.mapIso e
  have hbase : es.inv ≫ A.group.X.hom = P.X.hom := e.inv.hom.hom.w
  have hPsmooth : Smooth P.X.hom := by
    rw [← hbase]
    infer_instance
  let : Smooth (ellipticProduct E).X.hom := hPsmooth
  let : Smooth (∏ᶜ fun i => (E i).group).X.hom := hPsmooth
  apply (GroupScheme.verschiebungCotangent_eq_zero_iff_of_iso p e
    (GroupScheme.law_commutative A.group)
    (GroupScheme.law_commutative_product (fun i => (E i).group))).mpr
  exact GroupScheme.verschiebungCotangent_product_eq_zero p
    (fun i => (E i).group)
    (GroupScheme.law_commutative_product (fun i => (E i).group))
    (fun i => GroupScheme.law_commutative (E i).group) hE

end AbelianVariety
end SupersingularCurves.Geometry
