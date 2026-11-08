/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusVerschiebungQuotient
import SupersingularCurves.Geometry.FiniteSurjectivePoints
import SupersingularCurves.Geometry.JacobianPoints

/-!
# Geometric p-rank of the actual simultaneous-kernel quotient

The actual finite surjective quotient lifts all rational points. Its
infinitesimal kernel has only the identity rational point, so the quotient
induces a group isomorphism on rational points. Actual relative Frobenius
then identifies these with the original abelian variety's rational points.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open SchemeFrobenius PerfectFieldVerschiebung FrobeniusFactorGroup
open scoped CategoryTheory.MonObj

variable {K : Type u} [Field K] [IsAlgClosed K]
  {p : ℕ} [Fact p.Prime] [CharP K p] {g : ℕ} {A : AbelianVariety K g}
  (D : QuotientData p A)

/-- The actual quotient's rational kernel is trivial because the entire
simultaneous subgroup has one rational point. -/
theorem quotientPoint_kernel_trivial
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (base p A))
    (hx : pointMap D.quotientMap D.over_base x = D.quotientLaw.one (𝟙 _)) :
    x = (law p A).one (𝟙 _) := by
  obtain ⟨e, he⟩ := (D.kernel (𝟙 _) x).mp hx
  let t : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
      (FrobeniusVerschiebungSubgroup.toBase p A) :=
    ⟨e, by change e ≫ inclusion p A ≫ base p A = _; rw [← Category.assoc, he, x.2]⟩
  have ht := congrArg Subtype.val (unique_point p A t)
  apply Subtype.ext
  exact he.symm.trans ((congrArg (fun q => q ≫ inclusion p A) ht).trans
    (identityPoint_inclusion p A))

/-- The rational-point map of the actual quotient group homomorphism. -/
def pointsMap : (sourceAbelianVariety (p := p) (A := A)).Points →* D.abelianVariety.Points :=
  IsMonHom.monoidHom D.quotientHom.hom.hom (Over.mk (𝟙 (Spec (CommRingCat.of K))))

/-- Actual rational-point injectivity comes from the infinitesimal kernel. -/
theorem pointsMap_injective : Function.Injective D.pointsMap := by
  apply (injective_iff_map_eq_one D.pointsMap).mpr
  intro P hP
  let x := overHomToSchemeHomOver P
  have hx : pointMap D.quotientMap D.over_base x = D.quotientLaw.one (𝟙 _) := by
    have h := congrArg overHomToSchemeHomOver hP
    rw [D.quotientLaw.overHomToSchemeHomOver_one] at h
    apply Subtype.ext
    exact congrArg Subtype.val h
  have hh := D.quotientPoint_kernel_trivial x hx
  apply Over.OverMorphism.ext
  have h1 := (law p A).overHomToSchemeHomOver_one (𝟙 (Spec (CommRingCat.of K)))
  exact (congrArg Subtype.val hh).trans (congrArg Subtype.val h1).symm

/-- Finite scheme fibres over the algebraically closed field give actual
rational-point surjectivity, without assuming it from topological surjectivity. -/
theorem pointsMap_surjective : Function.Surjective D.pointsMap := by
  intro P
  obtain ⟨x, hx⟩ := FiniteSurjectivePoints.pointMap_surjective
    (base p A) D.structureMap D.quotientMap D.over_base (overHomToSchemeHomOver P)
  refine ⟨schemeHomOverToOverHom x, ?_⟩
  apply Over.OverMorphism.ext
  exact congrArg Subtype.val hx

/-- The actual quotient induces a genuine group isomorphism on rational points. -/
def pointsMulEquiv : (sourceAbelianVariety (p := p) (A := A)).Points ≃* D.abelianVariety.Points :=
  MulEquiv.ofBijective D.pointsMap ⟨D.pointsMap_injective, D.pointsMap_surjective⟩

/-- The group map on rational points induced by actual relative Frobenius. -/
def frobeniusPointsMap :
    A.Points →* (sourceAbelianVariety (p := p) (A := A)).Points :=
  IsMonHom.monoidHom (relativeFrobeniusHom p A).hom.hom
    (Over.mk (𝟙 (Spec (CommRingCat.of K))))

/-- Relative Frobenius is bijective on rational points over the perfect field. -/
theorem frobeniusPointsMap_bijective :
    Function.Bijective (frobeniusPointsMap (p := p) (A := A)) := by
  constructor
  · intro x y h
    have hh : relativePoint p A.group.X.hom (overHomToSchemeHomOver x) =
        relativePoint p A.group.X.hom (overHomToSchemeHomOver y) := by
      apply Subtype.ext
      exact congrArg Over.Hom.left h
    have hxy := relativePoint_injective p A.group.X.hom hh
    apply Over.OverMorphism.ext
    exact congrArg Subtype.val hxy
  · intro y
    obtain ⟨x, hx⟩ := relativePoint_surjective p A.group.X.hom
      (overHomToSchemeHomOver y)
    refine ⟨schemeHomOverToOverHom x, ?_⟩
    apply Over.OverMorphism.ext
    exact congrArg Subtype.val hx

/-- The original variety and its actual simultaneous-kernel quotient have
canonically isomorphic groups of rational points. -/
def originalPointsMulEquiv : A.Points ≃* D.abelianVariety.Points :=
  (MulEquiv.ofBijective (frobeniusPointsMap (p := p) (A := A))
    (frobeniusPointsMap_bijective (p := p) (A := A))).trans D.pointsMulEquiv

/-- The actual rational-point group isomorphism identifies every torsion group. -/
def torsionPointsEquiv (n : ℕ) :
    A.torsionPoints n ≃ D.abelianVariety.torsionPoints n where
  toFun P := ⟨D.originalPointsMulEquiv P, by
    change (D.originalPointsMulEquiv P) ^ n = 1
    rw [← map_pow, P.property, _root_.map_one]⟩
  invFun Q := ⟨D.originalPointsMulEquiv.symm Q, by
    change (D.originalPointsMulEquiv.symm Q) ^ n = 1
    rw [← map_pow, Q.property, _root_.map_one]⟩
  left_inv P := Subtype.ext (D.originalPointsMulEquiv.left_inv P)
  right_inv Q := Subtype.ext (D.originalPointsMulEquiv.right_inv Q)

/-- The actual quotient preserves geometric p-rank, proved directly on actual
rational torsion points. -/
theorem hasPRankOver_iff (f : ℕ) :
    D.abelianVariety.HasPRankOver p f ↔ A.HasPRankOver p f := by
  let e := D.torsionPointsEquiv p
  constructor
  · rintro ⟨hfinite, hcard⟩
    exact ⟨Finite.of_equiv _ e.symm, (Nat.card_congr e).trans hcard⟩
  · rintro ⟨hfinite, hcard⟩
    exact ⟨Finite.of_equiv _ e, (Nat.card_congr e).symm.trans hcard⟩

/-- In particular, the quotient of a p-rank-zero variety still has p-rank zero. -/
theorem hasPRankOver_zero (h : A.HasPRankOver p 0) :
    D.abelianVariety.HasPRankOver p 0 := (D.hasPRankOver_iff 0).mpr h

end SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData
