/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.Superspecial
import SupersingularCurves.Geometry.PointBaseChangeIsomorphism
import SupersingularCurves.Geometry.IsogenyBaseChangeIsomorphism

/-!
# Reversing scalar extension along a field isomorphism

When the ground field is already algebraically closed, its map to its
algebraic closure is an isomorphism. The actual scheme pullback equivalence
therefore transports product decompositions back to the original field.
No compatibility of Verschiebung or cotangent spaces is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
universe u

namespace SupersingularCurves.Geometry.AbelianVariety
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- Pullback along an actual field isomorphism preserves the actual product
of group schemes, with its transported group laws. -/
def baseChangeProductIso {g : ℕ} (E : Fin g → AbelianVariety K 1)
    (h : Function.Bijective (algebraMap K L)) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapGrp.obj
        (ellipticProduct E) ≅ ellipticProduct (fun i => (E i).baseChange L) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap K L))
  letI : IsIso (CommRingCat.ofHom (algebraMap K L)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr h
  letI : IsIso f := inferInstanceAs
    (IsIso (Spec.map (CommRingCat.ofHom (algebraMap K L))))
  letI : (Over.map f).Monoidal := Functor.Monoidal.ofChosenFiniteProducts _
  letI : (Over.pullback f).mapGrp.IsRightAdjoint :=
    (Over.mapPullbackAdj f).mapGrp.isRightAdjoint
  exact PreservesProduct.iso (Over.pullback f).mapGrp (fun i => (E i).group)

variable (p : ℕ) [Fact p.Prime] [CharP K p] [CharP L p]
  [IsAlgClosed K] [IsAlgClosed L]

/-- A genuine superspecial product decomposition is preserved by scalar
extension along a field isomorphism, including the elliptic p-torsion condition. -/
theorem IsSuperspecialOver.baseChange_of_bijective {g : ℕ}
    {A : AbelianVariety K g} (hA : A.IsSuperspecialOver p)
    (h : Function.Bijective (algebraMap K L)) :
    (A.baseChange L).IsSuperspecialOver p := by
  obtain ⟨E, hE, ⟨e⟩⟩ := hA
  refine ⟨fun i => (E i).baseChange L, ?_, ?_⟩
  · intro i
    exact ((E i).isSupersingularElliptic_baseChange_iff L h p).mpr (hE i)
  · exact ⟨(Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapGrp.mapIso e ≪≫
      baseChangeProductIso E h⟩

/-- The independent product-isogeny supersingularity predicate is likewise
preserved by scalar extension along a field isomorphism. -/
theorem IsSupersingularOver.baseChange_of_bijective {g : ℕ}
    {A : AbelianVariety K g} (hA : A.IsSupersingularOver p)
    (h : Function.Bijective (algebraMap K L)) :
    (A.baseChange L).IsSupersingularOver p := by
  obtain ⟨E, hE, f, hf⟩ := hA
  refine ⟨fun i => (E i).baseChange L, ?_, ?_⟩
  · intro i
    exact ((E i).isSupersingularElliptic_baseChange_iff L h p).mpr (hE i)
  · let F := (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapGrp
    refine ⟨F.map f ≫ (baseChangeProductIso E h).hom, ?_⟩
    exact ((isIsogeny_baseChange_iff L h f).mpr hf).comp
      (isIsogeny_of_isIso (baseChangeProductIso E h).hom)

variable [Algebra L K]

/-- Successive genuine scalar extensions whose ring maps compose to the
identity recover the original group scheme up to group-scheme isomorphism. -/
def baseChangeTwiceIso {g : ℕ} (A : AbelianVariety K g)
    (h : (algebraMap L K).comp (algebraMap K L) = RingHom.id K) :
    ((A.baseChange L).baseChange K).group ≅ A.group := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let g := Spec.map (CommRingCat.ofHom (algebraMap L K))
  have hfg : g ≫ f = 𝟙 (Spec (CommRingCat.of K)) := by
    change Spec.map (CommRingCat.ofHom (algebraMap L K)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K L)) = _
    rw [← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom ((algebraMap L K).comp (algebraMap K L))) = _
    rw [h]
    exact Spec.map_id _
  let e0 : Over.pullback (g ≫ f) ≅ 𝟭 (Over (Spec (CommRingCat.of K))) :=
    conjugateIsoEquiv (Over.mapPullbackAdj (g ≫ f)) Adjunction.id
      ((Over.mapId _).symm ≪≫ Over.mapCongr _ _ hfg.symm)
  let e : Over.pullback f ⋙ Over.pullback g ≅ 𝟭 (Over (Spec (CommRingCat.of K))) :=
    (Over.pullbackComp g f).symm ≪≫ e0
  exact ((Functor.mapGrpCompIso (F := Over.pullback f) (G := Over.pullback g)).symm ≪≫
    Functor.mapGrpNatIso e ≪≫ Functor.mapGrpIdIso).app A.group

omit [Algebra K L] [Algebra L K] [CharP L p] [IsAlgClosed L] in
/-- Over an already algebraically closed field, the independent geometric
superspecial predicate equals the product-isomorphism predicate over that field.
The proof reverses actual scalar extension; no Cartier criterion is used. -/
theorem isSuperspecial_iff_isSuperspecialOver {g : ℕ} (A : AbelianVariety K g) :
    A.IsSuperspecial p ↔ A.IsSuperspecialOver p := by
  let e : K ≃+* AlgebraicClosure K := RingEquiv.ofBijective
    (algebraMap K (AlgebraicClosure K)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  let : Algebra (AlgebraicClosure K) K := e.symm.toRingHom.toAlgebra
  have hforward : Function.Bijective (algebraMap K (AlgebraicClosure K)) := e.bijective
  have hbackward : Function.Bijective (algebraMap (AlgebraicClosure K) K) := e.symm.bijective
  have hback : (algebraMap (AlgebraicClosure K) K).comp
      (algebraMap K (AlgebraicClosure K)) = RingHom.id K := by
    ext x
    exact e.symm_apply_apply x
  constructor
  · intro hA
    have hA' := IsSuperspecialOver.baseChange_of_bijective p
      (A := A.baseChange (AlgebraicClosure K)) hA hbackward
    exact (isSuperspecialOver_iff_of_iso (baseChangeTwiceIso A hback)).mp hA'
  · intro hA
    exact IsSuperspecialOver.baseChange_of_bijective p hA hforward

omit [Algebra K L] [Algebra L K] [CharP L p] [IsAlgClosed L] in
/-- Over an already algebraically closed field, geometric supersingularity
agrees with the actual product-isogeny condition over that field. -/
theorem isSupersingular_iff_isSupersingularOver {g : ℕ} (A : AbelianVariety K g) :
    A.IsSupersingular p ↔ A.IsSupersingularOver p := by
  let e : K ≃+* AlgebraicClosure K := RingEquiv.ofBijective
    (algebraMap K (AlgebraicClosure K)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  let : Algebra (AlgebraicClosure K) K := e.symm.toRingHom.toAlgebra
  have hforward : Function.Bijective (algebraMap K (AlgebraicClosure K)) := e.bijective
  have hbackward : Function.Bijective (algebraMap (AlgebraicClosure K) K) := e.symm.bijective
  have hback : (algebraMap (AlgebraicClosure K) K).comp
      (algebraMap K (AlgebraicClosure K)) = RingHom.id K := by
    ext x
    exact e.symm_apply_apply x
  constructor
  · intro hA
    have hA' := IsSupersingularOver.baseChange_of_bijective p
      (A := A.baseChange (AlgebraicClosure K)) hA hbackward
    exact (isSupersingularOver_iff_of_iso (baseChangeTwiceIso A hback)).mp hA'
  · intro hA
    exact IsSupersingularOver.baseChange_of_bijective p hA hforward

end SupersingularCurves.Geometry.AbelianVariety
