/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.AbelianTateModule
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAlgPointsV2
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback

/-! # The genuine geometric Galois representation of an abelian variety -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SupersingularCurves.Geometry.AbelianTate
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open RelativeGroupLaw
open scoped TensorProduct

variable {k K : Type} [Field k] [Field K] [Algebra k K] {g : ℕ}

/-- Geometric field-valued points, with addition from the actual group law. -/
abbrev GeometricPoints (A : AbelianVariety k g) (K : Type) [Field K] [Algebra k K] :=
  (GroupScheme.law A.group).AlgPoints A.groupScheme_law_commutative K

/-- The integral representation acts on actual compatible geometric torsion points. -/
abbrev GeometricIntegral (ℓ : ℕ) (A : AbelianVariety k g) (K : Type)
    [Field K] [Algebra k K] := TateModule ℓ (GeometricPoints A K)

/-- The rational representation is Q_ℓ⊗Z_ℓ of this geometric inverse limit. -/
abbrev GeometricRational (ℓ : ℕ) [Fact ℓ.Prime] (A : AbelianVariety k g) (K : Type)
    [Field K] [Algebra k K] := ModularCurve.RationalTateModule ℓ (GeometricPoints A K)

/-- The Galois action comes from precomposition of actual field-valued scheme points. -/
def integralGaloisRep (ℓ : ℕ) [Fact ℓ.Prime] (A : AbelianVariety k g) :
    (K ≃ₐ[k] K) →* Module.End ℤ_[ℓ] (GeometricIntegral ℓ A K) :=
  TateModule.rep ℓ (GeometricPoints A K) (K ≃ₐ[k] K)

/-- Scalar extension of the genuine integral Galois representation. -/
def rationalGaloisRep (ℓ : ℕ) [Fact ℓ.Prime] (A : AbelianVariety k g) :
    (K ≃ₐ[k] K) →* Module.End ℚ_[ℓ] (GeometricRational ℓ A K) :=
  ModularCurve.rationalGaloisRep ℓ (GeometricPoints A K) (K ≃ₐ[k] K)

/-- Projection to a torsion level is the actual action on the underlying point. -/
theorem integralGaloisRep_apply (ℓ : ℕ) [Fact ℓ.Prime] (A : AbelianVariety k g)
    (σ : K ≃ₐ[k] K) (x : GeometricIntegral ℓ A K) (n : ℕ) :
    (AlgPoints.toPoint ((integralGaloisRep ℓ A σ x).1 n)).1 =
      Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom) ≫
        (AlgPoints.toPoint (x.1 n)).1 := rfl

/-- Base change preserves the actual multiplication-by-n torsion predicate. -/
theorem baseChange_torsion_iff
    {R R' : Type} [CommRing R] [CommRing R']
    {X : Scheme} {c : X ⟶ Spec (CommRingCat.of R)}
    (b : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    (L : RelativeGroupLaw R c) {T : Scheme} (t : T ⟶ Spec (CommRingCat.of R'))
    (n : ℕ) (x : SchemeHomOver t (baseChangeStr b c)) :
    (L.baseChange b).IsTorsionPoint t n x ↔
      L.IsTorsionPoint (t ≫ b) n (baseChangePointToBase b x) := by
  have hn : ∀ m : ℕ,
      baseChangePointToBase b ((L.baseChange b).nsmul t m x) =
        L.nsmul (t ≫ b) m (baseChangePointToBase b x) := by
    intro m
    induction m with
    | zero => exact baseChangePointToBase_one b L t
    | succ m ih =>
      rw [nsmul_succ, nsmul_succ, baseChangePointToBase_mul, ih]
  unfold IsTorsionPoint
  rw [← hn, ← baseChangePointToBase_one b L t]
  exact (baseChangePointEquiv b t).injective.eq_iff.symm

/-- The geometric torsion cardinality is proved on the actual scalar extension. -/
theorem geometric_natCard_torsionBy [IsAlgClosed K]
    (A : AbelianVariety k g) (n : ℕ) (hn : (n : K) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ (GeometricPoints A K) (n : ℤ)) = n ^ (2 * g) := by
  let L := GroupScheme.law A.group
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hprops : AbelianSchemePropertyBundle K (baseChangeStr b A.group.X.hom) :=
    A.abelianSchemePropertyBundle.of_isPullback (IsPullback.of_hasPullback _ _)
  have hs : SmoothOfRelativeDimension g (baseChangeStr b A.group.X.hom) := by
    change SmoothOfRelativeDimension g (pullback.snd _ _)
    infer_instance
  letI := hs
  have hc := RelativeGroupLaw.natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero K
    (baseChangeStr b A.group.X.hom) (L.baseChange b)
    (RelativeGroupLaw.IsCommutative.baseChange b A.groupScheme_law_commutative) hprops g n hn
  let e := (baseChangePointEquiv (f := A.group.X.hom) b (𝟙 _)).subtypeEquiv
    (fun x => baseChange_torsion_iff b L (𝟙 _) n x)
  have he := Nat.card_congr e
  rw [AlgPoints.natCard_torsionBy]
  change Nat.card {x : SchemeHomOver b A.group.X.hom // L.IsTorsionPoint b n x} = _
  convert he.symm.trans hc using 1
  exact congrArg (fun t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) =>
    Nat.card (L.torsionSubset t n)) (Category.id_comp b).symm

/-- Actual geometric Tate modules have the expected finite free rank 2g. -/
theorem geometric_finite_free_finrank [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime]
    (A : AbelianVariety k g) (hℓ : (ℓ : K) ≠ 0) :
    Module.Finite ℤ_[ℓ] (GeometricIntegral ℓ A K) ∧
      Module.Free ℤ_[ℓ] (GeometricIntegral ℓ A K) ∧
      Module.finrank ℤ_[ℓ] (GeometricIntegral ℓ A K) = 2 * g ∧
      Module.finrank ℚ_[ℓ] (GeometricRational ℓ A K) = 2 * g := by
  apply TateModule.finite_free_finrank_eq_of_natCard_torsionBy_pow_eq
  intro n
  exact geometric_natCard_torsionBy A (ℓ ^ n)
    (by simpa only [Nat.cast_pow] using pow_ne_zero n hℓ)

end SupersingularCurves.Geometry.AbelianTate
