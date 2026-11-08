/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.EllipticTorsionLiftingEndCotangentImage
import SupersingularCurves.Geometry.EllipticTorsionLiftingEndRestriction
import SupersingularCurves.Geometry.EllipticTorsionLiftingRestrictionBound

/-! # Lifting actual Frobenius-kernel restrictions to global elliptic maps

For a supersingular elliptic model over an algebraically closed algebraic
extension of Fp, basechanged to any algebraically closed extension, every
endomorphism of its Frobenius kernel that extends to its actual p-torsion
comes from a global elliptic group endomorphism. The proof constructs the
global scalar action from the rational quaternion order, proves the local
Fp² constraint by actual F/V naturality, and uses faithful cotangents.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SupersingularCurves.Geometry.WeierstrassGroupModel
open CategoryTheory AlgebraicGeometry PointedCotangent EllipticTorsionRealization
variable {k : Type} [Field k] [IsAlgClosed k] [DecidableEq k]
  {W : WeierstrassCurve k} [W.IsElliptic] (D : WeierstrassGroupModel W)
  (K : Type) [Field K] [IsAlgClosed K] [Algebra k K]
  (p : ℕ) [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
  [Algebra.IsAlgebraic (ZMod p) k] [CharP K p] [Algebra (ZMod p) K]
  (hss : ∀ P : W.toAffine.Point, p • P = 0 → P = 0)

include hss

/-- A Frobenius-fixed scalar of an actual kernel map is realized by a genuine
global group endomorphism, with equality of the actual Hopf restrictions. -/
theorem exists_global_of_kernel_scalar
    (HF : FrobeniusKernelHopf p (D.abelianVariety.baseChange K))
    (φ : HF.Coord →ₐc[K] HF.Coord)
    (hc : HF.cotangentScalar φ ^ (p ^ 2) = HF.cotangentScalar φ) :
    ∃ f : (D.abelianVariety.baseChange K).group ⟶ (D.abelianVariety.baseChange K).group,
      HF.ofGroupHom HF f = φ := by
  obtain ⟨f, hs, hd⟩ := D.exists_baseChanged_endomorphism_of_frobenius_scalar
    K p hss (HF.cotangentScalar φ) hc
  refine ⟨f, HF.cotangentMap_injective ?_⟩
  rw [HF.ofGroupHom_cotangentMap f hs (HF.cotangentScalar φ) hd,
    HF.cotangentMap_eq_scalar]

/-- The actual kernel restriction of any actual p-torsion Hopf endomorphism
lifts globally. Neither a supplied lifting nor its scalar constraint is an
assumption of this theorem. -/
theorem exists_global_of_torsion_extension
    (hV : GroupScheme.verschiebungCotangent p (D.abelianVariety.baseChange K).group
      (D.abelianVariety.baseChange K).groupScheme_law_commutative = 0)
    (HF : FrobeniusKernelHopf p (D.abelianVariety.baseChange K))
    (HT : TorsionLevels.Presentation (D.abelianVariety.baseChange K) p)
    (φ : HF.Coord →ₐc[K] HF.Coord) (ψ : HT.Coord →ₐc[K] HT.Coord)
    (hr : HF.endScheme φ ≫ frobeniusKernelToTorsion p (D.abelianVariety.baseChange K) =
      frobeniusKernelToTorsion p (D.abelianVariety.baseChange K) ≫
        TorsionLevels.Presentation.schemeMap HT HT ψ) :
    ∃ f : (D.abelianVariety.baseChange K).group ⟶ (D.abelianVariety.baseChange K).group,
      HF.ofGroupHom HF f = φ := by
  apply D.exists_global_of_kernel_scalar K p hss HF φ
  exact HF.cotangentScalar_pow_sq_of_torsion_extension p
    (D.abelianVariety.baseChange K) hV HT φ ψ hr

/-- Scheme-level form of the restriction lifting, with the actual inclusion
into the ambient elliptic curve. -/
theorem exists_global_restriction_square_of_torsion_extension
    (hV : GroupScheme.verschiebungCotangent p (D.abelianVariety.baseChange K).group
      (D.abelianVariety.baseChange K).groupScheme_law_commutative = 0)
    (HF : FrobeniusKernelHopf p (D.abelianVariety.baseChange K))
    (HT : TorsionLevels.Presentation (D.abelianVariety.baseChange K) p)
    (φ : HF.Coord →ₐc[K] HF.Coord) (ψ : HT.Coord →ₐc[K] HT.Coord)
    (hr : HF.endScheme φ ≫ frobeniusKernelToTorsion p (D.abelianVariety.baseChange K) =
      frobeniusKernelToTorsion p (D.abelianVariety.baseChange K) ≫
        TorsionLevels.Presentation.schemeMap HT HT ψ) :
    ∃ f : (D.abelianVariety.baseChange K).group ⟶ (D.abelianVariety.baseChange K).group,
      HF.endScheme φ ≫ frobeniusKernelInclusion p (D.abelianVariety.baseChange K) =
        frobeniusKernelInclusion p (D.abelianVariety.baseChange K) ≫ f.hom.hom.left := by
  obtain ⟨f, hf⟩ := D.exists_global_of_torsion_extension K p hss hV HF HT φ ψ hr
  exact ⟨f, by rw [← hf]; exact HF.ofGroupHom_inclusion f⟩

end SupersingularCurves.Geometry.WeierstrassGroupModel
