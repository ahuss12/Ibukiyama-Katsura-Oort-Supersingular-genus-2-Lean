/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.NormalFrobeniusFactorization
import SupersingularCurves.Geometry.Frobenius

/-!
# Actual relative Frobenius descent on a normal affine scheme

The pth-root ring homomorphism defines a morphism from the actual Frobenius
fibre product. Its scalar law proves that this morphism is over the ground
field, and its composite with actual relative Frobenius is the given map.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.AffineFrobeniusFactorization
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SchemeFrobenius

variable (K A B : Type u) [Field K] [CommRing A] [IsDomain A]
  [CommRing B] [Algebra K A] [Algebra K B] [IsIntegrallyClosed A]
  (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectRing K p]
  (f : B →ₐ[K] A) (h : ∀ b, KaehlerDifferential.D K A (f b) = 0)

/-- The descended map has the actual Frobenius pullback as its source. -/
def factor : Twist p (Spec.map (CommRingCat.ofHom (algebraMap K A))) ⟶
    Spec (CommRingCat.of B) :=
  projection p (Spec.map (CommRingCat.ofHom (algebraMap K A))) ≫
    Spec.map (CommRingCat.ofHom (NormalFrobeniusFactorization.factor K A p f.toRingHom h))

/-- The descended morphism composed with actual relative Frobenius is the
original affine morphism. -/
theorem relative_factor :
    relative p (Spec.map (CommRingCat.ofHom (algebraMap K A))) ≫ factor K A B p f h =
      Spec.map (CommRingCat.ofHom f.toRingHom) := by
  have : CharP A p := charP_of_injective_algebraMap (algebraMap K A).injective p
  have habs : absolute p (Spec.map (CommRingCat.ofHom (algebraMap K A))) =
      Spec.map (CommRingCat.ofHom (frobenius A p)) := by
    rw [absolute, Scheme.frobenius_Spec p 1 (Fact.out : p.Prime)
      (CharP.cast_eq_zero A p), powerRingHom_one]
  rw [factor, ← Category.assoc, relative_projection, habs, ← Spec.map_comp]
  congr 1
  exact congrArg CommRingCat.ofHom (NormalFrobeniusFactorization.frobenius_comp_factor K A p
    f.toRingHom h)

/-- The inverse-Frobenius scalar law makes the descended map a genuine
morphism over K, with the actual pullback structure map. -/
theorem factor_over :
    factor K A B p f h ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) =
      toBase p (Spec.map (CommRingCat.ofHom (algebraMap K A))) := by
  let invBase : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom ((frobeniusEquiv K p).symm : K →+* K))
  have hs :
      Spec.map (CommRingCat.ofHom (NormalFrobeniusFactorization.factor K A p f.toRingHom h)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K B)) =
      Spec.map (CommRingCat.ofHom (algebraMap K A)) ≫ invBase := by
    dsimp only [invBase]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext a
    exact NormalFrobeniusFactorization.factor_algebraMap K A p f h a
  have hi : baseMap p K ≫ invBase = 𝟙 _ := by
    dsimp only [invBase]
    rw [baseMap, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom
      ((frobenius K p).comp ((frobeniusEquiv K p).symm : K →+* K))) = _
    rw [frobenius_comp_frobeniusEquiv_symm]
    exact Spec.map_id _
  rw [factor, Category.assoc, hs, ← Category.assoc]
  change (pullback.fst _ _ ≫ _) ≫ invBase = _
  rw [pullback.condition, Category.assoc, hi, Category.comp_id]
  rfl

end SupersingularCurves.Geometry.AffineFrobeniusFactorization
