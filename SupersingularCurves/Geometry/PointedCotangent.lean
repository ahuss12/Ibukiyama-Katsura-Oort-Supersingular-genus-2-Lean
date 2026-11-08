/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.JacobianCotangent

/-!
# Functorial cotangent maps for pointed schemes

The cotangent space is the actual local maximal ideal modulo its square.
The local-ring equivalence with square-zero points constructs the
contravariant differential of a pointed scheme morphism and proves its
action, uniqueness, identity and composition laws.

This extends the construction used for the representing Jacobian to its
actual Frobenius base change. No arbitrary vector-space isomorphism is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.PointedCotangent
open CategoryTheory AlgebraicGeometry NeronModelInfra
open P2MW.S_AlgebraicGeometry_Scheme_exists_tangentPoints_equiv_linearMap_cotangentSpace

variable {K : Type u} [Field K] {X : Scheme.{u}}
variable (c : X ⟶ Spec (CommRingCat.of K))
  (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)

/-- The actual stalk at the given rational point. -/
abbrev Stalk := X.presheaf.stalk (s.1.base (IsLocalRing.closedPoint K))

instance stalkAlgebra : Algebra K (Stalk c s) :=
  ((X.presheaf.germ ⊤ (s.1.base (IsLocalRing.closedPoint K)) trivial).hom.comp
    (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)).toAlgebra

/-- The local cotangent space m/m², with its base-field scalar action. -/
abbrev Cotangent := IsLocalRing.CotangentSpace (Stalk c s)

abbrev augmentation : Stalk c s →ₐ[K] K :=
  P2mTJ1.πₐ (P2mTJ1.π_algebraMap (fun _ => rfl) s.2)

theorem ker_augmentation :
    RingHom.ker (augmentation c s) = IsLocalRing.maximalIdeal (Stalk c s) :=
  P2mTJ1.ker_πₐ _

def augmentationEquiv :
    Cotangent c s ≃ₗ[K] (RingHom.ker (augmentation c s)).Cotangent :=
  P2mTJ1.cotangentCast (ker_augmentation c s).symm

variable (V : Type u) [AddCommGroup V] [Module K V]
  [Module Kᵐᵒᵖ V] [IsCentralScalar K V]

/-- The local-ring construction of the square-zero point with a specified
cotangent functional. -/
def pointsEquiv : (Cotangent c s →ₗ[K] V) ≃ TangentPoints c s.1 V :=
  ((augmentationEquiv c s).arrowCongr (LinearEquiv.refl K V)).toEquiv.trans
    (P2mTJ1.pointEquiv (fun _ => rfl) (P2mTJ1.π_algebraMap (fun _ => rfl) s.2))

variable {V}
variable {W : Type u} [AddCommGroup W] [Module K W]
  [Module Kᵐᵒᵖ W] [IsCentralScalar K W]

theorem pointsEquiv_map (φ : V →ₗ[K] W) (l : Cotangent c s →ₗ[K] V) :
    pointsEquiv c s W (φ ∘ₗ l) = (pointsEquiv c s V l).map φ :=
  P2mTJ1.pointOf_map (x := c) (pt := s.1) (fun _ => rfl)
    (P2mTJ1.π_algebraMap (fun _ => rfl) s.2)
    φ (l ∘ₗ (augmentationEquiv c s).symm.toLinearMap)

variable {Y : Scheme.{u}} {d : Y ⟶ Spec (CommRingCat.of K)}
  {z : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) d}
variable (f : X ⟶ Y) (hf : f ≫ d = c) (hs : s.1 ≫ f = z.1)

/-- Composition with the actual scheme morphism on square-zero points. -/
def mapPoint (t : TangentPoints c s.1 V) : TangentPoints d z.1 V :=
  ⟨t.1 ≫ f, by rw [Category.assoc, hf, t.2.1],
    by rw [← Category.assoc, t.2.2, hs]⟩

theorem mapPoint_map (φ : V →ₗ[K] W) (t : TangentPoints c s.1 V) :
    mapPoint c s f hf hs (t.map φ) = (mapPoint c s f hf hs t).map φ := by
  apply TangentPoints.ext
  exact Category.assoc _ _ _

local instance cotangentOppositeModule : Module Kᵐᵒᵖ (Cotangent c s) :=
  Module.compHom _ (RingEquiv.toOpposite K).symm.toRingHom

local instance cotangentCentralScalar : IsCentralScalar K (Cotangent c s) :=
  ⟨fun _ _ => rfl⟩

/-- The contravariant differential of the actual pointed scheme morphism. -/
def differential : Cotangent d z →ₗ[K] Cotangent c s :=
  (pointsEquiv d z (Cotangent c s)).symm
    (mapPoint c s f hf hs (pointsEquiv c s (Cotangent c s) LinearMap.id))

theorem differential_action (l : Cotangent c s →ₗ[K] V) :
    pointsEquiv d z V (l ∘ₗ differential c s f hf hs) =
      mapPoint c s f hf hs (pointsEquiv c s V l) := by
  rw [pointsEquiv_map]
  change ((pointsEquiv d z (Cotangent c s))
    ((pointsEquiv d z (Cotangent c s)).symm _)).map l = _
  rw [Equiv.apply_symm_apply, ← mapPoint_map, ← pointsEquiv_map, LinearMap.comp_id]

theorem differential_unique (D : Cotangent d z →ₗ[K] Cotangent c s)
    (hD : pointsEquiv d z (Cotangent c s) D =
      mapPoint c s f hf hs (pointsEquiv c s (Cotangent c s) LinearMap.id)) :
    D = differential c s f hf hs := by
  apply (pointsEquiv d z (Cotangent c s)).injective
  exact hD.trans (Equiv.apply_symm_apply _ _).symm

theorem differential_id :
    differential c s (𝟙 X) (Category.id_comp c) (Category.comp_id s.1) = LinearMap.id := by
  apply (pointsEquiv c s (Cotangent c s)).injective
  rw [differential, Equiv.apply_symm_apply]
  apply TangentPoints.ext
  exact Category.comp_id _

variable {Z : Scheme.{u}} {e : Z ⟶ Spec (CommRingCat.of K)}
  {w : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) e}

theorem differential_comp (g : Y ⟶ Z) (hg : g ≫ e = d) (hz : z.1 ≫ g = w.1) :
    differential c s (f ≫ g) (by rw [Category.assoc, hg, hf])
        (by rw [← Category.assoc, hs, hz]) =
      differential c s f hf hs ∘ₗ differential d z g hg hz := by
  apply (pointsEquiv e w (Cotangent c s)).injective
  rw [differential_action]
  conv_lhs => rw [differential, Equiv.apply_symm_apply]
  rw [differential, Equiv.apply_symm_apply]
  apply TangentPoints.ext
  exact (Category.assoc _ _ _).symm

end SupersingularCurves.Geometry.PointedCotangent
