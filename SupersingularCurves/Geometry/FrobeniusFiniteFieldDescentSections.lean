/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.Frobenius
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection

/-!
# The genuine semilinear action on global sections

An automorphism of a scheme together with an actual pullback isomorphism of
sheaves induces an additive automorphism of global sections. Its action on
scalars is determined by the automorphism of the base, and therefore is the
p²-power action for an automorphism over the square of Frobenius.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FrobeniusFiniteFieldDescent
open CategoryTheory AlgebraicGeometry

variable {X : Scheme.{u}} (τ : X ≅ X) (M : X.Modules)

/-- Pullback along an actual scheme isomorphism is an equivalence. -/
def pullbackEquivalence : X.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.pullback τ.hom) (Scheme.Modules.pullback τ.inv)
    (Scheme.Modules.pullbackComp τ.inv τ.hom ≪≫
      Scheme.Modules.pullbackCongr τ.inv_hom_id ≪≫ Scheme.Modules.pullbackId X).symm
    (Scheme.Modules.pullbackComp τ.hom τ.inv ≪≫
      Scheme.Modules.pullbackCongr τ.hom_inv_id ≪≫ Scheme.Modules.pullbackId X)

variable (eM : (Scheme.Modules.pullback τ.hom).obj M ≅ M)

/-- The actual map of sheaves adjoint to the chosen pullback isomorphism. -/
def actionSheafHom : M ⟶ (Scheme.Modules.pushforward τ.hom).obj M :=
  (Scheme.Modules.pullbackPushforwardAdjunction τ.hom).homEquiv _ _ eM.hom

/-- The action on genuine global sections is pullback followed by `eM`. -/
def actionAddHom : Γ(M, ⊤) →+ Γ(M, ⊤) :=
  ((actionSheafHom τ M eM).app ⊤).hom

theorem actionAddHom_apply (s : Γ(M, ⊤)) :
    actionAddHom τ M eM s =
      eM.hom.app ⊤ (Scheme.Modules.pullbackLocalSection τ.hom s) := rfl

/-- This is an actual additive automorphism, with no injectivity assumption. -/
theorem actionAddHom_bijective : Function.Bijective (actionAddHom τ M eM) := by
  let : (Scheme.Modules.pullback τ.hom).IsEquivalence :=
    (pullbackEquivalence τ).isEquivalence_functor
  have : IsIso (actionSheafHom τ M eM) := by
    unfold actionSheafHom
    rw [Adjunction.homEquiv_unit]
    infer_instance
  exact ConcreteCategory.bijective_of_isIso ((actionSheafHom τ M eM).app ⊤)

theorem actionAddHom_injective : Function.Injective (actionAddHom τ M eM) :=
  (actionAddHom_bijective τ M eM).1

variable {K : Type u} [Field K] (c : X ⟶ Spec (CommRingCat.of K))

/-- The scalar map from the actual structure morphism of the scheme. -/
def scalarHom : K →+* Γ(X, ⊤) :=
  c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

/-- The K-module of global sections obtained from the actual structure map. -/
@[instance_reducible] def sectionsModule : Module K Γ(M, ⊤) :=
  Module.compHom Γ(M, ⊤) (scalarHom c)

theorem actionAddHom_smul_sections (r : Γ(X, ⊤)) (s : Γ(M, ⊤)) :
    actionAddHom τ M eM (r • s) = τ.hom.appTop r • actionAddHom τ M eM s := by
  rw [actionAddHom_apply, Scheme.Modules.pullbackLocalSection_smul,
    Scheme.Modules.Hom.app_smul, actionAddHom_apply]
  rfl

/-- Compatibility with the base morphism determines the scalar action. -/
theorem appTop_scalarHom (σ : K →+* K)
    (hτ : τ.hom ≫ c = c ≫ Spec.map (CommRingCat.ofHom σ)) (a : K) :
    τ.hom.appTop (scalarHom c a) = scalarHom c (σ a) := by
  have h := congrArg Scheme.Hom.appTop hτ
  simp only [Scheme.Hom.comp_appTop] at h
  change (c.appTop ≫ τ.hom.appTop).hom
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a) = _
  rw [h]
  change ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
      (Spec.map (CommRingCat.ofHom σ)).appTop ≫ c.appTop).hom a = _
  rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- The sheaf action is semilinear for its genuine action on the base. -/
theorem actionAddHom_smul (σ : K →+* K)
    (hτ : τ.hom ≫ c = c ≫ Spec.map (CommRingCat.ofHom σ))
    (a : K) (s : Γ(M, ⊤)) :
    letI := sectionsModule M c
    actionAddHom τ M eM (a • s) = σ a • actionAddHom τ M eM s := by
  let := sectionsModule M c
  change actionAddHom τ M eM (scalarHom c a • s) =
    scalarHom c (σ a) • actionAddHom τ M eM s
  rw [actionAddHom_smul_sections, appTop_scalarHom τ c σ hτ]

variable (p : ℕ) [Fact p.Prime] [CharP K p]

/-- The square Frobenius base map is the spectrum map of p² powers. -/
theorem baseMap_square :
    SchemeFrobenius.baseMap p K ≫ SchemeFrobenius.baseMap p K =
      Spec.map (CommRingCat.ofHom ((frobenius K p).comp (frobenius K p))) := by
  rw [SchemeFrobenius.baseMap, ← Spec.map_comp]
  rfl

/-- A genuine Frobenius-square-compatible sheaf automorphism acts by p²
semilinearity on its actual global sections. -/
theorem actionAddHom_frobeniusSquare_smul
    (hτ : τ.hom ≫ c =
      c ≫ (SchemeFrobenius.baseMap p K ≫ SchemeFrobenius.baseMap p K))
    (a : K) (s : Γ(M, ⊤)) :
    letI := sectionsModule M c
    actionAddHom τ M eM (a • s) = a ^ (p ^ 2) • actionAddHom τ M eM s := by
  have hτ' : τ.hom ≫ c =
      c ≫ Spec.map (CommRingCat.ofHom ((frobenius K p).comp (frobenius K p))) := by
    rw [← baseMap_square]
    exact hτ
  simpa only [RingHom.comp_apply, frobenius_def, ← pow_mul, ← pow_two] using
    actionAddHom_smul τ M eM c ((frobenius K p).comp (frobenius K p)) hτ' a s

/-- The actual section action bundled as a Frobenius-square-semilinear map. -/
def actionSemilinear
    (hτ : τ.hom ≫ c =
      c ≫ (SchemeFrobenius.baseMap p K ≫ SchemeFrobenius.baseMap p K)) :
    letI := sectionsModule M c
    Γ(M, ⊤) →ₛₗ[(frobenius K p).comp (frobenius K p)] Γ(M, ⊤) :=
  letI := sectionsModule M c
  { toFun := actionAddHom τ M eM
    map_add' := (actionAddHom τ M eM).map_add
    map_smul' := fun a s => by
      simpa only [RingHom.comp_apply, frobenius_def, ← pow_mul, ← pow_two] using
        actionAddHom_frobeniusSquare_smul τ M eM c p hτ a s }

theorem actionSemilinear_apply
    (hτ : τ.hom ≫ c =
      c ≫ (SchemeFrobenius.baseMap p K ≫ SchemeFrobenius.baseMap p K))
    (s : Γ(M, ⊤)) :
    actionSemilinear τ M eM c p hτ s = actionAddHom τ M eM s := rfl

end SupersingularCurves.Geometry.FrobeniusFiniteFieldDescent
