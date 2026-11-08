/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import Definitions.Def_AlgebraicGeometry_SchemeFrobenius
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_tensorPowSection_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorPowSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_of_locallySurjective
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor

/-!
# Frobenius pullback of an actual line bundle

The p-th tensor power of a section is additive for an invertible sheaf in
characteristic p. Its adjoint is the canonical map from Frobenius pullback
to the tensor power. All objects here are actual sheaves on a scheme.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FrobeniusLineBundle
open CategoryTheory MonoidalCategory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (p : ℕ) (hp : p.Prime)
  (hX : (p : Γ(X, ⊤)) = 0) {L : X.Modules} (hL : IsInvertible L)

include hp hX hL in
/-- Additivity is proved locally in a frame, then by sheaf separation. -/
theorem tensorPowSection_add {U : X.Opens} (s t : Γ(L, U)) :
    tensorPowSection (s + t) p = tensorPowSection s p + tensorPowSection t p := by
  classical
  choose V e hx he using fun x : U => hL.exists_isFrameOn x.1
  let W : U → X.Opens := fun x => U ⊓ V x
  have hWU : ∀ x, W x ≤ U := fun _ => inf_le_left
  have hWV : ∀ x, W x ≤ V x := fun _ => inf_le_right
  have hcover : U ≤ iSup W := fun x hxU =>
    Opens.mem_iSup.2 ⟨⟨x, hxU⟩, ⟨hxU, hx ⟨x, hxU⟩⟩⟩
  apply TopCat.Sheaf.eq_of_locally_eq'
    (⟨(L.tensorPow p).presheaf, (L.tensorPow p).isSheaf⟩ : TopCat.Sheaf Ab X)
    W U (fun x => homOfLE (hWU x)) hcover
  intro x
  obtain ⟨a, ha⟩ := (he x (hWV x) (hWV x)).surjective
    (L.presheaf.map (homOfLE (hWU x)).op s)
  obtain ⟨b, hb⟩ := (he x (hWV x) (hWV x)).surjective
    (L.presheaf.map (homOfLE (hWU x)).op t)
  change (L.tensorPow p).presheaf.map (homOfLE (hWU x)).op _ =
    (L.tensorPow p).presheaf.map (homOfLE (hWU x)).op _
  rw [map_add, map_tensorPowSection, map_tensorPowSection, map_tensorPowSection,
    map_add, ← ha, ← hb, ← add_smul, tensorPowSection_smul,
    tensorPowSection_smul, tensorPowSection_smul]
  have hab : (a + b) ^ p = a ^ p + b ^ p := by
    simpa only [powCharRingHom_apply, pow_one] using
      (powCharRingHom Γ(X, W x) p 1 hp (Scheme.natCast_eq_zero_sections hX (W x))).map_add a b
  rw [hab, add_smul]

/-- The section-power map, with its Frobenius semilinearity explicit. -/
def sectionPower (U : X.Opens) :
    Γ(L, U) →ₛₗ[powCharRingHom Γ(X, U) p 1 hp (Scheme.natCast_eq_zero_sections hX U)]
      Γ(L.tensorPow p, U) where
  toFun s := tensorPowSection s p
  map_add' := tensorPowSection_add p hp hX hL
  map_smul' r s := by
    change tensorPowSection (r • s) p = r ^ p ^ 1 • tensorPowSection s p
    rw [pow_one, tensorPowSection_smul]

/-- The section-power map as an O-linear map into Frobenius pushforward. -/
def powerToPushforward : L ⟶ (Scheme.Modules.pushforward (X.frobenius p 1 hp hX)).obj
    (L.tensorPow p) :=
  ⟨{ app := fun U =>
       (ModuleCat.semilinearMapAddEquiv
         (powCharRingHom Γ(X, U.unop) p 1 hp (Scheme.natCast_eq_zero_sections hX U.unop))
         (L.val.obj U) ((L.tensorPow p).val.obj U)) (sectionPower p hp hX hL U.unop)
     naturality := fun {U V} i => by
       ext s
       exact (map_tensorPowSection i.unop s p).symm }⟩

/-- The actual sheaf morphism obtained through pullback/pushforward adjunction. -/
def pullbackToTensorPower : (Scheme.Modules.pullback (X.frobenius p 1 hp hX)).obj L ⟶
    L.tensorPow p :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (X.frobenius p 1 hp hX)).homEquiv
    L (L.tensorPow p)).symm (powerToPushforward p hp hX hL)

/-- This map sends the pullback of a section to its p-th tensor power. -/
theorem pullbackToTensorPower_section {U : X.Opens} (s : Γ(L, U)) :
    (pullbackToTensorPower p hp hX hL).app U
      (pullbackLocalSection (X.frobenius p 1 hp hX) s) = tensorPowSection s p :=
  homEquiv_symm_app_pullbackLocalSection _ _ s

include hL in
/-- Tensor powers of an actual invertible sheaf remain invertible. -/
theorem tensorPower_invertible (n : ℕ) : IsInvertible (L.tensorPow n) := by
  induction n with
  | zero => exact Scheme.Modules.isInvertible_unit X
  | succ n ih => exact ih.tensor hL

/-- The canonical map is locally surjective: the p-th power of a frame is a
frame, and it is the image of the pulled-back frame. -/
theorem pullbackToTensorPower_isIso : IsIso (pullbackToTensorPower p hp hX hL) := by
  apply (hL.pullback (X.frobenius p 1 hp hX)).isIso_of_locallySurjective
    (tensorPower_invertible hL p)
  intro U t x hxU
  obtain ⟨V, e, hxV, he⟩ := hL.exists_isFrameOn x
  let W : X.Opens := U ⊓ V
  have hWU : W ≤ U := inf_le_left
  have hWV : W ≤ V := inf_le_right
  obtain ⟨a, ha⟩ := ((he.tensorPowSection p) hWV hWV).surjective
    ((L.tensorPow p).presheaf.map (homOfLE hWU).op t)
  let N := (Scheme.Modules.pullback (X.frobenius p 1 hp hX)).obj L
  let : Module Γ(X, W) Γ(N, W) := (N.val.obj (op W)).isModule
  let ep : Γ(N, W) := pullbackLocalSection (X.frobenius p 1 hp hX)
    (L.presheaf.map (homOfLE hWV).op e)
  refine ⟨W, hWU, ⟨hxU, hxV⟩, a • ep, ?_⟩
  rw [Scheme.Modules.Hom.app_smul]
  change a • (pullbackToTensorPower p hp hX hL).app W
    (pullbackLocalSection (X.frobenius p 1 hp hX)
      (L.presheaf.map (homOfLE hWV).op e)) = _
  rw [pullbackToTensorPower_section,
    ← map_tensorPowSection]
  exact ha

/-- Absolute Frobenius pullback is the p-th tensor power, as an isomorphism
of actual sheaves of modules on X. -/
def pullbackIsoTensorPower :
    (Scheme.Modules.pullback (X.frobenius p 1 hp hX)).obj L ≅ L.tensorPow p := by
  letI := pullbackToTensorPower_isIso p hp hX hL
  exact asIso (pullbackToTensorPower p hp hX hL)

/-- The isomorphism has the expected value on every pulled-back local section. -/
theorem pullbackIsoTensorPower_section {U : X.Opens} (s : Γ(L, U)) :
    (pullbackIsoTensorPower p hp hX hL).hom.app U
      (pullbackLocalSection (X.frobenius p 1 hp hX) s) = tensorPowSection s p :=
  pullbackToTensorPower_section p hp hX hL s

end SupersingularCurves.Geometry.FrobeniusLineBundle
