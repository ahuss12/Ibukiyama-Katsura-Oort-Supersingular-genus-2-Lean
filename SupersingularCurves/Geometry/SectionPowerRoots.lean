/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import Definitions.Def_AlgebraicGeometry_SchemeFrobenius

/-!
# Gluing pth roots of sections

On a reduced scheme in characteristic p, a section has a unique pth root
if all its germs have pth roots. The construction uses the actual structure
sheaf and also applies to empty opens and disconnected schemes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.SectionPowerRoots
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] [IsReduced X]
  (hX : (p : Γ(X, ⊤)) = 0)

include hX in
/-- Pth powers distinguish sections of a reduced characteristic-p scheme,
including sections on the empty open. -/
theorem pow_injective (U : X.Opens) :
    Function.Injective (fun s : Γ(X, U) => s ^ p) := by
  nontriviality Γ(X, U)
  have : CharP Γ(X, U) p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr
    (Scheme.natCast_eq_zero_sections hX U)
  exact frobenius_inj Γ(X, U) p

omit [Fact p.Prime] [IsReduced X] in
/-- A root in a stalk extends to a root on a sufficiently small neighborhood. -/
theorem exists_local_pow_eq (U : X.Opens) (s : Γ(X, U)) (x : X) (hx : x ∈ U)
    (h : ∃ y : X.presheaf.stalk x, y ^ p = X.presheaf.germ U x hx s) :
    ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      ∃ t : Γ(X, V), t ^ p = X.presheaf.map (homOfLE hVU).op s := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨V, hVU, hxV, t, ht⟩ := X.presheaf.exists_le_germ_eq y hx
  have he : X.presheaf.germ V x hxV (t ^ p) = X.presheaf.germ U x hx s := by
    rw [map_pow, ht, hy]
  obtain ⟨W, hxW, iWV, iWU, hw⟩ := X.presheaf.germ_eq x hxV hx (t ^ p) s he
  refine ⟨W, iWU.le, hxW, X.presheaf.map iWV.op t, ?_⟩
  simpa only [map_pow, show homOfLE iWU.le = iWU from Subsingleton.elim _ _] using hw

include hX in
/-- Roots in every stalk glue uniquely to a root of the section itself. -/
theorem existsUnique_pow_eq (U : X.Opens) (s : Γ(X, U))
    (h : ∀ (x : X) (hx : x ∈ U),
      ∃ y : X.presheaf.stalk x, y ^ p = X.presheaf.germ U x hx s) :
    ∃! r : Γ(X, U), r ^ p = s := by
  classical
  choose V hVU hxV t ht using
    fun x : U => exists_local_pow_eq X p U s x.1 x.2 (h x.1 x.2)
  have hcover : U ≤ iSup V := by
    intro x hx
    exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf V t := by
    intro i j
    apply pow_injective X p hX (V i ⊓ V j)
    dsimp only
    rw [← map_pow, ← map_pow, ht, ht]
    simp only [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
    rfl
  obtain ⟨r, hr, -⟩ := X.sheaf.existsUnique_gluing' V U
    (fun i => homOfLE (hVU i)) hcover t hcompat
  have hpow : r ^ p = s := by
    apply X.sheaf.eq_of_locally_eq' V U (fun i => homOfLE (hVU i)) hcover
    intro i
    rw [map_pow, hr]
    exact ht i
  exact ⟨r, hpow, fun r' hr' => pow_injective X p hX U (hr'.trans hpow.symm)⟩

include hX in
/-- Existence form of the unique gluing theorem. -/
theorem exists_pow_eq (U : X.Opens) (s : Γ(X, U))
    (h : ∀ (x : X) (hx : x ∈ U),
      ∃ y : X.presheaf.stalk x, y ^ p = X.presheaf.germ U x hx s) :
    ∃ r : Γ(X, U), r ^ p = s :=
  (existsUnique_pow_eq X p hX U s h).exists

end SupersingularCurves.Geometry.SectionPowerRoots
