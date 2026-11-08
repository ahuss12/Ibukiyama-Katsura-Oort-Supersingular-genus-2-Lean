/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentSections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_frame_of_frame_sum_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_mem_isFrameOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_smul_of_forall_exists_bijective_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_locallyQuasiFinite_of_forall_exists_eq_sum_smul

/-!
# Finite projective presentations by a full basis of actual sections

A full basis of global sections of a sheaf admitting a projective presentation
again gives a projective presentation. If the original presentation is finite,
the new one is finite. No closed immersion is assumed or asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FrobeniusFiniteFieldDescent
open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K] {X : Scheme.{u}}
variable (c : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)

variable {n N : ℕ} (P : M.ProjPresentation c N)
include P

/-- A nonempty scheme with a projective presentation has nonzero global
sections of the presented sheaf. -/
theorem sections_nontrivial_of_presentation [Nonempty X] : Nontrivial Γ(M, ⊤) := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨i, U, hx, hs⟩ := P.exists_mem_isFrameOn x
  have : Nontrivial Γ(X, U) := (X.presheaf.germ U x hx).hom.domain_nontrivial
  refine ⟨⟨P.σ i, 0, fun h0 => ?_⟩⟩
  have hb := hs (le_top : U ≤ ⊤) (le_refl U)
  have h10 : (1 : Γ(X, U)) = 0 := hb.1 (by simp only [h0, map_zero, smul_zero])
  exact one_ne_zero h10

/-- Positive dimension follows from the existing presentation and nonemptiness. -/
theorem finrank_pos_of_presentation [Nonempty X] :
    letI := sectionsModule M c
    ∀ [Module.Finite K Γ(M, ⊤)], 0 < Module.finrank K Γ(M, ⊤) := by
  let := sectionsModule M c
  intro hfinite
  have := sections_nontrivial_of_presentation c M P
  exact Module.finrank_pos

private abbrev RawFrame (s : Γ(M, ⊤)) (W : X.Opens) : Prop :=
  ∀ V : X.Opens, V ≤ W →
    Function.Bijective fun g : Γ(X, V) =>
      g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s : Γ(M, V))

/-- Some basis vector is a frame near every point. -/
theorem basis_frameCover :
    letI := sectionsModule M c
    ∀ b : Module.Basis (Fin (n + 1)) K Γ(M, ⊤),
    ∃ W : Fin (n + 1) → X.Opens, iSup W = ⊤ ∧ ∀ i V, V ≤ W i →
      Function.Bijective fun g : Γ(X, V) =>
        g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (b i) : Γ(M, V)) := by
  classical
  let := sectionsModule M c
  intro b
  refine ⟨fun i => ⨆ (W : X.Opens) (_ : RawFrame M (b i) W), W, ?_, ?_⟩
  · refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨k, U, hx, hk⟩ := P.exists_mem_isFrameOn x
    have hk' : RawFrame M (P.σ k) U := fun V hV => hk le_top hV
    have hsum : ∑ i, scalarHom c (b.repr (P.σ k) i) • b i = P.σ k :=
      b.sum_repr (P.σ k)
    rw [← hsum] at hk'
    obtain ⟨j, W, hxW, hW⟩ := Scheme.Modules.exists_frame_of_frame_sum_smul M
      (fun i => scalarHom c (b.repr (P.σ k) i)) b x ⟨U, hx, hk'⟩
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, TopologicalSpace.Opens.mem_iSup.2
      ⟨W, TopologicalSpace.Opens.mem_iSup.2 ⟨hW, hxW⟩⟩⟩
  · intro i V hV
    apply Scheme.Modules.bijective_smul_of_forall_exists_bijective_smul M (b i) V
    intro x hx
    obtain ⟨W, hW⟩ := TopologicalSpace.Opens.mem_iSup.1 (hV hx)
    obtain ⟨hPW, hxW⟩ := TopologicalSpace.Opens.mem_iSup.1 hW
    exact ⟨W, hxW, hPW⟩

/-- The complete basis defines a genuine projective presentation. -/
theorem exists_presentation_basis :
    letI := sectionsModule M c
    ∀ b : Module.Basis (Fin (n + 1)) K Γ(M, ⊤),
    ∃ Q : M.ProjPresentation c n, Q.σ = b := by
  let := sectionsModule M c
  intro b
  obtain ⟨W, hW, hfr⟩ := basis_frameCover c M P b
  obtain ⟨Q, hQ, -⟩ := Scheme.Modules.exists_projPresentation_of_iSup_eq_top c M n b W hW hfr
  exact ⟨Q, hQ⟩

/-- Replacing a finite presentation by a full section basis preserves finiteness. -/
theorem exists_finitePresentation_basis [IsFinite P.toProj] :
    letI := sectionsModule M c
    ∀ b : Module.Basis (Fin (n + 1)) K Γ(M, ⊤),
    ∃ Q : M.ProjPresentation c n, Q.σ = b ∧ IsFinite Q.toProj := by
  let := sectionsModule M c
  intro b
  obtain ⟨Q, hQ⟩ := exists_presentation_basis c M P b
  refine ⟨Q, hQ, ?_⟩
  have : LocallyQuasiFinite Q.toProj :=
    P.locallyQuasiFinite_of_forall_exists_eq_sum_smul Q (by
      intro i
      refine ⟨fun j => b.repr (P.σ i) j, ?_⟩
      rw [hQ]
      exact (b.sum_repr (P.σ i)).symm)
  have : IsProper c := by
    rw [← P.toProj_π]
    infer_instance
  have : IsProper (Q.toProj ≫ ProjSpace.π K n) := by
    rw [Q.toProj_π]
    infer_instance
  have : IsProper Q.toProj := IsProper.of_comp Q.toProj (ProjSpace.π K n)
  exact IsFinite.of_isProper_of_locallyQuasiFinite Q.toProj

omit P in
/-- A module basis is a section basis with the actual structure-map scalars. -/
theorem isSectionBasis_of_basis {m : ℕ} :
    letI := sectionsModule M c
    ∀ b : Module.Basis (Fin m) K Γ(M, ⊤),
    Scheme.Modules.IsSectionBasis c M b := by
  let := sectionsModule M c
  intro b
  change Function.Bijective (fun a : Fin m → K =>
    ∑ i, (c.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a i)) • b i)
  have heq : (fun a : Fin m → K =>
      ∑ i, (c.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a i)) • b i) =
      fun a => b.equivFun.symm a := by
    funext a
    rw [Module.Basis.equivFun_symm_apply,
      show c.appLE ⊤ ⊤ le_top = c.appTop from c.appLE_eq_app]
    rfl
  rw [heq]
  exact b.equivFun.symm.bijective

/-- A full fixed basis gives a finite presentation by fixed sections, with
its positive number of coordinates obtained from the original presentation. -/
theorem exists_finitePresentation_fixed [Nonempty X] [IsFinite P.toProj] :
    letI := sectionsModule M c
    ∀ [Module.Finite K Γ(M, ⊤)] (θ : Γ(M, ⊤) →+ Γ(M, ⊤))
    (b : Module.Basis (Fin (Module.finrank K Γ(M, ⊤))) K Γ(M, ⊤)),
    (∀ i, θ (b i) = b i) →
    ∃ (n : ℕ) (Q : M.ProjPresentation c n), IsFinite Q.toProj ∧
      Scheme.Modules.IsSectionBasis c M Q.σ ∧ ∀ i, θ (Q.σ i) = Q.σ i := by
  let := sectionsModule M c
  intro hfinite θ b hb
  have hpos := finrank_pos_of_presentation c M P
  let n := Module.finrank K Γ(M, ⊤) - 1
  have hn : Module.finrank K Γ(M, ⊤) = n + 1 :=
    (Nat.succ_pred_eq_of_pos hpos).symm
  let b' : Module.Basis (Fin (n + 1)) K Γ(M, ⊤) := b.reindex (finCongr hn)
  obtain ⟨Q, hQ, hfin⟩ := exists_finitePresentation_basis c M P b'
  refine ⟨n, Q, hfin, ?_, ?_⟩
  · rw [hQ]
    exact isSectionBasis_of_basis c M b'
  · intro i
    rw [hQ]
    simpa only [b', Module.Basis.reindex_apply] using hb ((finCongr hn).symm i)

end SupersingularCurves.Geometry.FrobeniusFiniteFieldDescent
