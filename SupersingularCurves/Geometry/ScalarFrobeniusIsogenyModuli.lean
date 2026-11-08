/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.ScalarFrobeniusIsogenyFiniteness
import Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_isFineModuli_quasiProjective
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_sections_finite_projective_and_isSectionBasisOn_pullback_type0
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_isSectionBasis_of_finite_sections_of_forall_exists_isFrameOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_mem_isFrameOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isClosedImmersion_toProj_of_isSectionBasis_of_closedImmersionBySections

/-!
# Finite isomorphism representatives for bounded polarized abelian varieties

The actual finite-type moduli scheme gives a finite list of actual framed
polarized abelian schemes over a finite field. Every model is isomorphic to
one of the representatives, preserving the group law, level and line bundle.
Every polarized model over a field admits a complete projective frame of
the prescribed section rank. Forgetting the frame therefore gives a finite
list covering all polarized models with the specified numerical data.

This proves a geometric finiteness ingredient of Tate's argument; it does
not assert a Tate realization theorem or construct a product isogeny.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SupersingularCurves.Geometry.ScalarFrobeniusIsogenyModuli
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

/-- A genuine abelian variety with a very ample line bundle and fixed
geometric section rank has a polarized moduli model at trivial level.
No torsion basis or extension of the ground field is required. -/
def polarizedOfVeryAmple {F : Type u} [Field F] {g d : ℕ}
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of F)}
    (L : RelativeGroupLaw F f) (hc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle F f)
    (hdim : ∀ s : Spec (CommRingCat.of F), topologicalKrullDim (f.base ⁻¹' {s}) = g)
    (pol : A.Modules) (hinv : Scheme.Modules.IsInvertible pol)
    (hva : Scheme.Modules.ClosedImmersionBySections pol f)
    (hrank : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : F →+* k),
      Scheme.Modules.geomFibreH0Finrank f pol k sk = d) : PolarisedAbelianScheme g d 1 F where
  A := A
  f := f
  L := L
  comm := hc
  bundle := hA
  dim_fibre := hdim
  P := fun _ => L.one (𝟙 _)
  P_torsion := by intro i; exact L.nsmul_unit _ _
  P_indep := by intros; exact Subsingleton.elim _ _
  P_span := by
    intro k _ _ sk Q hQ
    refine ⟨fun _ => 0, ?_⟩
    rw [L.nsmul_one_apply] at hQ
    rw [hQ]
    let := L.pointGroup (Spec.map (CommRingCat.ofHom sk))
    simp only [RelativeGroupLaw.finComb, Fin.val_zero, pow_zero, List.ofFn_const, List.prod_replicate, one_pow]
    rfl
  pol := pol
  pol_isInvertible := hinv
  pol_veryAmple := hva
  pol_finrank := hrank


variable (F : Type) [Field F] [Finite F]
variable (g N n : ℕ)

/-- There are finitely many actual framed polarized abelian schemes of
fixed dimension, section rank and level over a finite field, up to their
actual group-scheme and line-bundle isomorphism relation. -/
theorem exists_finite_framed_representatives (hn : IsUnit ((n : ℕ) : F)) :
    ∃ s : Finset (FramedPolarisedAbelianScheme g N n F),
      ∀ X : FramedPolarisedAbelianScheme g N n F,
        ∃ Y ∈ s, FramedPolarisedAbelianScheme.Iso X Y := by
  classical
  obtain ⟨M, π, pt, hmod, hsep, hqc, hfp, haf, hproj⟩ :=
    FramedPolarisedAbelianScheme.exists_isFineModuli_quasiProjective g N n F hn
  let : QuasiCompact π := hqc
  let : LocallyOfFinitePresentation π := hfp
  let := FiniteFieldPoints.finite_scheme_points π
  let : Finite (SchemeHomOver (𝟙 (Spec (CommRingCat.of F))) π) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  let m := pt F (𝟙 (Spec (CommRingCat.of F)))
  let I := Set.range m
  let : Fintype I := Fintype.ofFinite I
  let pick : I → FramedPolarisedAbelianScheme g N n F := fun y => y.property.choose
  refine ⟨Finset.univ.image pick, fun X => ?_⟩
  let y : I := ⟨m X, X, rfl⟩
  refine ⟨pick y, Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩, ?_⟩
  apply hmod.pt_injective F (𝟙 _) X (pick y)
  exact y.property.choose_spec.symm

/-- A framed isomorphism supplies the actual polarized group-scheme
isomorphism after its projective-frame equality is forgotten. -/
theorem iso_forget_frame {F : Type} [Field F] {g N n : ℕ}
    {X Y : FramedPolarisedAbelianScheme g N n F}
    (h : FramedPolarisedAbelianScheme.Iso X Y) :
    PolarisedAbelianScheme.Iso X.toPolarisedAbelianScheme Y.toPolarisedAbelianScheme := by
  obtain ⟨e, he, hframe, hmul, hlevel, hpol⟩ := h
  exact ⟨e, he, hmul, hlevel, hpol⟩

/-- Forgetting frames produces a finite list of actual polarized models
covering every model that admits a global basis defining a closed projective
immersion of the specified section rank. -/
theorem exists_finite_polarized_representatives_of_framed (hn : IsUnit ((n : ℕ) : F)) :
    ∃ s : Finset (PolarisedAbelianScheme g (N + 1) n F),
      ∀ X : PolarisedAbelianScheme g (N + 1) n F,
        (∃ X' : FramedPolarisedAbelianScheme g N n F,
          X'.toPolarisedAbelianScheme = X) →
        ∃ Y ∈ s, PolarisedAbelianScheme.Iso X Y := by
  classical
  obtain ⟨s, hs⟩ := exists_finite_framed_representatives F g N n hn
  refine ⟨s.image FramedPolarisedAbelianScheme.toPolarisedAbelianScheme, ?_⟩
  rintro _ ⟨X, rfl⟩
  obtain ⟨Y, hY, hXY⟩ := hs X
  exact ⟨Y.toPolarisedAbelianScheme, Finset.mem_image.mpr ⟨Y, hY, rfl⟩,
    iso_forget_frame hXY⟩

/-- A complete basis of global sections supplies an actual projective
frame of the prescribed rank over a finite field. -/
theorem exists_frame {F : Type} [Field F] [Finite F] {g N n : ℕ}
    (X : PolarisedAbelianScheme g (N + 1) n F) :
    ∃ X' : FramedPolarisedAbelianScheme g N n F,
      X'.toPolarisedAbelianScheme = X := by
  classical
  obtain ⟨hfin, hlocal, hbase, hrank⟩ :=
    X.bundle.sections_finite_projective_and_isSectionBasisOn_pullback_type0
      X.L X.pol X.pol_isInvertible X.pol_veryAmple
  obtain ⟨N₀, P₀, hP₀⟩ := X.pol_veryAmple
  have hgen : ∀ x : X.A, ∃ (s : Γ(X.pol, ⊤)) (U : X.A.Opens),
      x ∈ U ∧ Scheme.Modules.IsFrameOn s U := by
    intro x
    obtain ⟨i, U, hx, hU⟩ := P₀.exists_mem_isFrameOn x
    exact ⟨P₀.σ i, U, hx, hU⟩
  have hfiniteSections : Finite Γ(X.pol, ⊤) := by
    letI : CommRing F := inferInstance
    letI : Module F Γ(X.pol, ⊤) :=
      Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ X.f.appTop).hom
    letI : Module.Finite F Γ(X.pol, ⊤) := hfin.1
    exact Module.finite_of_finite F
  obtain ⟨M, P, hP⟩ :=
    Scheme.Modules.exists_projPresentation_isSectionBasis_of_finite_sections_of_forall_exists_isFrameOn
      F X.f ⟨(X.L.one (𝟙 _)).1 (IsLocalRing.closedPoint F)⟩ X.pol X.pol_isInvertible
      (by
        letI := hfiniteSections
        letI : Algebra F Γ(X.A, ⊤) :=
          ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ X.f.appLE ⊤ ⊤ le_top).hom.toAlgebra
        change @Module.Finite F Γ(X.pol, ⊤) _ _
          (Module.compHom _ (algebraMap F Γ(X.A, ⊤)))
        exact @Module.Finite.of_finite F Γ(X.pol, ⊤) _ _
          (Module.compHom _ (algebraMap F Γ(X.A, ⊤))) hfiniteSections) hgen
  have heq : M + 1 = N + 1 :=
    (hrank P.σ hP (AlgebraicClosure F) (algebraMap F (AlgebraicClosure F))).symm.trans
      (X.pol_finrank (AlgebraicClosure F) (algebraMap F (AlgebraicClosure F)))
  have hMN : M = N := Nat.add_right_cancel heq
  subst M
  exact ⟨{
    toPolarisedAbelianScheme := X
    frame := P
    frame_isClosedImmersion :=
      P.isClosedImmersion_toProj_of_isSectionBasis_of_closedImmersionBySections X.pol_veryAmple hP
    frame_basis := hP }, rfl⟩

/-- All polarized abelian schemes with fixed dimension, section rank and
prime-to-characteristic level over a finite field have finitely many actual
isomorphism representatives. -/
theorem exists_finite_polarized_representatives (hn : IsUnit ((n : ℕ) : F)) :
    ∃ s : Finset (PolarisedAbelianScheme g (N + 1) n F),
      ∀ X : PolarisedAbelianScheme g (N + 1) n F,
        ∃ Y ∈ s, PolarisedAbelianScheme.Iso X Y := by
  obtain ⟨s, hs⟩ := exists_finite_polarized_representatives_of_framed F g N n hn
  exact ⟨s, fun X => hs X (exists_frame X)⟩

/-- A finite list covers actual abelian varieties over a finite field with
fixed dimension and a very ample line bundle of fixed geometric section rank.
The comparison is an actual scheme isomorphism preserving the group law on
all test schemes; no level structure is assumed of the input variety. -/
theorem exists_finite_abelian_representatives :
    ∃ s : Finset (PolarisedAbelianScheme g (N + 1) 1 F),
      ∀ (A : Scheme) (f : A ⟶ Spec (CommRingCat.of F))
        (L : RelativeGroupLaw F f) (hc : L.IsCommutative)
        (hA : AbelianSchemePropertyBundle F f)
        (hdim : ∀ x : Spec (CommRingCat.of F), topologicalKrullDim (f.base ⁻¹' {x}) = g)
        (pol : A.Modules) (hinv : Scheme.Modules.IsInvertible pol)
        (hva : Scheme.Modules.ClosedImmersionBySections pol f)
        (hrank : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : F →+* k),
          Scheme.Modules.geomFibreH0Finrank f pol k sk = N + 1),
        ∃ Y ∈ s, ∃ (e : A ≅ Y.A) (he : e.hom ≫ Y.f = f),
          ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of F)) (x y : SchemeHomOver t f),
            (L.mul t x y).1 ≫ e.hom =
              (Y.L.mul t
                ⟨x.1 ≫ e.hom, by rw [Category.assoc, he]; exact x.2⟩
                ⟨y.1 ≫ e.hom, by rw [Category.assoc, he]; exact y.2⟩).1 := by
  obtain ⟨s, hs⟩ := exists_finite_polarized_representatives F g N 1 (by simp)
  refine ⟨s, ?_⟩
  intro A f L hc hA hdim pol hinv hva hrank
  obtain ⟨Y, hY, e, he, hmul, hlevel, hpol⟩ :=
    hs (polarizedOfVeryAmple L hc hA hdim pol hinv hva hrank)
  exact ⟨Y, hY, e, he, hmul⟩

end SupersingularCurves.Geometry.ScalarFrobeniusIsogenyModuli
