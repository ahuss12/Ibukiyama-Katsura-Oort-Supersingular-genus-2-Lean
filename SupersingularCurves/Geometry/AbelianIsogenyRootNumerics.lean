/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.PolarisationRootNumerics
import SupersingularCurves.Geometry.AbelianIsogenyEuler
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_projPresentation_pullback_sigma_eq_toProj_eq

/-!
# Uniform section counts for roots on actual finite-flat quotients

If a genuine finite-flat map has degree m^g and its pullback polarization is
R^m modulo Pic0, then R has exactly the same H0 rank as the original bundle.
Thus the cube of R has a section rank independent of m. Finiteness of that
cube's projective map is proved; being a closed immersion is not assumed or
claimed here.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SupersingularCurves.Geometry.AbelianIsogenyRootNumerics
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open GoodReductionJacobian NeronModelInfra AlgebraicGeometry.Polarisation
open PolarisationRootNumerics AbelianIsogenyEuler

variable {K : Type} [Field K] [IsAlgClosed K] {g : ℕ}

/-- Pulling an actual finite projective presentation back along a finite map
again gives an actual finite projective presentation. -/
theorem finiteBySections_pullback {X Y : Scheme.{0}}
    (c : X ⟶ Spec (CommRingCat.of K)) (ψ : Y ⟶ X) [IsFinite ψ]
    (M : X.Modules) (hM : M.FiniteBySections c) :
    ((Scheme.Modules.pullback ψ).obj M).FiniteBySections (ψ ≫ c) := by
  obtain ⟨N, P, hP⟩ := hM
  obtain ⟨Q, _, he⟩ := P.exists_projPresentation_pullback_sigma_eq_toProj_eq ψ
  letI := hP
  refine ⟨N, Q, ?_⟩
  rw [he]
  infer_instance

private theorem fibre_dimension (A : AbelianVariety K g) (s : Spec (CommRingCat.of K)) :
    topologicalKrullDim (A.group.X.hom.base ⁻¹' {s}) = g :=
  SmoothOfRelativeDimension.topologicalKrullDim_preimage_singleton_eq A.group.X.hom g s
    (A.abelianSchemePropertyBundle.connectedFibres s).nonempty

variable (A B : AbelianVariety K g)
  (ψ : B.group.X.left ⟶ A.group.X.left)
  (hover : ψ ≫ A.group.X.hom = B.group.X.hom) [IsFinite ψ] [hflat : Flat ψ]
  (d : ℕ) (hdegree : ∀ x, Scheme.Hom.finrank ψ x = d)
  (𝒰 : A.group.X.left.OrderedAffineCover)
  (M : A.group.X.left.Modules) (hM : Scheme.Modules.IsInvertible M)
  (hfs : M.FiniteBySections A.group.X.hom)

include hover hdegree 𝒰 hM hfs hflat in
/-- For finite-by-sections bundles the finite-flat degree scales actual H0,
not merely a formal Hilbert coefficient. -/
theorem geomH0_pullback_eq_degree_mul :
    Scheme.Modules.geomFibreH0Finrank B.group.X.hom ((Scheme.Modules.pullback ψ).obj M)
        K (RingHom.id K) =
      d * Scheme.Modules.geomFibreH0Finrank A.group.X.hom M K (RingHom.id K) := by
  have hPB := hM.pullback ψ
  have hfsPB : ((Scheme.Modules.pullback ψ).obj M).FiniteBySections B.group.X.hom := by
    rw [← hover]
    exact finiteBySections_pullback A.group.X.hom ψ M hfs
  obtain ⟨hKA, hpA⟩ := kernelPts_finite_and_geomFibreH0Finrank_pos_of_finiteBySections
    K A.group.X.hom (GroupScheme.law A.group) A.groupScheme_law_commutative
    A.abelianSchemePropertyBundle g (fibre_dimension A) M hM hfs
  obtain ⟨hKB, hpB⟩ := kernelPts_finite_and_geomFibreH0Finrank_pos_of_finiteBySections
    K B.group.X.hom (GroupScheme.law B.group) B.groupScheme_law_commutative
    B.abelianSchemePropertyBundle g (fibre_dimension B) _ hPB hfsPB
  have h := cross_eulerChar_pullback_eq_degree_mul A B ψ hover d hdegree 𝒰 M hM
  rw [← geomH0_eq_eulerChar K B.group.X.hom (GroupScheme.law B.group)
    B.groupScheme_law_commutative B.abelianSchemePropertyBundle g _ hPB hKB
    (hpB K (RingHom.id K)) (𝒰.comap ψ),
    ← geomH0_eq_eulerChar K A.group.X.hom (GroupScheme.law A.group)
    A.groupScheme_law_commutative A.abelianSchemePropertyBundle g M hM hKA
    (hpA K (RingHom.id K)) 𝒰] at h
  exact_mod_cast h

include hover 𝒰 hM hfs hflat in
/-- The m^g degree and m-th root exactly cancel. This is the uniform numerical
bound required for the lattice-quotient family. -/
theorem geomH0_root_eq_of_degree_pow
    (m : ℕ) (hm : 0 < m) (hdeg : ∀ x, Scheme.Hom.finrank ψ x = m ^ g)
    (R P : B.group.X.left.Modules) (hR : Scheme.Modules.IsInvertible R)
    (hP : InPicZero B.group.X.hom (GroupScheme.law B.group) P)
    (e : (Scheme.Modules.pullback ψ).obj M ≅ R.tensorPow m ⊗ P)
    (k' : Type) [Field k'] [IsAlgClosed k'] (sk : K →+* k') :
    Scheme.Modules.geomFibreH0Finrank B.group.X.hom R k' sk =
      Scheme.Modules.geomFibreH0Finrank A.group.X.hom M k' sk := by
  have hfsPB : ((Scheme.Modules.pullback ψ).obj M).FiniteBySections B.group.X.hom := by
    rw [← hover]
    exact finiteBySections_pullback A.group.X.hom ψ M hfs
  have hroot := geomH0_root_scaling K B.group.X.hom (GroupScheme.law B.group)
    B.groupScheme_law_commutative B.abelianSchemePropertyBundle g (fibre_dimension B)
    _ R P (hM.pullback ψ) hfsPB hR hP m hm e K (RingHom.id K)
  have hdegH0 := geomH0_pullback_eq_degree_mul A B ψ hover (m ^ g) hdeg 𝒰 M hM hfs
  have hbase : Scheme.Modules.geomFibreH0Finrank B.group.X.hom R K (RingHom.id K) =
      Scheme.Modules.geomFibreH0Finrank A.group.X.hom M K (RingHom.id K) :=
    Nat.eq_of_mul_eq_mul_left (pow_pos hm g) (hroot.symm.trans hdegH0)
  have eR := Scheme.Modules.geomFibreH0Finrank_comp_eq B.group.X.hom R hR K k' (RingHom.id K) sk
  have eM := Scheme.Modules.geomFibreH0Finrank_comp_eq A.group.X.hom M hM K k' (RingHom.id K) sk
  simp only [RingHom.comp_id] at eR eM
  exact eR.trans (hbase.trans eM.symm)

include hover 𝒰 hM hfs hflat in
/-- All positive powers of the quotient root have a level-independent H0 rank;
the root also has finite translation kernel and positive sections. -/
theorem root_uniform_numerics
    (m : ℕ) (hm : 0 < m) (hdeg : ∀ x, Scheme.Hom.finrank ψ x = m ^ g)
    (R P : B.group.X.left.Modules) (hR : Scheme.Modules.IsInvertible R)
    (hP : InPicZero B.group.X.hom (GroupScheme.law B.group) P)
    (e : (Scheme.Modules.pullback ψ).obj M ≅ R.tensorPow m ⊗ P) :
    (kernelPts B.group.X.hom (GroupScheme.law B.group) R).Finite ∧
    (∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : K →+* k'),
      0 < Scheme.Modules.geomFibreH0Finrank B.group.X.hom R k' sk) ∧
    (R.tensorPow 3).FiniteBySections B.group.X.hom ∧
    ∀ (r : ℕ), 0 < r → ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : K →+* k'),
      Scheme.Modules.geomFibreH0Finrank B.group.X.hom (R.tensorPow r) k' sk =
        r ^ g * Scheme.Modules.geomFibreH0Finrank A.group.X.hom M k' sk := by
  have hfsPB : ((Scheme.Modules.pullback ψ).obj M).FiniteBySections B.group.X.hom := by
    rw [← hover]
    exact finiteBySections_pullback A.group.X.hom ψ M hfs
  obtain ⟨hKR, hpos⟩ := root_finiteKernel_positive_of_finiteBySections
    K B.group.X.hom (GroupScheme.law B.group) B.groupScheme_law_commutative
    B.abelianSchemePropertyBundle g (fibre_dimension B) _ R P (hM.pullback ψ) hfsPB hR hP m hm e
  refine ⟨hKR, hpos, cube_finiteBySections K B.group.X.hom (GroupScheme.law B.group)
    B.groupScheme_law_commutative B.abelianSchemePropertyBundle R hR hKR
    (hpos K (RingHom.id K)), ?_⟩
  intro r hr k' _ _ sk
  rw [geomH0_tensorPow K B.group.X.hom (GroupScheme.law B.group)
    B.groupScheme_law_commutative B.abelianSchemePropertyBundle g R hR hKR
    (hpos K (RingHom.id K)) r hr k' sk]
  rw [geomH0_root_eq_of_degree_pow A B ψ hover 𝒰 M hM hfs m hm hdeg R P hR hP e k' sk]


include hover 𝒰 hM hfs hflat in
/-- The root constructs a symmetric finite bundle with fixed H0 rank 3^g*h0(M),
so symmetrization introduces no quotient-level dependence. -/
theorem exists_symmetric_bundle_with_uniform_rank
    (m : ℕ) (hm : 0 < m) (hdeg : ∀ x, Scheme.Hom.finrank ψ x = m ^ g)
    (R P : B.group.X.left.Modules) (hR : Scheme.Modules.IsInvertible R)
    (hP : InPicZero B.group.X.hom (GroupScheme.law B.group) P)
    (e : (Scheme.Modules.pullback ψ).obj M ≅ R.tensorPow m ⊗ P) :
    ∃ N : B.group.X.left.Modules, Scheme.Modules.IsInvertible N ∧
      Nonempty ((Scheme.Modules.pullback (negMor B.group.X.hom (GroupScheme.law B.group))).obj N ≅ N) ∧
      N.FiniteBySections B.group.X.hom ∧
      ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : K →+* k'),
        Scheme.Modules.geomFibreH0Finrank B.group.X.hom N k' sk =
          3 ^ g * Scheme.Modules.geomFibreH0Finrank A.group.X.hom M k' sk := by
  obtain ⟨hKR, hpos, _, _⟩ := root_uniform_numerics A B ψ hover 𝒰 M hM hfs m hm hdeg R P hR hP e
  obtain ⟨Q, _, hN, hsym, hfin, hnum⟩ := exists_symmetric_finite_cube
    K B.group.X.hom (GroupScheme.law B.group) B.groupScheme_law_commutative
    B.abelianSchemePropertyBundle g (fibre_dimension B) R hR hKR (hpos K (RingHom.id K))
  refine ⟨(R ⊗ Q).tensorPow 3, hN, hsym, hfin, ?_⟩
  intro k' _ _ sk
  rw [hnum k' sk, geomH0_root_eq_of_degree_pow A B ψ hover 𝒰 M hM hfs m hm hdeg R P hR hP e k' sk]

end SupersingularCurves.Geometry.AbelianIsogenyRootNumerics
