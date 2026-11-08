/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.PolarisationRootKernel
import Theorems.Thm_AlgebraicGeometry_Polarisation_kernelPts_finite_and_geomFibreH0Finrank_pos_of_finiteBySections
import Theorems.Thm_AlgebraicGeometry_Polarisation_kernelPts_tensor_eq_of_inPicZero
import Theorems.Thm_AlgebraicGeometry_Polarisation_geomFibreH0Finrank_pos_of_iso_tensorPow_tensor_of_inPicZero_of_kernelPts_finite
import Theorems.Thm_AlgebraicGeometry_Polarisation_geomFibreH0Finrank_tensor_eq_of_inPicZero_of_kernelPts_finite
import Theorems.Thm_AlgebraicGeometry_Polarisation_subsingleton_HSucc_and_finrank_eq_pow_mul_of_iso_tensorPow_of_finite_kernelPts_of_finrank_pos_u0
import Theorems.Thm_AlgebraicGeometry_Polarisation_finiteBySections_of_iso_tensorPow_three_of_finite_kernelPts_of_finrank_pos
import Theorems.Thm_AlgebraicGeometry_Polarisation_finite_kernelPts_of_iso_tensorPow_of_finite_kernelPts
import Theorems.Thm_AlgebraicGeometry_Polarisation_exists_inPicZero_isSymmetric_tensor_of_kernelPts_finite
import Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_iff_nonempty_iso_of_field
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_id_eq_finrank_sections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_comp_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_locIsoOnBase
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_finrank_sections_eq_eulerChar_of_iso_of_forall_subsingleton_HSucc

/-!
# Positivity and numerical invariants of actual polarization roots

A root modulo Pic0 of a line bundle finite by sections has finite translation
kernel and positive H0. Its powers have the expected section counts, and its
cube is finite by sections. None of these statements identifies a finite map
with a closed immersion: the general very-ampleness theorem is separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SupersingularCurves.Geometry.PolarisationRootNumerics
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open GoodReductionJacobian NeronModelInfra AlgebraicGeometry.Polarisation

variable (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}}
  (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)

/-- A sheaf isomorphism preserves the geometric H0 rank. -/
theorem geomH0_eq_of_iso (M N : A.Modules) (e : M ≅ N)
    (k' : Type) [Field k'] (sk : k →+* k') :
    Scheme.Modules.geomFibreH0Finrank f M k' sk =
      Scheme.Modules.geomFibreH0Finrank f N k' sk := by
  apply Scheme.Modules.geomFibreH0Finrank_eq_of_locIsoOnBase f
  intro s
  exact ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso e⟩⟩

variable (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
  (g : ℕ) (hdim : ∀ s : Spec (CommRingCat.of k), topologicalKrullDim (f.base ⁻¹' {s}) = g)

include hc hA hdim in
/-- No finite-kernel or positivity hypothesis on the root is needed. -/
theorem root_finiteKernel_positive_of_finiteBySections (M R P : A.Modules)
    (hM : Scheme.Modules.IsInvertible M) (hfs : M.FiniteBySections f)
    (hR : Scheme.Modules.IsInvertible R) (hP : InPicZero f L P)
    (n : ℕ) (hn : 0 < n) (e : M ≅ R.tensorPow n ⊗ P) :
    (kernelPts f L R).Finite ∧
      ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : k →+* k'),
        0 < Scheme.Modules.geomFibreH0Finrank f R k' sk := by
  obtain ⟨hKM, hposM⟩ := kernelPts_finite_and_geomFibreH0Finrank_pos_of_finiteBySections
    k f L hc hA g hdim M hM hfs
  have hKR := finite_kernelPts_of_root k f L M R P hR hP n e hKM
  exact ⟨hKR, fun k' _ _ sk =>
    geomFibreH0Finrank_pos_of_iso_tensorPow_tensor_of_inPicZero_of_kernelPts_finite
      k f L hc hA g hdim R hR hKR n hn P hP M e hposM k' sk⟩

section Cohomology
variable [IsProper f] [SmoothOfRelativeDimension g f]
  (R : A.Modules) (hR : Scheme.Modules.IsInvertible R)
  (hKR : (kernelPts f L R).Finite)
  (hpos : 0 < Scheme.Modules.geomFibreH0Finrank f R k (RingHom.id k))

include hc hA g hR hKR hpos in
/-- Positive nondegenerate bundles have no higher Cech cohomology. -/
theorem higherCohomology_zero (𝒰 : A.OrderedAffineCover) (i : ℕ) :
    Subsingleton ((OModulePresheaf.ofModules f R).HSucc 𝒰 i) := by
  have hp := hpos
  rw [Scheme.Modules.geomFibreH0Finrank_id_eq_finrank_sections k f R hR] at hp
  exact (subsingleton_HSucc_and_finrank_eq_pow_mul_of_iso_tensorPow_of_finite_kernelPts_of_finrank_pos_u0
    k f L hc hA g R hR hKR hp 1 (by decide) R (λ_ R).symm).1 𝒰 i

include hc hA g hR hKR hpos in
/-- H0 is the actual Euler characteristic, on any ordered affine cover. -/
theorem geomH0_eq_eulerChar (𝒰 : A.OrderedAffineCover) :
    (Scheme.Modules.geomFibreH0Finrank f R k (RingHom.id k) : ℤ) =
      (OModulePresheaf.ofModules f R).eulerChar 𝒰 := by
  rw [Scheme.Modules.geomFibreH0Finrank_id_eq_finrank_sections k f R hR]
  exact OModulePresheaf.finrank_sections_eq_eulerChar_of_iso_of_forall_subsingleton_HSucc
    f R R (Iso.refl _) 𝒰 (higherCohomology_zero k f L hc hA g R hR hKR hpos 𝒰)

include hc hA hR hKR hpos in
/-- Exact section count of every positive tensor power, over every field extension. -/
theorem geomH0_tensorPow (n : ℕ) (hn : 0 < n)
    (k' : Type) [Field k'] (sk : k →+* k') :
    Scheme.Modules.geomFibreH0Finrank f (R.tensorPow n) k' sk =
      n ^ g * Scheme.Modules.geomFibreH0Finrank f R k' sk := by
  have hp := hpos
  rw [Scheme.Modules.geomFibreH0Finrank_id_eq_finrank_sections k f R hR] at hp
  have hnum := (subsingleton_HSucc_and_finrank_eq_pow_mul_of_iso_tensorPow_of_finite_kernelPts_of_finrank_pos_u0
    k f L hc hA g R hR hKR hp n hn (R.tensorPow n) (Iso.refl _)).2
  have hpow := FrobeniusLineBundle.tensorPower_invertible hR n
  have eR := Scheme.Modules.geomFibreH0Finrank_comp_eq f R hR k k' (RingHom.id k) sk
  have eN := Scheme.Modules.geomFibreH0Finrank_comp_eq f (R.tensorPow n) hpow k k' (RingHom.id k) sk
  simp only [RingHom.comp_id] at eR eN
  rw [eR, eN, Scheme.Modules.geomFibreH0Finrank_id_eq_finrank_sections k f R hR,
    Scheme.Modules.geomFibreH0Finrank_id_eq_finrank_sections k f (R.tensorPow n) hpow]
  exact hnum

include hc hA hR hKR hpos in
/-- A root already gives a finite projective map with a fixed exponent, namely three. -/
theorem cube_finiteBySections : (R.tensorPow 3).FiniteBySections f := by
  have hp := hpos
  rw [Scheme.Modules.geomFibreH0Finrank_id_eq_finrank_sections k f R hR] at hp
  exact finiteBySections_of_iso_tensorPow_three_of_finite_kernelPts_of_finrank_pos
    k f L hc hA R hR hKR hp (R.tensorPow 3) (Iso.refl _)
end Cohomology

variable [IsProper f] [SmoothOfRelativeDimension g f]

include hc hA hdim in
/-- Extracting a root divides the geometric H0 rank by the dimension power.
Both nondegeneracy and positivity of the root are proved from the input. -/
theorem geomH0_root_scaling (M R P : A.Modules)
    (hM : Scheme.Modules.IsInvertible M) (hfs : M.FiniteBySections f)
    (hR : Scheme.Modules.IsInvertible R) (hP : InPicZero f L P)
    (n : ℕ) (hn : 0 < n) (e : M ≅ R.tensorPow n ⊗ P)
    (k' : Type) [Field k'] [IsAlgClosed k'] (sk : k →+* k') :
    Scheme.Modules.geomFibreH0Finrank f M k' sk =
      n ^ g * Scheme.Modules.geomFibreH0Finrank f R k' sk := by
  obtain ⟨hKR, hpos⟩ := root_finiteKernel_positive_of_finiteBySections
    k f L hc hA g hdim M R P hM hfs hR hP n hn e
  have hRn := FrobeniusLineBundle.tensorPower_invertible hR n
  have hKn := finite_kernelPts_of_iso_tensorPow_of_finite_kernelPts
    k f L hc hA R hR hKR n hn (R.tensorPow n) (Iso.refl _)
  rw [geomH0_eq_of_iso k f M _ e k' sk,
    geomFibreH0Finrank_tensor_eq_of_inPicZero_of_kernelPts_finite
      k f L hc hA g hdim (R.tensorPow n) hRn hKn P hP k' sk]
  exact geomH0_tensorPow k f L hc hA g R hR hKR (hpos k (RingHom.id k)) n hn k' sk


include hc hA hdim in
/-- Symmetrize the actual root without changing its H0 rank, then take its cube.
This provides precisely the symmetric finite bundle used by Frobenius descent,
with the explicit section count 3^g times that of the root. -/
theorem exists_symmetric_finite_cube (R : A.Modules)
    (hR : Scheme.Modules.IsInvertible R) (hKR : (kernelPts f L R).Finite)
    (hpos : 0 < Scheme.Modules.geomFibreH0Finrank f R k (RingHom.id k)) :
    ∃ Q : A.Modules, InPicZero f L Q ∧
      Scheme.Modules.IsInvertible ((R ⊗ Q).tensorPow 3) ∧
      Nonempty ((Scheme.Modules.pullback (negMor f L)).obj ((R ⊗ Q).tensorPow 3) ≅
        (R ⊗ Q).tensorPow 3) ∧
      ((R ⊗ Q).tensorPow 3).FiniteBySections f ∧
      ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : k →+* k'),
        Scheme.Modules.geomFibreH0Finrank f ((R ⊗ Q).tensorPow 3) k' sk =
          3 ^ g * Scheme.Modules.geomFibreH0Finrank f R k' sk := by
  obtain ⟨Q, hQ, hsym⟩ := exists_inPicZero_isSymmetric_tensor_of_kernelPts_finite
    k f L hc hA g hdim R hR hKR
  have hRQ : Scheme.Modules.IsInvertible (R ⊗ Q) := hR.tensor hQ.1
  have hKRQ : (kernelPts f L (R ⊗ Q)).Finite := by
    rw [kernelPts_tensor_eq_of_inPicZero k f L R hR Q hQ]
    exact hKR
  have hposRQ : 0 < Scheme.Modules.geomFibreH0Finrank f (R ⊗ Q) k (RingHom.id k) := by
    rw [geomFibreH0Finrank_tensor_eq_of_inPicZero_of_kernelPts_finite
      k f L hc hA g hdim R hR hKR Q hQ k (RingHom.id k)]
    exact hpos
  obtain ⟨es⟩ := (locIsoOnBase_iff_nonempty_iso_of_field f _ _).mp hsym
  obtain ⟨ep⟩ := Scheme.Modules.nonempty_pullback_tensorPow_iso (negMor f L) (R ⊗ Q) 3
  refine ⟨Q, hQ, FrobeniusLineBundle.tensorPower_invertible hRQ 3,
    ⟨ep ≪≫ Scheme.Modules.tensorPowMapIso es 3⟩,
    cube_finiteBySections k f L hc hA (R ⊗ Q) hRQ hKRQ hposRQ, ?_⟩
  intro k' _ _ sk
  rw [geomH0_tensorPow k f L hc hA g (R ⊗ Q) hRQ hKRQ hposRQ 3 (by decide) k' sk,
    geomFibreH0Finrank_tensor_eq_of_inPicZero_of_kernelPts_finite
      k f L hc hA g hdim R hR hKR Q hQ k' sk]

end SupersingularCurves.Geometry.PolarisationRootNumerics
