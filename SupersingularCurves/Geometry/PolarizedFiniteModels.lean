/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.ScalarFrobeniusIsogenyModuli
import SupersingularCurves.Geometry.ScalarFrobeniusPolarizedDescentRank
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_smoothOfRelativeDimension_of_forall_topologicalKrullDim_eq
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral
import Theorems.Thm_AlgebraicGeometry_GeometricallyIrreducible_geometricallyConnected

/-!
# Actual group-scheme representatives from finite polarized moduli

The moduli representatives are converted to actual abelian varieties and their
isomorphisms to group-scheme isomorphisms. Fixed-rank symmetric very ample
bundles on zero-dV varieties therefore give finitely many geometric models.
The existence of those uniformly very ample bundles is still a premise.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SupersingularCurves.Geometry.PolarizedFiniteModels
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open scoped CategoryTheory.MonObj
open ScalarFrobeniusIsogenyModuli FrobeniusDescent

variable {F : Type} [Field F] {g d l : ℕ}

/-- The moduli object carries a genuine abelian variety of its stated dimension. -/
def varietyOfPolarized (X : PolarisedAbelianScheme g d l F) : AbelianVariety F g where
  group := { X := Over.mk X.f, grp := X.L.grpObjOverMk }
  comm := X.L.isCommMonObj_grpObjOverMk_iff_mul_comm.mpr X.comm
  smooth := by
    letI := X.bundle.smooth
    exact X.L.smoothOfRelativeDimension_of_forall_topologicalKrullDim_eq g X.dim_fibre
  proper := X.bundle.proper
  connected := by
    letI := X.bundle.geometricallyIntegral
    exact GeometricallyIrreducible.geometricallyConnected X.f

/-- A scheme isomorphism preserving multiplication on all test schemes is an
isomorphism of the actual internal group objects. -/
def groupIsoOfSchemeIsoMul (A B : AbelianVariety F g)
    (e : A.group.X.left ≅ B.group.X.left) (he : e.hom ≫ B.group.X.hom = A.group.X.hom)
    (hmul : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of F))
      (x y : SchemeHomOver t A.group.X.hom),
      pointMap e.hom he ((GroupScheme.law A.group).mul t x y) =
        (GroupScheme.law B.group).mul t (pointMap e.hom he x) (pointMap e.hom he y)) :
    A.group ≅ B.group := by
  let E : A.group.X ≅ B.group.X := Over.isoMk e he
  letI : IsMonHom E.hom := by
    apply GroupScheme.isMonHom_of_pointMap e.hom he
    · intro T t
      letI := (GroupScheme.law B.group).pointGroup t
      let a := pointMap e.hom he ((GroupScheme.law A.group).one t)
      have ha : a * a = a * 1 := by
        change (GroupScheme.law B.group).mul t a a =
          (GroupScheme.law B.group).mul t a ((GroupScheme.law B.group).one t)
        rw [(GroupScheme.law B.group).mul_one]
        exact (hmul t ((GroupScheme.law A.group).one t)
          ((GroupScheme.law A.group).one t)).symm.trans
            (congrArg (pointMap e.hom he) ((GroupScheme.law A.group).one_mul t _))
      exact mul_left_cancel ha
    · exact hmul
  exact Grp.mkIso' E

variable (F) [Finite F] (g N : ℕ)

/-- Fixed-rank very ample polarizations give a finite list of actual abelian
varieties, with actual group-scheme comparison isomorphisms. -/
theorem exists_finite_variety_representatives :
    ∃ s : Finset (AbelianVariety F g),
      ∀ (A : AbelianVariety F g) (M : A.group.X.left.Modules),
        Scheme.Modules.IsInvertible M → M.ClosedImmersionBySections A.group.X.hom →
        (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : F →+* k),
          Scheme.Modules.geomFibreH0Finrank A.group.X.hom M k sk = N + 1) →
        ∃ B ∈ s, Nonempty (A.group ≅ B.group) := by
  classical
  obtain ⟨s, hs⟩ := exists_finite_abelian_representatives F g N
  refine ⟨s.image varietyOfPolarized, ?_⟩
  intro A M hM hc hrank
  have hdim (x : Spec (CommRingCat.of F)) :
      topologicalKrullDim (A.group.X.hom.base ⁻¹' {x}) = g :=
    SmoothOfRelativeDimension.topologicalKrullDim_preimage_singleton_eq A.group.X.hom g x
      (A.abelianSchemePropertyBundle.connectedFibres x).nonempty
  obtain ⟨Y, hY, e, he, hmul⟩ := hs A.group.X.left A.group.X.hom
    (GroupScheme.law A.group) A.groupScheme_law_commutative A.abelianSchemePropertyBundle
    hdim M hM hc hrank
  refine ⟨varietyOfPolarized Y, Finset.mem_image.mpr ⟨Y, hY, rfl⟩, ⟨?_⟩⟩
  apply groupIsoOfSchemeIsoMul A (varietyOfPolarized Y) e he
  intro T t x y
  apply Subtype.ext
  simpa only [GroupScheme.law, varietyOfPolarized,
    relativeGroupLawOfGrpObj_grpObjOverMk_mul, pointMap] using hmul t x y

variable {K : Type} [Field K] [Algebra F K]

/-- Actual bounded polarized models over one finite field give finitely many
actual geometric group-scheme models for the whole sequence. -/
theorem exists_finite_geometric_models_of_bounded_models
    (A : ℕ → AbelianVariety K g)
    (hmodels : ∀ n, ∃ (B : AbelianVariety F g) (M : B.group.X.left.Modules),
      Scheme.Modules.IsInvertible M ∧ M.ClosedImmersionBySections B.group.X.hom ∧
      Nonempty ((A n).group ≅ (B.baseChange K).group) ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : F →+* k),
        Scheme.Modules.geomFibreH0Finrank B.group.X.hom M k sk = N + 1) :
    ∃ s : Finset (AbelianVariety K g), ∀ n, ∃ B ∈ s, Nonempty (B.group ≅ (A n).group) := by
  classical
  obtain ⟨s, hs⟩ := exists_finite_variety_representatives F g N
  refine ⟨s.image (fun B => B.baseChange K), ?_⟩
  intro n
  obtain ⟨B, M, hM, hc, ⟨eA⟩, hr⟩ := hmodels n
  obtain ⟨C, hC, ⟨eB⟩⟩ := hs B M hM hc hr
  refine ⟨C.baseChange K, Finset.mem_image.mpr ⟨C, hC, rfl⟩, ⟨?_⟩⟩
  exact (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F K)))).mapGrp).mapIso eB).symm ≪≫
    eA.symm

end SupersingularCurves.Geometry.PolarizedFiniteModels

namespace SupersingularCurves.Geometry.ScalarFrobeniusTate
open CategoryTheory AlgebraicGeometry GoodReductionJacobian
open FrobeniusDescent PolarizedFiniteModels
variable {K : Type} [Field K] [IsAlgClosed K] {g : ℕ}

/-- With the very-ampleness input explicit, the finite-field and moduli assembly
is complete. Only the original geometric H0 rank is prescribed. -/
theorem exists_finite_models_of_symmetric_veryAmple_fixed_rank
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (A : ℕ → AbelianVariety K g)
    (hV : ∀ n, GroupScheme.verschiebungCotangent p (A n).group
      (A n).groupScheme_law_commutative = 0)
    (M : ∀ n, (A n).group.X.left.Modules)
    (hM : ∀ n, Scheme.Modules.IsInvertible (M n))
    (hsym : ∀ n, Nonempty ((Scheme.Modules.pullback ((𝟙 (A n).group.X)⁻¹).left).obj (M n) ≅ M n))
    (hc : ∀ n, (M n).ClosedImmersionBySections (A n).group.X.hom)
    (d : ℕ) (hd : 0 < d)
    (hr : ∀ n, Scheme.Modules.geomFibreH0Finrank (A n).group.X.hom (M n) K (RingHom.id K) = d) :
    ∃ s : Finset (AbelianVariety K g), ∀ n, ∃ B ∈ s, Nonempty (B.group ≅ (A n).group) := by
  letI : Finite (fixedField K p 2) := fixedField_finite K p 2 (by decide)
  have hpos : 0 < (p ^ 2) ^ g * d :=
    Nat.mul_pos (pow_pos (pow_pos (Fact.out : p.Prime).pos 2) g) hd
  apply exists_finite_geometric_models_of_bounded_models (fixedField K p 2) g
    ((p ^ 2) ^ g * d - 1) A
  intro n
  obtain ⟨B, L, hL, hLc, hB, hR⟩ :=
    (A n).exists_finiteField_polarized_model_with_rank p (hV n) (M n) (hM n) (hsym n) (hc n)
  refine ⟨B, L, hL, hLc, hB, ?_⟩
  intro k _ _ sk
  rw [hR k sk, hr n, Nat.sub_add_cancel hpos]

end SupersingularCurves.Geometry.ScalarFrobeniusTate
