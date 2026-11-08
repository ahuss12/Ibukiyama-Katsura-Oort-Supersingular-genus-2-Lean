/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.AbelianMultiplicationDegree
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_hopfAlgebra_torsion_finrank_eq_pow_and_nsmulAlgHom_eq
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_bialgHom_torsion_of_hom
import Definitions.Def_Dieudonne_WittHomColimit

/-!
# Actual torsion and its Dieudonné realization

The Hopf algebra is constructed from the given abelian variety's actual
scheme-theoretic torsion, with its natural comparison on every test algebra.
Every actual group morphism induces a map of these Hopf algebras and hence
a Dieudonné map commuting with both Frobenius and Verschiebung.

For an elliptic curve the coordinate algebra has dimension `p²`. This
realization does not assert the supersingular Dieudonné normal form or lift
arbitrary maps of infinitesimal torsion to elliptic homomorphisms.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj

variable {K : Type u} [Field K] {g h : ℕ}

/-- A presentation of actual scheme-theoretic torsion, including its natural
group-valued functor of points. Existence is proved below from the abelian
variety; no presentation or comparison is an input to that construction. -/
structure TorsionHopfRealization (A : AbelianVariety K g) (n : ℕ) where
  Coord : Type u
  [commRing : CommRing Coord]
  [hopf : HopfAlgebra K Coord]
  [finite : Module.Finite K Coord]
  [cocomm : Coalgebra.IsCocomm K Coord]
  rank_eq : Module.finrank K Coord = n ^ (2 * g)
  nsmul_eq : PDivisibleGroup.Hopf.nsmulAlgHom K Coord n =
    (Algebra.ofId K Coord).comp (Bialgebra.counitAlgHom K Coord)
  points : ∀ (T : Type u) [CommRing T] [Algebra K T],
    WithConv (Coord →ₐ[K] T) ≃ (GroupScheme.law A.group).torsionSubset
      (Spec.map (CommRingCat.ofHom (algebraMap K T))) n
  points_mul : ∀ (T : Type u) [CommRing T] [Algebra K T]
    (φ ψ : WithConv (Coord →ₐ[K] T)),
    ((points T (φ * ψ)).val : SchemeHomOver _ A.group.X.hom) =
      (GroupScheme.law A.group).mul _ (points T φ).val (points T ψ).val
  points_natural : ∀ (T T' : Type u) [CommRing T] [Algebra K T]
    [CommRing T'] [Algebra K T'] (a : T →ₐ[K] T') (φ : WithConv (Coord →ₐ[K] T)),
    ((points T' (.toConv (a.comp φ.ofConv))).val : SchemeHomOver _ A.group.X.hom).1 =
      Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (points T φ).val.1

attribute [instance] TorsionHopfRealization.commRing TorsionHopfRealization.hopf
  TorsionHopfRealization.finite TorsionHopfRealization.cocomm

namespace AbelianVariety

/-- Construct the Hopf algebra of the actual torsion of the given variety. -/
def torsionHopfRealization [IsAlgClosed K] (A : AbelianVariety K g)
    (n : ℕ) (hn : n ≠ 0) : TorsionHopfRealization A n := by
  let hex := A.abelianSchemePropertyBundle.exists_hopfAlgebra_torsion_finrank_eq_pow_and_nsmulAlgHom_eq
    K A.group.X.hom (GroupScheme.law A.group) A.groupScheme_law_commutative
    g n hn
  choose H hR hH hfin hcomm hrank hkill e hmul hnat using hex
  exact {
    Coord := H
    commRing := hR
    hopf := hH
    finite := hfin
    cocomm := hcomm
    rank_eq := hrank
    nsmul_eq := hkill
    points := e
    points_mul := hmul
    points_natural := hnat }

end AbelianVariety

namespace GroupScheme

/-- Preservation of the actual relative group law by a group-scheme map. -/
theorem torsionRealization_map_mul {G H : GroupScheme K} (f : G ⟶ H)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t G.X.hom) :
    NeronModelInfra.schemeHomOverComp ((law G).mul t x y)
        (⟨f.hom.hom.left, f.hom.hom.w⟩ : SchemeHomOver G.X.hom H.X.hom) =
      (law H).mul t
        (NeronModelInfra.schemeHomOverComp x
          (⟨f.hom.hom.left, f.hom.hom.w⟩ : SchemeHomOver G.X.hom H.X.hom))
        (NeronModelInfra.schemeHomOverComp y
          (⟨f.hom.hom.left, f.hom.hom.w⟩ : SchemeHomOver G.X.hom H.X.hom)) := by
  have hm := (IsMonHom.monoidHom f.hom.hom (Over.mk t)).map_mul
    (schemeHomOverToOverHom x) (schemeHomOverToOverHom y)
  apply Subtype.ext
  exact congrArg (fun z : Over.mk t ⟶ H.X => z.left) hm

end GroupScheme

namespace TorsionHopfRealization
variable {A : AbelianVariety K g} {B : AbelianVariety K h} {n : ℕ}
variable (HA : TorsionHopfRealization A n) (HB : TorsionHopfRealization B n)

/-- The coordinate map is obtained from the genuine morphism on all actual
torsion points, including points over nonreduced test algebras. -/
theorem exists_map (f : A.group ⟶ B.group) :
    ∃ φ : HB.Coord →ₐc[K] HA.Coord,
      ∀ (T : Type u) [CommRing T] [Algebra K T] (x : WithConv (HA.Coord →ₐ[K] T)),
        ((HB.points T (.toConv (x.ofConv.comp (φ : HB.Coord →ₐ[K] HA.Coord)))).val :
            SchemeHomOver _ B.group.X.hom) =
          NeronModelInfra.schemeHomOverComp
            ((HA.points T x).val : SchemeHomOver _ A.group.X.hom)
            (⟨f.hom.hom.left, f.hom.hom.w⟩ : SchemeHomOver A.group.X.hom B.group.X.hom) := by
  exact GoodReductionJacobian.RelativeGroupLaw.exists_bialgHom_torsion_of_hom
    (GroupScheme.law A.group) (GroupScheme.law B.group) ⟨f.hom.hom.left, f.hom.hom.w⟩
    (fun t x y => GroupScheme.torsionRealization_map_mul f t x y)
    n HA.Coord HB.Coord HA.points HA.points_mul HA.points_natural
    HB.points HB.points_mul HB.points_natural

/-- Pullback on the constructed actual torsion coordinate algebras. -/
def map (f : A.group ⟶ B.group) : HB.Coord →ₐc[K] HA.Coord :=
  Classical.choose (exists_map HA HB f)

theorem map_points (f : A.group ⟶ B.group)
    (T : Type u) [CommRing T] [Algebra K T] (x : WithConv (HA.Coord →ₐ[K] T)) :
    ((HB.points T (.toConv (x.ofConv.comp (map HA HB f : HB.Coord →ₐ[K] HA.Coord)))).val :
        SchemeHomOver _ B.group.X.hom) =
      NeronModelInfra.schemeHomOverComp
        ((HA.points T x).val : SchemeHomOver _ A.group.X.hom)
        (⟨f.hom.hom.left, f.hom.hom.w⟩ : SchemeHomOver A.group.X.hom B.group.X.hom) :=
  Classical.choose_spec (exists_map HA HB f) T x

/-- The actual comparison on all test algebras detects coordinate maps. -/
theorem hom_ext (φ ψ : HB.Coord →ₐc[K] HA.Coord)
    (hφψ : ∀ (T : Type u) [CommRing T] [Algebra K T]
      (x : WithConv (HA.Coord →ₐ[K] T)),
      ((HB.points T (.toConv (x.ofConv.comp (φ : HB.Coord →ₐ[K] HA.Coord)))).val :
          SchemeHomOver _ B.group.X.hom) =
        (HB.points T (.toConv (x.ofConv.comp (ψ : HB.Coord →ₐ[K] HA.Coord)))).val) :
    φ = ψ := by
  have hp := hφψ HA.Coord (.toConv (AlgHom.id K HA.Coord))
  have he := (HB.points HA.Coord).injective (Subtype.ext hp)
  ext z
  exact congrArg (fun q : WithConv (HB.Coord →ₐ[K] HA.Coord) => q.ofConv z) he

theorem map_id : map HA HA (𝟙 A.group) = BialgHom.id K HA.Coord := by
  apply hom_ext HA HA
  intro T _ _ x
  rw [map_points]
  apply Subtype.ext
  simp [NeronModelInfra.schemeHomOverComp]

theorem map_comp {i : ℕ} {C : AbelianVariety K i}
    (HC : TorsionHopfRealization C n) (f : A.group ⟶ B.group) (g' : B.group ⟶ C.group) :
    map HA HC (f ≫ g') = (map HA HB f).comp (map HB HC g') := by
  apply hom_ext HA HC
  intro T _ _ x
  rw [map_points]
  have hg := map_points HB HC g' T
    (.toConv (x.ofConv.comp (map HA HB f : HB.Coord →ₐ[K] HA.Coord)))
  rw [map_points HA HB f] at hg
  apply Subtype.ext
  have hgv := congrArg Subtype.val hg
  simpa [NeronModelInfra.schemeHomOverComp, Category.assoc, AlgHom.comp_assoc] using hgv.symm

/-- The actual Witt-covector Dieudonné group of the constructed Hopf algebra. -/
abbrev Dieudonne (p : ℕ) [Fact p.Prime] := Deformation.DieudonneModule K p HA.Coord

/-- The induced contravariant map on actual torsion Dieudonné groups. -/
def dieudonneMap (p : ℕ) [Fact p.Prime] (f : A.group ⟶ B.group) :
    Dieudonne HB p →+ Dieudonne HA p :=
  Deformation.DieudonneModule.map K p (map HA HB f)

theorem dieudonneMap_id (p : ℕ) [Fact p.Prime] (z : Dieudonne HA p) :
    dieudonneMap HA HA p (𝟙 A.group) z = z := by
  simp only [dieudonneMap, map_id, Deformation.DieudonneModule.map_id]

theorem dieudonneMap_comp {i : ℕ} {C : AbelianVariety K i}
    (HC : TorsionHopfRealization C n) (p : ℕ) [Fact p.Prime]
    (f : A.group ⟶ B.group) (g' : B.group ⟶ C.group) (z : Dieudonne HC p) :
    dieudonneMap HA HC p (f ≫ g') z =
      dieudonneMap HA HB p f (dieudonneMap HB HC p g' z) := by
  simp only [dieudonneMap, map_comp HA HB HC, Deformation.DieudonneModule.map_comp]

theorem dieudonneMap_frobenius (p : ℕ) [Fact p.Prime] [CharP K p]
    (f : A.group ⟶ B.group) (z : Dieudonne HB p) :
    dieudonneMap HA HB p f (Deformation.DieudonneModule.frobenius K p HB.Coord z) =
      Deformation.DieudonneModule.frobenius K p HA.Coord (dieudonneMap HA HB p f z) :=
  Deformation.DieudonneModule.map_frobenius (map HA HB f) z

theorem dieudonneMap_verschiebung (p : ℕ) [Fact p.Prime]
    (f : A.group ⟶ B.group) (z : Dieudonne HB p) :
    dieudonneMap HA HB p f (Deformation.DieudonneModule.verschiebung K p HB.Coord z) =
      Deformation.DieudonneModule.verschiebung K p HA.Coord (dieudonneMap HA HB p f z) :=
  Deformation.DieudonneModule.map_verschiebung (map HA HB f) z

end TorsionHopfRealization

namespace AbelianVariety
variable [IsAlgClosed K]

/-- In particular, the actual elliptic `p`-torsion coordinate algebra has
dimension `p²`, including in characteristic `p`. -/
theorem elliptic_torsionHopf_finrank (E : AbelianVariety K 1)
    (p : ℕ) [Fact p.Prime] :
    Module.finrank K (E.torsionHopfRealization p (Fact.out : p.Prime).ne_zero).Coord = p ^ 2 := by
  simpa using (E.torsionHopfRealization p (Fact.out : p.Prime).ne_zero).rank_eq

end AbelianVariety
end SupersingularCurves.Geometry
