/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.Verschiebung
import SupersingularCurves.Geometry.PointedCotangent
import SupersingularCurves.Geometry.JacobianVerschiebung
import SupersingularCurves.Geometry.AbelianVariety
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj

/-!
# Naturality of genuine scheme Verschiebung

The map on Frobenius twists is the actual map of fibre products. Naturality
of Verschiebung follows from its independently proved multiplication-by-p
factorization and faithful-flat epimorphy of relative Frobenius.
No superspecial or supersingular classification is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

namespace SupersingularCurves.Geometry.SchemeFrobenius
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
variable {K : Type u} [Field K] [CharP K p]
variable {X Y Z : Scheme.{u}}
variable {c : X ⟶ Spec (CommRingCat.of K)}
variable {d : Y ⟶ Spec (CommRingCat.of K)}
variable {e : Z ⟶ Spec (CommRingCat.of K)}

/-- The actual base-change morphism between Frobenius fibre products. -/
def map (f : X ⟶ Y) (hf : f ≫ d = c) : Twist p c ⟶ Twist p d :=
  pullback.lift (projection p c ≫ f) (toBase p c)
    (by rw [Category.assoc, hf]; exact pullback.condition)

@[reassoc (attr := simp)]
theorem map_projection (f : X ⟶ Y) (hf : f ≫ d = c) :
    map p f hf ≫ projection p d = projection p c ≫ f :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem map_toBase (f : X ⟶ Y) (hf : f ≫ d = c) :
    map p f hf ≫ toBase p d = toBase p c :=
  pullback.lift_snd _ _ _

theorem map_id : map p (𝟙 X) (Category.id_comp c) = 𝟙 (Twist p c) := by
  apply pullback.hom_ext <;> simp [map, projection, toBase]

theorem map_comp (f : X ⟶ Y) (hf : f ≫ d = c)
    (g : Y ⟶ Z) (hg : g ≫ e = d) :
    map p (f ≫ g) (by rw [Category.assoc, hg, hf]) =
      map p f hf ≫ map p g hg := by
  apply pullback.hom_ext <;> simp [map, projection, toBase, Category.assoc]

/-- Relative Frobenius is natural for actual base-preserving morphisms. -/
theorem relative_natural (f : X ⟶ Y) (hf : f ≫ d = c) :
    relative p c ≫ map p f hf = f ≫ relative p d := by
  apply pullback.hom_ext
  · change (relative p c ≫ map p f hf) ≫ projection p d =
      (f ≫ relative p d) ≫ projection p d
    simp only [Category.assoc, map_projection, relative_projection, relative_projection_assoc]
    exact Scheme.frobenius_comp f p 1 (Fact.out : p.Prime)
      (globalChar p c) (globalChar p d)
  · change (relative p c ≫ map p f hf) ≫ toBase p d =
      (f ≫ relative p d) ≫ toBase p d
    simp only [Category.assoc, map_toBase, relative_toBase, hf]

end SupersingularCurves.Geometry.SchemeFrobenius

namespace SupersingularCurves.Geometry.GroupScheme
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj

variable {K : Type u} [Field K]

instance overMkGrpObj (G : GroupScheme K) : GrpObj (Over.mk G.X.hom) := by
  change GrpObj G.X
  infer_instance

/-- The law is derived from the given group scheme, on every test scheme. -/
def law (G : GroupScheme K) : RelativeGroupLaw K G.X.hom :=
  relativeGroupLawOfGrpObj K G.X.hom

theorem nsmul_eq_pow (G : GroupScheme K) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (n : ℕ) (P : Over.mk t ⟶ G.X) :
    (law G).nsmul t n (overHomToSchemeHomOver P) =
      overHomToSchemeHomOver (P ^ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (law G).mul t ((law G).nsmul t n (overHomToSchemeHomOver P))
      (overHomToSchemeHomOver P) = _
    rw [ih]
    simp only [law, relativeGroupLawOfGrpObj_mul,
      schemeHomOverToOverHom_overHomToSchemeHomOver, pow_succ]

/-- Natural-number multiplication commutes with every genuine group morphism. -/
theorem schemeNsmul_natural {G H : GroupScheme K} (f : G ⟶ H) (n : ℕ) :
    (law G).schemeNsmul n ≫ f.hom.hom.left =
      f.hom.hom.left ≫ (law H).schemeNsmul n := by
  let P : Over.mk G.X.hom ⟶ G.X := 𝟙 G.X
  have h := (IsMonHom.monoidHom f.hom.hom (Over.mk G.X.hom)).map_pow P n
  have h' := congrArg (fun q : Over.mk G.X.hom ⟶ H.X => q.left) h
  have hG := congrArg Subtype.val (nsmul_eq_pow G G.X.hom n P)
  have hH := congrArg Subtype.val (nsmul_eq_pow H G.X.hom n (P ≫ f.hom.hom))
  rw [SchemeFrobenius.nsmul_point] at hG hH
  change P.left ≫ (law G).schemeNsmul n = (P ^ n).left at hG
  change (P ≫ f.hom.hom).left ≫ (law H).schemeNsmul n =
    ((P ≫ f.hom.hom) ^ n).left at hH
  change (P ^ n).left ≫ f.hom.hom.left = ((P ≫ f.hom.hom) ^ n).left at h'
  rw [← hG, ← hH] at h'
  change (𝟙 G.X.left ≫ (law G).schemeNsmul n) ≫ f.hom.hom.left =
    (𝟙 G.X.left ≫ f.hom.hom.left) ≫ (law H).schemeNsmul n at h'
  simpa only [Category.id_comp] using h'

end SupersingularCurves.Geometry.GroupScheme

namespace SupersingularCurves.Geometry.PerfectFieldVerschiebung
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian SchemeFrobenius

variable (p : ℕ) [Fact p.Prime]
variable {K : Type u} [Field K] [CharP K p] [PerfectField K]
variable {G H : GroupScheme K} [Smooth G.X.hom] [Smooth H.X.hom]

/-- Naturality of independently constructed Verschiebung for a genuine
group-scheme morphism. The Frobenius twists are not suppressed. -/
theorem natural (f : G ⟶ H)
    (hG : (GroupScheme.law G).IsCommutative)
    (hH : (GroupScheme.law H).IsCommutative) :
    verschiebung p G.X.hom (GroupScheme.law G) hG ≫ f.hom.hom.left =
      SchemeFrobenius.map p f.hom.hom.left f.hom.hom.w ≫
        verschiebung p H.X.hom (GroupScheme.law H) hH := by
  let hF := finite_flat_surjective p G.X.hom
  let : IsFinite (relative p G.X.hom) := hF.1
  let : Flat (relative p G.X.hom) := hF.2.1
  let : Surjective (relative p G.X.hom) := hF.2.2.2
  rw [← cancel_epi (relative p G.X.hom), ← Category.assoc,
    frobenius_verschiebung, ← Category.assoc,
    relative_natural, Category.assoc, frobenius_verschiebung]
  exact GroupScheme.schemeNsmul_natural f p

end SupersingularCurves.Geometry.PerfectFieldVerschiebung

namespace SupersingularCurves.Geometry.PointedCotangent
open CategoryTheory AlgebraicGeometry NeronModelInfra

variable {K : Type u} [Field K] {X Y : Scheme.{u}}
variable {c : X ⟶ Spec (CommRingCat.of K)}
  {d : Y ⟶ Spec (CommRingCat.of K)}
variable {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c}
  {z : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) d}

theorem iso_inv_over (e : X ≅ Y) (he : e.hom ≫ d = c) : e.inv ≫ c = d := by
  rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]

theorem iso_inv_point (e : X ≅ Y) (hs : s.1 ≫ e.hom = z.1) :
    z.1 ≫ e.inv = s.1 := by
  rw [← hs, Category.assoc, e.hom_inv_id, Category.comp_id]

/-- Cotangent equivalence induced by a genuine pointed scheme isomorphism. -/
def isoEquiv (e : X ≅ Y) (he : e.hom ≫ d = c) (hs : s.1 ≫ e.hom = z.1) :
    Cotangent d z ≃ₗ[K] Cotangent c s where
  toFun := differential c s e.hom he hs
  invFun := differential d z e.inv (iso_inv_over e he) (iso_inv_point e hs)
  left_inv ω := by
    have h := differential_comp d z e.inv (iso_inv_over e he) (iso_inv_point e hs)
      e.hom he hs
    simp only [e.inv_hom_id, differential_id] at h
    exact LinearMap.congr_fun h.symm ω
  right_inv ω := by
    have h := differential_comp c s e.hom he hs
      e.inv (iso_inv_over e he) (iso_inv_point e hs)
    simp only [e.hom_inv_id, differential_id] at h
    exact LinearMap.congr_fun h.symm ω
  map_add' := (differential c s e.hom he hs).map_add
  map_smul' := (differential c s e.hom he hs).map_smul

variable {X' Y' : Scheme.{u}}
variable {c' : X' ⟶ Spec (CommRingCat.of K)}
  {d' : Y' ⟶ Spec (CommRingCat.of K)}
variable {s' : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c'}
  {z' : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) d'}

/-- A commuting square of actual pointed morphisms gives the contravariant
commuting square on actual maximal-ideal cotangent spaces. -/
theorem differential_square
    (f : X ⟶ Y) (hf : f ≫ d = c) (hfs : s.1 ≫ f = z.1)
    (f' : X' ⟶ Y') (hf' : f' ≫ d' = c') (hfs' : s'.1 ≫ f' = z'.1)
    (a : X ⟶ X') (ha : a ≫ c' = c) (has : s.1 ≫ a = s'.1)
    (b : Y ⟶ Y') (hb : b ≫ d' = d) (hbz : z.1 ≫ b = z'.1)
    (hsq : a ≫ f' = f ≫ b) :
    differential c s a ha has ∘ₗ differential c' s' f' hf' hfs' =
      differential c s f hf hfs ∘ₗ differential d z b hb hbz := by
  rw [← differential_comp, ← differential_comp]
  simp only [hsq]

/-- Vanishing of the true cotangent differential is invariant under
isomorphisms of both pointed source and pointed target in a commuting square. -/
theorem differential_eq_zero_iff_of_iso_square
    (f : X ⟶ Y) (hf : f ≫ d = c) (hfs : s.1 ≫ f = z.1)
    (f' : X' ⟶ Y') (hf' : f' ≫ d' = c') (hfs' : s'.1 ≫ f' = z'.1)
    (a : X ≅ X') (ha : a.hom ≫ c' = c) (has : s.1 ≫ a.hom = s'.1)
    (b : Y ≅ Y') (hb : b.hom ≫ d' = d) (hbz : z.1 ≫ b.hom = z'.1)
    (hsq : a.hom ≫ f' = f ≫ b.hom) :
    differential c s f hf hfs = 0 ↔ differential c' s' f' hf' hfs' = 0 := by
  have h := differential_square f hf hfs f' hf' hfs'
    a.hom ha has b.hom hb hbz hsq
  constructor
  · intro hzero
    apply LinearMap.ext
    intro ω
    apply (isoEquiv a ha has).injective
    change differential c s a.hom ha has (differential c' s' f' hf' hfs' ω) = _
    have he := LinearMap.congr_fun h ω
    simpa only [hzero, LinearMap.comp_apply, LinearMap.zero_apply, map_zero] using he
  · intro hzero
    apply LinearMap.ext
    intro ω
    obtain ⟨ω', rfl⟩ := (isoEquiv b hb hbz).surjective ω
    change differential c s f hf hfs (differential d z b.hom hb hbz ω') = 0
    have he := LinearMap.congr_fun h ω'
    simpa only [hzero, LinearMap.comp_apply, LinearMap.zero_apply, map_zero] using he.symm

/-- Replacing identity sections by proved equal sections preserves the
vanishing statement, including all dependent cotangent-space types. -/
theorem differential_eq_zero_iff_of_points_eq
    {s₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c}
    {z₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) d}
    (hs : s = s₁) (hz : z = z₁)
    (f : X ⟶ Y) (hf : f ≫ d = c)
    (hfs : s.1 ≫ f = z.1) (hfs₁ : s₁.1 ≫ f = z₁.1) :
    differential c s f hf hfs = 0 ↔ differential c s₁ f hf hfs₁ = 0 := by
  cases hs
  cases hz
  rfl

end SupersingularCurves.Geometry.PointedCotangent

namespace SupersingularCurves.Geometry.SchemeFrobenius
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
variable {K : Type u} [Field K] [CharP K p]
variable {X Y : Scheme.{u}}
variable {c : X ⟶ Spec (CommRingCat.of K)}
  {d : Y ⟶ Spec (CommRingCat.of K)}

/-- The actual isomorphism of Frobenius twists induced by a base-preserving
scheme isomorphism. -/
def mapIso (e : X ≅ Y) (he : e.hom ≫ d = c) : Twist p c ≅ Twist p d where
  hom := map p e.hom he
  inv := map p e.inv (PointedCotangent.iso_inv_over e he)
  hom_inv_id := by
    rw [← map_comp]
    simp only [e.hom_inv_id, map_id]
  inv_hom_id := by
    rw [← map_comp]
    simp only [e.inv_hom_id, map_id]

end SupersingularCurves.Geometry.SchemeFrobenius

namespace SupersingularCurves.Geometry.GroupScheme
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj

variable {K : Type u} [Field K]

/-- The identity section of the independently supplied group scheme. -/
def zero (G : GroupScheme K) :
    SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) G.X.hom :=
  (law G).one _

theorem zero_natural {G H : GroupScheme K} (f : G ⟶ H) :
    (zero G).1 ≫ f.hom.hom.left = (zero H).1 := by
  have h : (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) ≫ f.hom.hom = 1 :=
    MonObj.one_comp _
  exact congrArg (fun q : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X => q.left) h

variable (p : ℕ) [Fact p.Prime] [CharP K p]

/-- The actual identity section on the Frobenius twist. -/
def twistZero (G : GroupScheme K) :
    SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (SchemeFrobenius.toBase p G.X.hom) :=
  (SchemeFrobenius.twistLaw p G.X.hom (law G)).one _

theorem relative_zero (G : GroupScheme K) :
    (zero G).1 ≫ SchemeFrobenius.relative p G.X.hom = (twistZero p G).1 :=
  congrArg Subtype.val (SchemeFrobenius.relative_one p G.X.hom (law G) _)

theorem twistZero_natural {G H : GroupScheme K} (f : G ⟶ H) :
    (twistZero p G).1 ≫ SchemeFrobenius.map p f.hom.hom.left f.hom.hom.w =
      (twistZero p H).1 := by
  rw [← relative_zero, Category.assoc, SchemeFrobenius.relative_natural,
    ← Category.assoc, zero_natural, relative_zero]

variable [PerfectField K]

/-- The actual Verschiebung cotangent map of a smooth commutative group
scheme, with its actual Frobenius-twisted target cotangent space. -/
def verschiebungCotangent (G : GroupScheme K) [Smooth G.X.hom]
    (hc : (law G).IsCommutative) :
    PointedCotangent.Cotangent G.X.hom (zero G) →ₗ[K]
      PointedCotangent.Cotangent (SchemeFrobenius.toBase p G.X.hom) (twistZero p G) :=
  PointedCotangent.differential (SchemeFrobenius.toBase p G.X.hom) (twistZero p G)
    (PerfectFieldVerschiebung.verschiebung p G.X.hom (law G) hc)
    (PerfectFieldVerschiebung.verschiebung_over p G.X.hom (law G) hc)
    (PerfectFieldVerschiebung.verschiebung_zero p G.X.hom (law G) hc)

/-- The true cotangent square for every morphism of smooth commutative
group schemes. In particular this applies to genuine product projections. -/
theorem verschiebungCotangent_natural {G H : GroupScheme K}
    [Smooth G.X.hom] [Smooth H.X.hom] (f : G ⟶ H)
    (hG : (law G).IsCommutative) (hH : (law H).IsCommutative) :
    PointedCotangent.differential (SchemeFrobenius.toBase p G.X.hom) (twistZero p G)
        (SchemeFrobenius.map p f.hom.hom.left f.hom.hom.w)
        (SchemeFrobenius.map_toBase p f.hom.hom.left f.hom.hom.w)
        (twistZero_natural p f) ∘ₗ verschiebungCotangent p H hH =
      verschiebungCotangent p G hG ∘ₗ
        PointedCotangent.differential G.X.hom (zero G) f.hom.hom.left
          f.hom.hom.w (zero_natural f) :=
  PointedCotangent.differential_square _ _ _ _ _ _ _ _ _ _ _ _
    (PerfectFieldVerschiebung.natural p f hG hH).symm

/-- Actual group-scheme isomorphisms preserve vanishing of the actual
Verschiebung cotangent map. No classification theorem is assumed. -/
theorem verschiebungCotangent_eq_zero_iff_of_iso {G H : GroupScheme K}
    [Smooth G.X.hom] [Smooth H.X.hom] (e : G ≅ H)
    (hG : (law G).IsCommutative) (hH : (law H).IsCommutative) :
    verschiebungCotangent p G hG = 0 ↔ verschiebungCotangent p H hH = 0 := by
  let es : G.X.left ≅ H.X.left := underlyingScheme.mapIso e
  exact PointedCotangent.differential_eq_zero_iff_of_iso_square
    _ _ _ _ _ _
    (SchemeFrobenius.mapIso p es e.hom.hom.hom.w)
    (SchemeFrobenius.map_toBase p e.hom.hom.hom.left e.hom.hom.hom.w)
    (twistZero_natural p e.hom)
    es e.hom.hom.hom.w (zero_natural e.hom)
    (PerfectFieldVerschiebung.natural p e.hom hG hH).symm

end SupersingularCurves.Geometry.GroupScheme

namespace SupersingularCurves.Geometry.PointedCotangent
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open scoped CategoryTheory.MonObj

variable {K : Type u} [Field K] {g : ℕ}
variable (E : Fin g → GroupScheme K)
variable {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of K))
  (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)

local instance productCotangentOppositeModule : Module Kᵐᵒᵖ (Cotangent c s) :=
  Module.compHom _ (RingEquiv.toOpposite K).symm.toRingHom

local instance productCotangentCentralScalar : IsCentralScalar K (Cotangent c s) :=
  ⟨fun _ _ => rfl⟩

/-- The actual product universal property detects zero cotangent maps.
The proof compares all square-zero points using product projections; no
direct-sum model for the product cotangent space is postulated. -/
theorem differential_eq_zero_of_product_components
    (f : X ⟶ (∏ᶜ E).X.left) (hf : f ≫ (∏ᶜ E).X.hom = c)
    (hfs : s.1 ≫ f = (GroupScheme.zero (∏ᶜ E)).1)
    (hcomp : ∀ i : Fin g,
      differential c s (f ≫ (Pi.π E i).hom.hom.left)
        (by rw [Category.assoc, (Pi.π E i).hom.hom.w, hf])
        (by rw [← Category.assoc, hfs, GroupScheme.zero_natural]) = 0) :
    differential c s f hf hfs = 0 := by
  let P := ∏ᶜ E
  let V := Cotangent c s
  let t := pointsEquiv c s V LinearMap.id
  let z := GroupScheme.zero P
  let q := mapPoint c s f hf hfs t
  let q₀ := pointsEquiv P.X.hom z V 0
  have heq : q = q₀ := by
    apply TangentPoints.ext
    have hov :
        (Over.homMk q.1 q.2.1 : Over.mk (SquareZero.toBase K V) ⟶ P.X) =
          Over.homMk q₀.1 q₀.2.1 := by
      apply (isLimitOfPreserves (Grp.forget (Over (Spec (CommRingCat.of K))))
        (limit.isLimit (Discrete.functor E))).hom_ext
      intro i
      cases i with
      | mk i =>
        apply Over.OverMorphism.ext
        change q.1 ≫ (Pi.π E i).hom.hom.left = q₀.1 ≫ (Pi.π E i).hom.hom.left
        have h₁ := differential_action c s (f ≫ (Pi.π E i).hom.hom.left)
          (by rw [Category.assoc, (Pi.π E i).hom.hom.w, hf])
          (by rw [← Category.assoc, hfs, GroupScheme.zero_natural])
          (LinearMap.id : V →ₗ[K] V)
        rw [hcomp i, LinearMap.comp_zero] at h₁
        have h₂ := differential_action P.X.hom z (Pi.π E i).hom.hom.left
          (Pi.π E i).hom.hom.w (GroupScheme.zero_natural (Pi.π E i))
          (0 : Cotangent P.X.hom z →ₗ[K] V)
        rw [LinearMap.zero_comp] at h₂
        have hp := congrArg Subtype.val (h₁.symm.trans h₂)
        simpa only [q, q₀, t, mapPoint, Category.assoc] using hp
    exact congrArg (fun r : Over.mk (SquareZero.toBase K V) ⟶ P.X => r.left) hov
  apply (pointsEquiv P.X.hom z V).injective
  change pointsEquiv P.X.hom z V ((pointsEquiv P.X.hom z V).symm q) = q₀
  rw [Equiv.apply_symm_apply]
  exact heq

end SupersingularCurves.Geometry.PointedCotangent

namespace SupersingularCurves.Geometry.GroupScheme
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

variable (p : ℕ) [Fact p.Prime]
variable {K : Type u} [Field K] [CharP K p] [PerfectField K] {g : ℕ}

/-- A product of smooth commutative group schemes has zero Verschiebung
cotangent map when each factor does. This is a theorem about the actual
categorical product and actual scheme morphisms. -/
theorem verschiebungCotangent_product_eq_zero
    (E : Fin g → GroupScheme K) [∀ i, Smooth (E i).X.hom]
    [Smooth (∏ᶜ E).X.hom]
    (hP : (law (∏ᶜ E)).IsCommutative)
    (hE : ∀ i, (law (E i)).IsCommutative)
    (hzero : ∀ i, verschiebungCotangent p (E i) (hE i) = 0) :
    verschiebungCotangent p (∏ᶜ E) hP = 0 := by
  apply PointedCotangent.differential_eq_zero_of_product_components E
  intro i
  have h := verschiebungCotangent_natural p (Pi.π E i) hP (hE i)
  rw [hzero i, LinearMap.comp_zero] at h
  rw [PointedCotangent.differential_comp]
  exact h.symm

end SupersingularCurves.Geometry.GroupScheme

namespace SupersingularCurves.Geometry.Jacobian
open CategoryTheory AlgebraicGeometry AlgebraicCurve NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
variable {M : CurveModel K F}
  {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase}
variable (J : Jacobian M s)

/-- The abstract group-scheme law is exactly the independently constructed
Picard tensor-product law of the actual Jacobian. -/
theorem groupScheme_law_eq : GroupScheme.law J.abelianVariety.group = J.groupLaw := rfl

theorem groupScheme_zero_eq :
    GroupScheme.zero J.abelianVariety.group =
      (⟨J.designation.zeroSection, J.designation.zeroSection_toBase⟩ :
        SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) J.designation.toBase) := by
  apply Subtype.ext
  exact J.represents.relativeGroupLaw_one (P := algEquivZeroGroupCut M.toBase s)

variable (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K]

local instance groupScheme_smooth : Smooth J.abelianVariety.group.X.hom :=
  SmoothOfRelativeDimension.smooth (genusFF K F) J.designation.toBase

theorem groupScheme_twistZero_eq :
    GroupScheme.twistZero p J.abelianVariety.group = J.twistedZero p := by
  apply Subtype.ext
  rw [← GroupScheme.relative_zero, J.groupScheme_zero_eq]
  exact J.frobenius_zero p

/-- Vanishing of the general group-scheme cotangent map is the existing
actual-Jacobian Verschiebung vanishing condition. The identity and twisted
identity sections are compared, and the Picard group law is unchanged. -/
theorem groupScheme_verschiebungCotangent_eq_zero_iff :
    GroupScheme.verschiebungCotangent p J.abelianVariety.group
        (J.represents.relativeGroupLaw_isCommutative
          (P := algEquivZeroGroupCut M.toBase s)) = 0 ↔
      J.verschiebungCotangent p = 0 := by
  exact PointedCotangent.differential_eq_zero_iff_of_points_eq
    (J.groupScheme_twistZero_eq p) J.groupScheme_zero_eq _ _ _ _

end SupersingularCurves.Geometry.Jacobian
