/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.EllipticVerschiebungVanishing
import SupersingularCurves.Geometry.FrobeniusBaseChangeDegree

/-!
# The actual Frobenius extension of elliptic p-torsion

The map from the actual multiplication-by-p kernel to the actual Verschiebung
kernel is a base change of relative Frobenius. In particular it is finite,
flat, and surjective of degree p. Its fibre over the identity is the actual
Frobenius kernel. These are scheme statements, including nonreduced test
schemes, underlying the local extension in Oort's elliptic torsion argument.

This file does not assert that a map of these kernels extends to a map of
elliptic curves.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.EllipticTorsionRealization
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian SchemeFrobenius PerfectFieldVerschiebung
open AbelianVariety

variable {K : Type u} [Field K] [IsAlgClosed K]
variable (p : ℕ) [Fact p.Prime] [CharP K p]
variable (E : AbelianVariety K 1)

abbrev torsion : Scheme.{u} := (GroupScheme.law E.group).schemeKer p

abbrev torsionBase : torsion p E ⟶ Spec (CommRingCat.of K) :=
  (GroupScheme.law E.group).schemeKerStr p

abbrev torsionInclusion : torsion p E ⟶ E.group.X.left :=
  pullback.fst ((GroupScheme.law E.group).schemeNsmul p) (GroupScheme.zero E.group).1

abbrev frobeniusKernel : Scheme.{u} :=
  pullback (relative p E.group.X.hom) (GroupScheme.twistZero p E.group).1

abbrev frobeniusKernelBase : frobeniusKernel p E ⟶ Spec (CommRingCat.of K) :=
  pullback.snd (relative p E.group.X.hom) (GroupScheme.twistZero p E.group).1

abbrev frobeniusKernelInclusion : frobeniusKernel p E ⟶ E.group.X.left :=
  pullback.fst (relative p E.group.X.hom) (GroupScheme.twistZero p E.group).1

omit [IsAlgClosed K] [Fact p.Prime] [CharP K p] in
theorem torsionInclusion_over :
    torsionInclusion p E ≫ E.group.X.hom = torsionBase p E := by
  rw [← (GroupScheme.law E.group).schemeNsmul_over p, ← Category.assoc]
  change (pullback.fst _ _ ≫ (GroupScheme.law E.group).schemeNsmul p) ≫ _ = _
  rw [pullback.condition, Category.assoc, (GroupScheme.zero E.group).2,
    Category.comp_id]
  rfl

omit [IsAlgClosed K] in
theorem frobeniusKernelInclusion_over :
    frobeniusKernelInclusion p E ≫ E.group.X.hom = frobeniusKernelBase p E := by
  rw [← relative_toBase p E.group.X.hom, ← Category.assoc]
  change (pullback.fst _ _ ≫ relative p E.group.X.hom) ≫ _ = _
  rw [pullback.condition, Category.assoc, (GroupScheme.twistZero p E.group).2,
    Category.comp_id]

/-- Frobenius on the actual p-torsion factors through the actual V-kernel. -/
def frobeniusOnTorsion : torsion p E ⟶ verschiebungKernelScheme p E :=
  pullback.lift (torsionInclusion p E ≫ relative p E.group.X.hom)
    (torsionBase p E) (by
      rw [Category.assoc]
      change torsionInclusion p E ≫
        (relative p E.group.X.hom ≫ verschiebung p E.group.X.hom
          (GroupScheme.law E.group) (GroupScheme.law_commutative E.group)) = _
      rw [frobenius_verschiebung]
      exact pullback.condition)

@[reassoc (attr := simp)]
theorem frobeniusOnTorsion_inclusion :
    frobeniusOnTorsion p E ≫ verschiebungKernelInclusion p E =
      torsionInclusion p E ≫ relative p E.group.X.hom :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem frobeniusOnTorsion_over :
    frobeniusOnTorsion p E ≫ verschiebungKernelToBase p E = torsionBase p E :=
  pullback.lift_snd _ _ _

/-- This is an actual base change of Frobenius, not a pointwise quotient. -/
theorem frobeniusOnTorsion_isPullback :
    IsPullback (torsionInclusion p E) (frobeniusOnTorsion p E)
      (relative p E.group.X.hom) (verschiebungKernelInclusion p E) := by
  apply IsPullback.of_bot (v₂₁ := verschiebungKernelToBase p E)
    (v₂₂ := ellipticVerschiebung p E) (h₃₁ := (GroupScheme.zero E.group).1)
  · rw [frobeniusOnTorsion_over]
    change IsPullback _ _
      (relative p E.group.X.hom ≫ verschiebung p E.group.X.hom
        (GroupScheme.law E.group) (GroupScheme.law_commutative E.group)) _
    rw [frobenius_verschiebung]
    exact IsPullback.of_hasPullback _ _
  · exact (frobeniusOnTorsion_inclusion p E).symm
  · exact IsPullback.of_hasPullback _ _

/-- The actual Frobenius projection on p-torsion is finite. -/
instance frobeniusOnTorsion_isFinite : IsFinite (frobeniusOnTorsion p E) := by
  let := (finite_flat_surjective p E.group.X.hom).1
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @IsFinite) (frobeniusOnTorsion_isPullback p E) inferInstance

/-- The actual Frobenius projection on p-torsion is flat. -/
instance frobeniusOnTorsion_flat : Flat (frobeniusOnTorsion p E) := by
  let := (finite_flat_surjective p E.group.X.hom).2.1
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @Flat) (frobeniusOnTorsion_isPullback p E) inferInstance

/-- The actual Frobenius projection on p-torsion is surjective. -/
instance frobeniusOnTorsion_surjective : Surjective (frobeniusOnTorsion p E) := by
  let := (finite_flat_surjective p E.group.X.hom).2.2.2
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @Surjective) (frobeniusOnTorsion_isPullback p E) inferInstance

/-- Every scheme-theoretic fibre of the projection has length p. -/
theorem frobeniusOnTorsion_finrank (x : verschiebungKernelScheme p E) :
    (frobeniusOnTorsion p E).finrank x = p := by
  let := (finite_flat_surjective p E.group.X.hom).1
  let := (finite_flat_surjective p E.group.X.hom).2.1
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ (frobeniusOnTorsion_isPullback p E)]
  simpa only [pow_one] using E.relativeFrobenius_finrank p
    (verschiebungKernelInclusion p E x)

/-- The Frobenius kernel is an actual closed subscheme of p-torsion. -/
def frobeniusKernelToTorsion : frobeniusKernel p E ⟶ torsion p E :=
  pullback.lift (frobeniusKernelInclusion p E) (frobeniusKernelBase p E) (by
    rw [← frobenius_verschiebung p E.group.X.hom (GroupScheme.law E.group)
      (GroupScheme.law_commutative E.group), ← Category.assoc]
    change (pullback.fst _ _ ≫ relative p E.group.X.hom) ≫ _ = _
    rw [pullback.condition, Category.assoc]
    congr 1
    exact verschiebung_zero p E.group.X.hom (GroupScheme.law E.group)
      (GroupScheme.law_commutative E.group))

@[reassoc (attr := simp)]
theorem frobeniusKernelToTorsion_inclusion :
    frobeniusKernelToTorsion p E ≫ torsionInclusion p E =
      frobeniusKernelInclusion p E := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem frobeniusKernelToTorsion_over :
    frobeniusKernelToTorsion p E ≫ torsionBase p E =
      frobeniusKernelBase p E := pullback.lift_snd _ _ _

theorem frobeniusKernelToTorsion_frobeniusOnTorsion :
    frobeniusKernelToTorsion p E ≫ frobeniusOnTorsion p E =
      frobeniusKernelBase p E ≫ (verschiebungKernelZero p E).1 := by
  apply (cancel_mono (verschiebungKernelInclusion p E)).mp
  simp only [Category.assoc, frobeniusOnTorsion_inclusion,
    frobeniusKernelToTorsion_inclusion_assoc, verschiebungKernelZero_inclusion]
  exact pullback.condition

/-- The identity fibre of the actual finite flat projection is ker(F). -/
theorem frobeniusKernel_isPullback :
    IsPullback (frobeniusKernelToTorsion p E) (frobeniusKernelBase p E)
      (frobeniusOnTorsion p E) (verschiebungKernelZero p E).1 := by
  apply IsPullback.of_right (h₁₂ := torsionInclusion p E)
    (h₂₂ := verschiebungKernelInclusion p E)
    (v₁₃ := relative p E.group.X.hom)
  · rw [frobeniusKernelToTorsion_inclusion, verschiebungKernelZero_inclusion]
    exact IsPullback.of_hasPullback _ _
  · exact frobeniusKernelToTorsion_frobeniusOnTorsion p E
  · exact frobeniusOnTorsion_isPullback p E

/-- The identity belongs to the actual Frobenius kernel. -/
def frobeniusKernelZero :
    SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (frobeniusKernelBase p E) :=
  ⟨pullback.lift (GroupScheme.zero E.group).1 (𝟙 _) (by
      simpa only [Category.id_comp] using
        GroupScheme.relative_zero p E.group),
    pullback.lift_snd _ _ _⟩

omit [IsAlgClosed K] in
@[reassoc (attr := simp)]
theorem frobeniusKernelZero_inclusion :
    (frobeniusKernelZero p E).1 ≫ frobeniusKernelInclusion p E =
      (GroupScheme.zero E.group).1 := pullback.lift_fst _ _ _

/-- The actual identity of p-torsion, through its Frobenius-kernel inclusion. -/
def torsionZero :
    SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (torsionBase p E) :=
  ⟨(frobeniusKernelZero p E).1 ≫ frobeniusKernelToTorsion p E, by
    rw [Category.assoc, frobeniusKernelToTorsion_over]
    exact (frobeniusKernelZero p E).2⟩

@[reassoc (attr := simp)]
theorem torsionZero_inclusion :
    (torsionZero p E).1 ≫ torsionInclusion p E = (GroupScheme.zero E.group).1 := by
  simp only [torsionZero, Category.assoc, frobeniusKernelToTorsion_inclusion,
    frobeniusKernelZero_inclusion]

instance frobeniusKernelInclusion_isClosedImmersion :
    IsClosedImmersion (frobeniusKernelInclusion p E) := by
  let : IsSeparated (toBase p E.group.X.hom) := by
    change IsSeparated (pullback.snd E.group.X.hom (baseMap p K))
    infer_instance
  let : IsClosedImmersion (GroupScheme.twistZero p E.group).1 :=
    isClosedImmersion_of_comp_eq_id (toBase p E.group.X.hom)
      (GroupScheme.twistZero p E.group).1 (GroupScheme.twistZero p E.group).2
  infer_instance

omit [IsAlgClosed K] in
/-- The Frobenius kernel has height one as an actual scheme: its own relative
Frobenius factors through its identity section. -/
theorem frobeniusKernel_relative_eq_zero :
    relative p (frobeniusKernelBase p E) =
      frobeniusKernelBase p E ≫ (frobeniusKernelZero p E).1 ≫
        relative p (frobeniusKernelBase p E) := by
  let i := frobeniusKernelInclusion p E
  let hi := frobeniusKernelInclusion_over p E
  let : IsClosedImmersion (SchemeFrobenius.map p i hi) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (SchemeFrobenius.map_isPullback p i hi).flip inferInstance
  apply (cancel_mono (SchemeFrobenius.map p i hi)).mp
  rw [relative_natural, Category.assoc, Category.assoc, relative_natural]
  change frobeniusKernelInclusion p E ≫ relative p E.group.X.hom =
    frobeniusKernelBase p E ≫ (frobeniusKernelZero p E).1 ≫
      frobeniusKernelInclusion p E ≫ relative p E.group.X.hom
  rw [← Category.assoc (frobeniusKernelZero p E).1,
    frobeniusKernelZero_inclusion,
    GroupScheme.relative_zero p E.group]
  exact pullback.condition

instance frobeniusKernelBase_isFinite : IsFinite (frobeniusKernelBase p E) := by
  let := (finite_flat_surjective p E.group.X.hom).1
  infer_instance

instance frobeniusKernelBase_flat : Flat (frobeniusKernelBase p E) := by
  let := (finite_flat_surjective p E.group.X.hom).2.1
  infer_instance

/-- The genuine Frobenius kernel of an elliptic curve has scheme rank p. -/
theorem frobeniusKernelBase_finrank :
    (frobeniusKernelBase p E).finrank (IsLocalRing.closedPoint K) = p := by
  let := (finite_flat_surjective p E.group.X.hom).1
  let := (finite_flat_surjective p E.group.X.hom).2.1
  rw [Scheme.Hom.finrank_pullback_snd]
  simpa only [pow_one] using E.relativeFrobenius_finrank p
    ((GroupScheme.twistZero p E.group).1 (IsLocalRing.closedPoint K))

omit [IsAlgClosed K] in
private theorem one_coe {X : Scheme.{u}} {c : X ⟶ Spec (CommRingCat.of K)}
    (L : RelativeGroupLaw K c) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) :
    (L.one t).1 = t ≫ (L.one (𝟙 _)).1 :=
  (congrArg Subtype.val (L.one_natural (𝟙 _) t t (Category.comp_id t))).symm

omit [IsAlgClosed K] in
/-- The actual kernel universal property on every test scheme. -/
theorem factors_iff {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x : SchemeHomOver t E.group.X.hom) :
    (∃ e : T ⟶ frobeniusKernel p E, e ≫ frobeniusKernelInclusion p E = x.1) ↔
      x.1 ≫ relative p E.group.X.hom = t ≫ (GroupScheme.twistZero p E.group).1 := by
  constructor
  · rintro ⟨e, he⟩
    have ht : e ≫ frobeniusKernelBase p E = t := by
      rw [← frobeniusKernelInclusion_over, ← Category.assoc, he, x.2]
    rw [← he, Category.assoc]
    change e ≫ (pullback.fst _ _ ≫ relative p E.group.X.hom) = _
    rw [pullback.condition, ← Category.assoc, ht]
  · intro hx
    exact ⟨pullback.lift x.1 t hx, pullback.lift_fst _ _ _⟩

omit [IsAlgClosed K] in
theorem factors_iff_points {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x : SchemeHomOver t E.group.X.hom) :
    (∃ e : T ⟶ frobeniusKernel p E, e ≫ frobeniusKernelInclusion p E = x.1) ↔
      relativePoint p E.group.X.hom x =
        (twistLaw p E.group.X.hom (GroupScheme.law E.group)).one t := by
  rw [factors_iff]
  constructor
  · intro hx
    exact Subtype.ext (hx.trans (one_coe _ t).symm)
  · intro hx
    exact (congrArg Subtype.val hx).trans (one_coe _ t)

omit [IsAlgClosed K] in
/-- The actual identity section factors through ker(F). -/
theorem one_factors {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) :
    ∃ e : T ⟶ frobeniusKernel p E,
      e ≫ frobeniusKernelInclusion p E = ((GroupScheme.law E.group).one t).1 := by
  apply (factors_iff_points p E t _).mpr
  exact relative_one p E.group.X.hom (GroupScheme.law E.group) t

omit [IsAlgClosed K] in
/-- Multiplication in the ambient elliptic curve preserves its actual ker(F). -/
theorem mul_factors {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t E.group.X.hom)
    (hx : ∃ e : T ⟶ frobeniusKernel p E, e ≫ frobeniusKernelInclusion p E = x.1)
    (hy : ∃ e : T ⟶ frobeniusKernel p E, e ≫ frobeniusKernelInclusion p E = y.1) :
    ∃ e : T ⟶ frobeniusKernel p E,
      e ≫ frobeniusKernelInclusion p E = ((GroupScheme.law E.group).mul t x y).1 := by
  apply (factors_iff_points p E t _).mpr
  rw [relative_mul, (factors_iff_points p E t x).mp hx,
    (factors_iff_points p E t y).mp hy,
    (twistLaw p E.group.X.hom (GroupScheme.law E.group)).one_mul]

omit [IsAlgClosed K] in
/-- Inversion in the ambient elliptic curve preserves its actual ker(F). -/
theorem inv_factors {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x : SchemeHomOver t E.group.X.hom)
    (hx : ∃ e : T ⟶ frobeniusKernel p E, e ≫ frobeniusKernelInclusion p E = x.1) :
    ∃ e : T ⟶ frobeniusKernel p E,
      e ≫ frobeniusKernelInclusion p E = ((GroupScheme.law E.group).inv t x).1 := by
  apply (factors_iff_points p E t _).mpr
  let L := GroupScheme.law E.group
  let M := twistLaw p E.group.X.hom L
  let := L.pointGroup t
  let := M.pointGroup t
  let φ : SchemeHomOver t E.group.X.hom →* SchemeHomOver t (toBase p E.group.X.hom) :=
    { toFun := relativePoint p E.group.X.hom
      map_one' := relative_one p E.group.X.hom L t
      map_mul' := relative_mul p E.group.X.hom L t }
  change φ (x⁻¹) = 1
  rw [map_inv]
  change (relativePoint p E.group.X.hom x)⁻¹ = 1
  rw [(factors_iff_points p E t x).mp hx]
  exact inv_one

variable {E} {E' : AbelianVariety K 1}

/-- Every actual pointed map of p-torsion schemes takes ker(F) into ker(F).
Only naturality of actual Frobenius is used; no extension to elliptic curves
is assumed. -/
theorem torsionMap_frobeniusKernel_eq_zero
    (f : torsion p E ⟶ torsion p E')
    (hf : f ≫ torsionBase p E' = torsionBase p E)
    (hf0 : (torsionZero p E).1 ≫ f = (torsionZero p E').1) :
    (frobeniusKernelToTorsion p E ≫ f ≫ torsionInclusion p E') ≫
        relative p E'.group.X.hom =
      frobeniusKernelBase p E ≫ (GroupScheme.twistZero p E'.group).1 := by
  let q := frobeniusKernelToTorsion p E ≫ f ≫ torsionInclusion p E'
  have hq : q ≫ E'.group.X.hom = frobeniusKernelBase p E := by
    dsimp only [q]
    rw [Category.assoc, Category.assoc, torsionInclusion_over,
      hf, frobeniusKernelToTorsion_over]
  have hq0 : (frobeniusKernelZero p E).1 ≫ q = (GroupScheme.zero E'.group).1 := by
    change (frobeniusKernelZero p E).1 ≫
      frobeniusKernelToTorsion p E ≫ f ≫ torsionInclusion p E' = _
    rw [← Category.assoc, ← Category.assoc]
    change ((torsionZero p E).1 ≫ f) ≫ torsionInclusion p E' = _
    rw [hf0, torsionZero_inclusion]
  change q ≫ relative p E'.group.X.hom = _
  rw [← relative_natural p q hq]
  conv_lhs => rw [frobeniusKernel_relative_eq_zero p E]
  rw [Category.assoc, Category.assoc, relative_natural,
    ← Category.assoc (frobeniusKernelZero p E).1, hq0,
    GroupScheme.relative_zero p E'.group]

/-- Restriction of an actual pointed p-torsion morphism to the actual
Frobenius kernels. -/
def restrictFrobeniusKernel
    (f : torsion p E ⟶ torsion p E')
    (hf : f ≫ torsionBase p E' = torsionBase p E)
    (hf0 : (torsionZero p E).1 ≫ f = (torsionZero p E').1) :
    frobeniusKernel p E ⟶ frobeniusKernel p E' :=
  pullback.lift (frobeniusKernelToTorsion p E ≫ f ≫ torsionInclusion p E')
    (frobeniusKernelBase p E) (torsionMap_frobeniusKernel_eq_zero p f hf hf0)

@[reassoc (attr := simp)]
theorem restrictFrobeniusKernel_inclusion
    (f : torsion p E ⟶ torsion p E')
    (hf : f ≫ torsionBase p E' = torsionBase p E)
    (hf0 : (torsionZero p E).1 ≫ f = (torsionZero p E').1) :
    restrictFrobeniusKernel p f hf hf0 ≫ frobeniusKernelInclusion p E' =
      frobeniusKernelToTorsion p E ≫ f ≫ torsionInclusion p E' :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem restrictFrobeniusKernel_over
    (f : torsion p E ⟶ torsion p E')
    (hf : f ≫ torsionBase p E' = torsionBase p E)
    (hf0 : (torsionZero p E).1 ≫ f = (torsionZero p E').1) :
    restrictFrobeniusKernel p f hf hf0 ≫ frobeniusKernelBase p E' =
      frobeniusKernelBase p E := pullback.lift_snd _ _ _

/-- The restriction commutes with the actual inclusions into p-torsion. -/
theorem restrictFrobeniusKernel_torsion
    (f : torsion p E ⟶ torsion p E')
    (hf : f ≫ torsionBase p E' = torsionBase p E)
    (hf0 : (torsionZero p E).1 ≫ f = (torsionZero p E').1) :
    restrictFrobeniusKernel p f hf hf0 ≫ frobeniusKernelToTorsion p E' =
      frobeniusKernelToTorsion p E ≫ f := by
  apply pullback.hom_ext
  · change (_ ≫ frobeniusKernelToTorsion p E') ≫ torsionInclusion p E' =
      (frobeniusKernelToTorsion p E ≫ f) ≫ torsionInclusion p E'
    simp only [Category.assoc, frobeniusKernelToTorsion_inclusion,
      restrictFrobeniusKernel_inclusion]
  · change (_ ≫ frobeniusKernelToTorsion p E') ≫ torsionBase p E' =
      (frobeniusKernelToTorsion p E ≫ f) ≫ torsionBase p E'
    simp only [Category.assoc, frobeniusKernelToTorsion_over,
      restrictFrobeniusKernel_over, hf]

/-- Compatibility with p-torsion determines the kernel restriction uniquely. -/
theorem restrictFrobeniusKernel_unique
    (f : torsion p E ⟶ torsion p E')
    (hf : f ≫ torsionBase p E' = torsionBase p E)
    (hf0 : (torsionZero p E).1 ≫ f = (torsionZero p E').1)
    (r : frobeniusKernel p E ⟶ frobeniusKernel p E')
    (hr : r ≫ frobeniusKernelToTorsion p E' = frobeniusKernelToTorsion p E ≫ f) :
    r = restrictFrobeniusKernel p f hf hf0 := by
  apply (cancel_mono (frobeniusKernelInclusion p E')).mp
  rw [restrictFrobeniusKernel_inclusion]
  simpa only [Category.assoc, frobeniusKernelToTorsion_inclusion] using
    congrArg (fun q => q ≫ torsionInclusion p E') hr

/-- Restriction of an actual elliptic group homomorphism to its p-torsion
scheme. This retains the entire finite scheme, not only geometric points. -/
def onTorsion (f : E.group ⟶ E'.group) : torsion p E ⟶ torsion p E' :=
  pullback.lift (torsionInclusion p E ≫ f.hom.hom.left) (torsionBase p E) (by
    rw [Category.assoc, ← GroupScheme.schemeNsmul_natural f p, ← Category.assoc]
    change (pullback.fst _ _ ≫ (GroupScheme.law E.group).schemeNsmul p) ≫ _ = _
    rw [pullback.condition, Category.assoc, GroupScheme.zero_natural]
    rfl)

omit [IsAlgClosed K] [Fact p.Prime] [CharP K p] in
@[reassoc (attr := simp)]
theorem onTorsion_inclusion (f : E.group ⟶ E'.group) :
    onTorsion p f ≫ torsionInclusion p E' =
      torsionInclusion p E ≫ f.hom.hom.left := pullback.lift_fst _ _ _

omit [IsAlgClosed K] [Fact p.Prime] [CharP K p] in
@[reassoc (attr := simp)]
theorem onTorsion_over (f : E.group ⟶ E'.group) :
    onTorsion p f ≫ torsionBase p E' = torsionBase p E :=
  pullback.lift_snd _ _ _

theorem onTorsion_zero (f : E.group ⟶ E'.group) :
    (torsionZero p E).1 ≫ onTorsion p f = (torsionZero p E').1 := by
  apply pullback.hom_ext
  · change (_ ≫ onTorsion p f) ≫ torsionInclusion p E' =
      (torsionZero p E').1 ≫ torsionInclusion p E'
    rw [Category.assoc, onTorsion_inclusion, ← Category.assoc,
      torsionZero_inclusion, GroupScheme.zero_natural, torsionZero_inclusion]
  · change (_ ≫ onTorsion p f) ≫ torsionBase p E' =
      (torsionZero p E').1 ≫ torsionBase p E'
    rw [Category.assoc, onTorsion_over, (torsionZero p E).2, (torsionZero p E').2]

omit [IsAlgClosed K] [Fact p.Prime] [CharP K p] in
theorem onTorsion_id : onTorsion p (𝟙 E.group) = 𝟙 (torsion p E) := by
  apply pullback.hom_ext
  · change onTorsion p (𝟙 E.group) ≫ torsionInclusion p E =
      𝟙 (torsion p E) ≫ torsionInclusion p E
    rw [onTorsion_inclusion]
    rfl
  · change onTorsion p (𝟙 E.group) ≫ torsionBase p E =
      𝟙 (torsion p E) ≫ torsionBase p E
    rw [onTorsion_over, Category.id_comp]

omit [IsAlgClosed K] [Fact p.Prime] [CharP K p] in
theorem onTorsion_comp {E'' : AbelianVariety K 1}
    (f : E.group ⟶ E'.group) (g : E'.group ⟶ E''.group) :
    onTorsion p (f ≫ g) = onTorsion p f ≫ onTorsion p g := by
  apply pullback.hom_ext
  · change onTorsion p (f ≫ g) ≫ torsionInclusion p E'' =
      (onTorsion p f ≫ onTorsion p g) ≫ torsionInclusion p E''
    simp only [onTorsion_inclusion, Category.assoc, onTorsion_inclusion_assoc]
    rfl
  · change onTorsion p (f ≫ g) ≫ torsionBase p E'' =
      (onTorsion p f ≫ onTorsion p g) ≫ torsionBase p E''
    simp only [Category.assoc, onTorsion_over]

/-- Restriction of an actual elliptic homomorphism to the actual Frobenius
kernel, through the genuine full p-torsion restriction. -/
def onFrobeniusKernel (f : E.group ⟶ E'.group) :
    frobeniusKernel p E ⟶ frobeniusKernel p E' :=
  restrictFrobeniusKernel p (onTorsion p f) (onTorsion_over p f) (onTorsion_zero p f)

@[reassoc (attr := simp)]
theorem onFrobeniusKernel_inclusion (f : E.group ⟶ E'.group) :
    onFrobeniusKernel p f ≫ frobeniusKernelInclusion p E' =
      frobeniusKernelInclusion p E ≫ f.hom.hom.left := by
  simp only [onFrobeniusKernel, restrictFrobeniusKernel_inclusion,
    onTorsion_inclusion, frobeniusKernelToTorsion_inclusion_assoc]

theorem onFrobeniusKernel_torsion (f : E.group ⟶ E'.group) :
    onFrobeniusKernel p f ≫ frobeniusKernelToTorsion p E' =
      frobeniusKernelToTorsion p E ≫ onTorsion p f :=
  restrictFrobeniusKernel_torsion p (onTorsion p f)
    (onTorsion_over p f) (onTorsion_zero p f)

end SupersingularCurves.Geometry.EllipticTorsionRealization
