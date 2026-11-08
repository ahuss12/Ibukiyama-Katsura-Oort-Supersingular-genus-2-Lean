/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.AbelianVariety

/-!
# Superspecial and supersingular abelian varieties

These are geometric definitions on actual group schemes. Over an algebraically
closed field, superspecial means isomorphic to a product of supersingular
elliptic curves, whereas supersingular means isogenous to such a product.
Over an arbitrary field we first base change to its algebraic closure.
Isomorphisms here preserve the scheme group laws; no polarization is required.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace SupersingularCurves.Geometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AbelianVariety
variable {K : Type u} [Field K]

/-- A dimension-one abelian variety over an algebraically closed field is
supersingular when its geometric p-torsion is trivial. The multiplicative
notation is Mathlib's notation for points of a group object. -/
def IsSupersingularElliptic (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsAlgClosed K] (E : AbelianVariety K 1) : Prop :=
  ∀ P : E.Points, P ^ p = 1 → P = 1

/-- Superspeciality over an algebraically closed field: a group-scheme
isomorphism with a product of supersingular elliptic curves. -/
def IsSuperspecialOver (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsAlgClosed K] {g : ℕ} (A : AbelianVariety K g) : Prop :=
  ∃ E : Fin g → AbelianVariety K 1,
    (∀ i, (E i).IsSupersingularElliptic p) ∧
      Nonempty (A.group ≅ ellipticProduct E)

/-- Supersingularity over an algebraically closed field: a finite surjective
group-scheme morphism to a product of supersingular elliptic curves. -/
def IsSupersingularOver (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsAlgClosed K] {g : ℕ} (A : AbelianVariety K g) : Prop :=
  ∃ E : Fin g → AbelianVariety K 1,
    (∀ i, (E i).IsSupersingularElliptic p) ∧
      ∃ f : A.group ⟶ ellipticProduct E, IsIsogeny f

/-- Geometric superspeciality, including finite and perfect ground fields. -/
def IsSuperspecial (p : ℕ) [Fact p.Prime] [CharP K p]
    {g : ℕ} (A : AbelianVariety K g) : Prop :=
  (A.baseChange (AlgebraicClosure K)).IsSuperspecialOver p

/-- Geometric supersingularity, including finite and perfect ground fields. -/
def IsSupersingular (p : ℕ) [Fact p.Prime] [CharP K p]
    {g : ℕ} (A : AbelianVariety K g) : Prop :=
  (A.baseChange (AlgebraicClosure K)).IsSupersingularOver p

variable {p : ℕ} [Fact p.Prime] [CharP K p] {g : ℕ}

/-- An isomorphism supplies the required finite surjective morphism. -/
theorem IsSuperspecialOver.isSupersingularOver [IsAlgClosed K]
    {A : AbelianVariety K g} (h : A.IsSuperspecialOver p) :
    A.IsSupersingularOver p := by
  obtain ⟨E, hE, ⟨e⟩⟩ := h
  exact ⟨E, hE, e.hom, isIsogeny_of_isIso e.hom⟩

/-- Superspecial implies supersingular over every ground field. -/
theorem IsSuperspecial.isSupersingular {A : AbelianVariety K g}
    (h : A.IsSuperspecial p) : A.IsSupersingular p :=
  h.isSupersingularOver

theorem isSuperspecialOver_iff_of_iso [IsAlgClosed K]
    {A B : AbelianVariety K g} (e : A.group ≅ B.group) :
    A.IsSuperspecialOver p ↔ B.IsSuperspecialOver p := by
  constructor
  · rintro ⟨E, hE, ⟨f⟩⟩
    exact ⟨E, hE, ⟨e.symm ≪≫ f⟩⟩
  · rintro ⟨E, hE, ⟨f⟩⟩
    exact ⟨E, hE, ⟨e ≪≫ f⟩⟩

theorem isSupersingularOver_iff_of_iso [IsAlgClosed K]
    {A B : AbelianVariety K g} (e : A.group ≅ B.group) :
    A.IsSupersingularOver p ↔ B.IsSupersingularOver p := by
  constructor
  · rintro ⟨E, hE, f, hf⟩
    exact ⟨E, hE, e.inv ≫ f, (isIsogeny_of_isIso e.inv).comp hf⟩
  · rintro ⟨E, hE, f, hf⟩
    exact ⟨E, hE, e.hom ≫ f, (isIsogeny_of_isIso e.hom).comp hf⟩

/-- Supersingularity pulls back along an isogeny over an algebraically closed field. -/
theorem IsSupersingularOver.of_isogeny [IsAlgClosed K]
    {A B : AbelianVariety K g} (hB : B.IsSupersingularOver p)
    (f : A.group ⟶ B.group) (hf : IsIsogeny f) :
    A.IsSupersingularOver p := by
  obtain ⟨E, hE, h, hh⟩ := hB
  exact ⟨E, hE, f ≫ h, hf.comp hh⟩

theorem isSuperspecial_iff_of_iso {A B : AbelianVariety K g}
    (e : A.group ≅ B.group) : A.IsSuperspecial p ↔ B.IsSuperspecial p := by
  apply isSuperspecialOver_iff_of_iso
  exact ((Over.pullback (Spec.map
    (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))).mapGrp).mapIso e

theorem isSupersingular_iff_of_iso {A B : AbelianVariety K g}
    (e : A.group ≅ B.group) : A.IsSupersingular p ↔ B.IsSupersingular p := by
  apply isSupersingularOver_iff_of_iso
  exact ((Over.pullback (Spec.map
    (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))).mapGrp).mapIso e

/-- Scheme-group isomorphisms induce group isomorphisms on actual K-points. -/
def pointsMulEquiv {A B : AbelianVariety K g} (e : A.group ≅ B.group) :
    A.Points ≃* B.Points where
  toFun P := P ≫ e.hom.hom.hom
  invFun Q := Q ≫ e.inv.hom.hom
  left_inv P := by
    simp only [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom, Category.comp_id]
  right_inv Q := by
    simp only [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  map_mul' P Q := (IsMonHom.monoidHom e.hom.hom.hom _).map_mul P Q

theorem isSupersingularElliptic_iff_of_iso [IsAlgClosed K]
    {E E' : AbelianVariety K 1} (e : E.group ≅ E'.group) :
    E.IsSupersingularElliptic p ↔ E'.IsSupersingularElliptic p := by
  let q := pointsMulEquiv e
  constructor
  · intro h P hP
    apply q.symm.injective
    simpa using h (q.symm P) (by rw [← map_pow, hP, map_one])
  · intro h P hP
    apply q.injective
    simpa using h (q P) (by rw [← map_pow, hP, map_one])

/-- In dimension one the product-isomorphism definition recovers the usual
geometric p-torsion definition of a supersingular elliptic curve. -/
theorem isSuperspecialOver_iff_isSupersingularElliptic [IsAlgClosed K]
    (E : AbelianVariety K 1) :
    E.IsSuperspecialOver p ↔ E.IsSupersingularElliptic p := by
  constructor
  · rintro ⟨E', hE', ⟨e⟩⟩
    exact (isSupersingularElliptic_iff_of_iso
      (e ≪≫ productUniqueIso (fun i : Fin 1 => (E' i).group))).mpr (hE' _)
  · intro hE
    exact ⟨fun _ => E, fun _ => hE, ⟨(productUniqueIso (fun _ : Fin 1 => E.group)).symm⟩⟩

end AbelianVariety
end SupersingularCurves.Geometry
