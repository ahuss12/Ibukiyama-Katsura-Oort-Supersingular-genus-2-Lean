import SupersingularCurves.Geometry.PointedCotangent

/-!
# Cotangent spaces of actual kernels

Monomorphisms induce surjective cotangent maps at rational points. Consequently,
the cotangent space of an actual kernel vanishes when the ambient differential
is surjective. All maps here are morphisms of the given pointed schemes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.PointedCotangent

open CategoryTheory AlgebraicGeometry NeronModelInfra

variable {K : Type u} [Field K]
variable {X Y Z : Scheme.{u}}
variable (c : X ⟶ Spec (CommRingCat.of K))
  (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
variable {d : Y ⟶ Spec (CommRingCat.of K)}
  {z : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) d}
variable (f : X ⟶ Y) (hf : f ≫ d = c) (hs : s.1 ≫ f = z.1)

/-- A genuine scheme monomorphism induces a surjection on cotangent spaces. -/
theorem differential_surjective_of_mono [Mono f] :
    Function.Surjective (differential c s f hf hs) := by
  apply LinearMap.dualMap_injective_iff.mp
  intro l m h
  apply (pointsEquiv c s K).injective
  apply TangentPoints.ext
  apply (cancel_mono f).mp
  change l ∘ₗ differential c s f hf hs = m ∘ₗ differential c s f hf hs at h
  have hh := congrArg (pointsEquiv d z K) h
  rw [differential_action, differential_action] at hh
  exact congrArg Subtype.val hh

local instance kernelCotangentOppositeModule : Module Kᵐᵒᵖ (Cotangent c s) :=
  Module.compHom _ (RingEquiv.toOpposite K).symm.toRingHom

local instance kernelCotangentCentralScalar : IsCentralScalar K (Cotangent c s) :=
  ⟨fun _ _ => rfl⟩

/-- The actual constant morphism through a rational point has zero differential. -/
theorem differential_eq_zero_of_eq_constant (hconst : f = c ≫ z.1) :
    differential c s f hf hs = 0 := by
  let V := Cotangent c s
  let t := pointsEquiv c s V LinearMap.id
  let t₀ := pointsEquiv c s V 0
  have heq : mapPoint c s f hf hs t = mapPoint c s f hf hs t₀ := by
    apply TangentPoints.ext
    change t.1 ≫ f = t₀.1 ≫ f
    rw [hconst, ← Category.assoc, ← Category.assoc, t.2.1, t₀.2.1]
  apply (pointsEquiv d z V).injective
  have h₁ := differential_action c s f hf hs (LinearMap.id : V →ₗ[K] V)
  have h₀ := differential_action c s f hf hs (0 : V →ₗ[K] V)
  rw [LinearMap.id_comp] at h₁
  rw [LinearMap.zero_comp] at h₀
  exact h₁.trans (heq.trans h₀.symm)

variable {e : Z ⟶ Spec (CommRingCat.of K)}
  {w : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) e}

include hf hs in
/-- If a monomorphism lands in the actual fibre of a pointed map whose cotangent
differential is surjective, its source has zero cotangent space. -/
theorem cotangent_subsingleton_of_mono_comp_eq_constant [Mono f]
    (g : Y ⟶ Z) (hg : g ≫ e = d) (hz : z.1 ≫ g = w.1)
    (hconst : f ≫ g = c ≫ w.1)
    (hsurj : Function.Surjective (differential d z g hg hz)) :
    Subsingleton (Cotangent c s) := by
  have hcomp := differential_eq_zero_of_eq_constant c s (f ≫ g)
    (by rw [Category.assoc, hg, hf]) (by rw [← Category.assoc, hs, hz]) hconst
  rw [differential_comp c s f hf hs g hg hz] at hcomp
  have hzero : differential c s f hf hs = 0 := by
    ext x
    obtain ⟨y, rfl⟩ := hsurj x
    exact LinearMap.congr_fun hcomp y
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨y, rfl⟩ := differential_surjective_of_mono c s f hf hs x
  exact LinearMap.congr_fun hzero y

end SupersingularCurves.Geometry.PointedCotangent
