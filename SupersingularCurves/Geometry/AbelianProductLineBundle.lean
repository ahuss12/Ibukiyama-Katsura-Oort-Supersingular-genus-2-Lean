/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FiniteBySectionsExternalProduct
import SupersingularCurves.Geometry.AbelianVarietyProductMaps

/-!
# Actual line bundles finite by sections on an abelian product

The exterior tensor product is formed using the actual product projections.
Invertibility and a finite projective presentation are constructed from those
of the factors, using Segre's projective map.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SupersingularCurves.Geometry.AbelianTate
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry GoodReductionJacobian
variable {K : Type} [Field K] {g h : ℕ}

/-- The actual exterior tensor product on the actual abelian product. -/
def productLineBundle (A : AbelianVariety K g) (B : AbelianVariety K h)
    (M : A.group.X.left.Modules) (N : B.group.X.left.Modules) : (A.prod B).group.X.left.Modules :=
  (Scheme.Modules.pullback (A.prodFst B).hom.hom.left).obj M ⊗
    (Scheme.Modules.pullback (A.prodSnd B).hom.hom.left).obj N

theorem productLineBundle_isInvertible (A : AbelianVariety K g) (B : AbelianVariety K h)
    (M : A.group.X.left.Modules) (N : B.group.X.left.Modules)
    (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N) :
    Scheme.Modules.IsInvertible (productLineBundle A B M N) :=
  (hM.pullback (A.prodFst B).hom.hom.left).tensor (hN.pullback (A.prodSnd B).hom.hom.left)

/-- The product polarization is finite by sections by an actual Segre
construction on the finite projective presentations of the factors. -/
theorem productLineBundle_finiteBySections (A : AbelianVariety K g) (B : AbelianVariety K h)
    (M : A.group.X.left.Modules) (N : B.group.X.left.Modules)
    (hM : M.FiniteBySections A.group.X.hom) (hN : N.FiniteBySections B.group.X.hom) :
    (productLineBundle A B M N).FiniteBySections (A.prod B).group.X.hom :=
  finiteBySections_externalProduct A.group.X.hom B.group.X.hom M N hM hN

end SupersingularCurves.Geometry.AbelianTate
