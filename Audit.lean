import SupersingularCurves

set_option autoImplicit false
set_option maxHeartbeats 16000000

/- Checkpoint 13: actual local cotangents and infinitesimal Picard functoriality.
These declarations do not assert the Cartier--Verschiebung comparison. -/
#check SupersingularCurves.Geometry.Jacobian.infinitesimalPicardEquiv
#check SupersingularCurves.Geometry.Jacobian.infinitesimalPicardEquiv_pullback
#check SupersingularCurves.Geometry.Jacobian.Cotangent
#check SupersingularCurves.Geometry.Jacobian.finrank_cotangent
#check SupersingularCurves.Geometry.Jacobian.cotangentDeformationEquiv
#check SupersingularCurves.Geometry.Jacobian.pullbackCotangent
#check SupersingularCurves.Geometry.Jacobian.cotangentDeformationEquiv_pullback
#check SupersingularCurves.Geometry.Jacobian.pullbackCotangent_unique
#print axioms SupersingularCurves.Geometry.Jacobian.cotangentDeformationEquiv_pullback
#print axioms SupersingularCurves.Geometry.Jacobian.pullbackCotangent_unique

/- Checkpoint 14: actual relative Frobenius, and independent V over the prime field. -/
#check SupersingularCurves.Geometry.SchemeFrobenius.finite_flat_surjective
#check SupersingularCurves.Geometry.SchemeFrobenius.picardPullback_classify
#check SupersingularCurves.Geometry.PrimeFieldVerschiebung.existsUnique_verschiebung
#check SupersingularCurves.Geometry.PrimeFieldVerschiebung.frobenius_verschiebung
#check SupersingularCurves.Geometry.PrimeFieldVerschiebung.verschiebung_frobenius
#check SupersingularCurves.Geometry.PrimeFieldVerschiebung.verschiebung_mul
#check SupersingularCurves.Geometry.Jacobian.primeVerschiebungCotangent_action
#print axioms SupersingularCurves.Geometry.PrimeFieldVerschiebung.verschiebung_mul
#print axioms SupersingularCurves.Geometry.Jacobian.primeVerschiebungCotangent_action

/- Checkpoint 15: actual twists, perfect-field V, and Picard base change. -/
#check SupersingularCurves.Geometry.SchemeFrobenius.twistPointsEquiv
#check SupersingularCurves.Geometry.SchemeFrobenius.relative_mul
#check SupersingularCurves.Geometry.PerfectFieldVerschiebung.existsUnique_verschiebung
#print axioms SupersingularCurves.Geometry.PerfectFieldVerschiebung.multiplication_coequalizes
#print axioms SupersingularCurves.Geometry.PerfectFieldVerschiebung.verschiebung_frobenius
#print axioms SupersingularCurves.Geometry.PerfectFieldVerschiebung.verschiebung_mul
#print axioms SupersingularCurves.Geometry.PointedCotangent.differential_comp
#check SupersingularCurves.Geometry.Jacobian.verschiebungCotangent
#print axioms SupersingularCurves.Geometry.Jacobian.verschiebungCotangent_action
#print axioms SupersingularCurves.Geometry.SchemeFrobenius.twistRepresents
#print axioms SupersingularCurves.Geometry.SchemeFrobenius.twistRepresents_groupLaw
#check SupersingularCurves.Geometry.Jacobian.frobeniusPicardPullback
#check SupersingularCurves.Geometry.Jacobian.frobeniusPicardPullbackCotangent

/- Checkpoint 16: actual line-bundle Frobenius and Picard/V comparison. -/
#check SupersingularCurves.Geometry.FrobeniusLineBundle.sectionPower
#print axioms SupersingularCurves.Geometry.FrobeniusLineBundle.tensorPowSection_add
#print axioms SupersingularCurves.Geometry.FrobeniusLineBundle.pullbackIsoTensorPower
#print axioms SupersingularCurves.Geometry.FrobeniusLineBundle.pullbackIsoTensorPower_section
#print axioms SupersingularCurves.Geometry.SchemeFrobenius.productRelative_projection
#print axioms SupersingularCurves.Geometry.SchemeFrobenius.poincareFrobeniusCompositeIso
#print axioms SupersingularCurves.Geometry.SchemeFrobenius.frobenius_picardPullback
#check SupersingularCurves.Geometry.Jacobian.frobeniusPicardPullback_eq_verschiebung
#print axioms SupersingularCurves.Geometry.Jacobian.frobeniusPicardPullback_eq_verschiebung
#print axioms SupersingularCurves.Geometry.Jacobian.frobeniusPicardPullbackCotangent_eq_verschiebungCotangent

/- Checkpoint 17: the actual cotangent/dual-Cech-H1 comparison. -/
#check SupersingularCurves.Geometry.PicardCohomology.cotangentCechLinearEquiv
#print axioms SupersingularCurves.Geometry.InfinitesimalPicard.deformationCechEquiv
#print axioms SupersingularCurves.Geometry.InfinitesimalPicard.deformationCechEquiv_of_cocycle
#print axioms SupersingularCurves.Geometry.PicardCohomology.cotangentCechEquiv_map
#print axioms SupersingularCurves.Geometry.PicardCohomology.cotangent_finite
#print axioms SupersingularCurves.Geometry.PicardCohomology.cotangentDualCechEquiv
#print axioms SupersingularCurves.Geometry.PicardCohomology.cotangentDualCechEquiv_unique
#print axioms SupersingularCurves.Geometry.PicardCohomology.cotangentCechEquiv_pullback
#check SupersingularCurves.Geometry.Jacobian.twistedCotangentDualCechEquiv
#print axioms SupersingularCurves.Geometry.Jacobian.verschiebungCotangent_cech
#print axioms SupersingularCurves.Geometry.Jacobian.cotangentDualCechEquiv_frobeniusDeformation

/-! Check all project and imported FLT declarations by their module of origin. -/

run_cmd do
  let env ← Lean.getEnv
  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut project : Nat := 0
  let mut vendor : Nat := 0
  for (name, _) in env.constants.toList do
    let mod := match env.getModuleIdxFor? name with
      | none => Lean.Name.anonymous
      | some idx => env.header.moduleNames[idx.toNat]!
    let fromProject := (`SupersingularCurves).isPrefixOf mod ||
      (`SupersingularCurves).isPrefixOf name
    let fromVendor := (`Definitions).isPrefixOf mod || (`Theorems).isPrefixOf mod ||
      (`P2M.Sol).isPrefixOf mod
    if fromProject || fromVendor then
      if fromProject then project := project + 1
      if fromVendor then vendor := vendor + 1
      for ax in ← Lean.collectAxioms name do
        unless allowed.contains ax do
          throwError "Nonstandard axiom {ax} in {name} from module {mod}"
  unless project > 0 && vendor > 0 do
    throwError "Audit did not inspect both project and vendor declarations."
  Lean.logInfo m!"Origin-based axiom audit passed: {project} project declarations; {vendor} imported FLT declarations."

#print SupersingularCurves.Elliptic.IsSupersingular
#check SupersingularCurves.Elliptic.isSupersingular_iff_hasseInvariant_eq_zero
#check SupersingularCurves.Elliptic.isSupersingular_baseChange_iff
#check SupersingularCurves.Elliptic.legendre_isSupersingular_iff
#print axioms SupersingularCurves.Elliptic.legendre_isSupersingular_iff
#print axioms SupersingularCurves.Elliptic.hassePolynomial_separable
#check SupersingularCurves.IKO.familyA_separable
#check SupersingularCurves.IKO.coefficientMatrix_familyA_mod_six_one
#check SupersingularCurves.IKO.coefficientMatrix_familyA_mod_six_five
#check SupersingularCurves.IKO.semilinearAction_square_zero_iff
#print axioms SupersingularCurves.IKO.coefficientMatrix_familyB_five_zero_iff
#print axioms SupersingularCurves.IKO.x_fifth_sub_one_three_matrix_distinction

/- Checkpoint 2: uniform formulas and matrix criteria, including private dependencies. -/
#check SupersingularCurves.IKO.coeff_quadratic_power_high
#check SupersingularCurves.IKO.coeff_quadratic_power_low
#check SupersingularCurves.IKO.coefficientMatrix_familyA_formula_one
#check SupersingularCurves.IKO.coefficientMatrix_familyA_formula_five
#check SupersingularCurves.IKO.coefficientMatrix_familyB_formula_one
#check SupersingularCurves.IKO.coefficientMatrix_familyB_formula_three
#check SupersingularCurves.IKO.coefficientMatrix_familyA_zero_iff
#check SupersingularCurves.IKO.coefficientMatrix_familyB_zero_iff
#check SupersingularCurves.IKO.coefficientMatrix_familyA_det_ne_zero_iff
#check SupersingularCurves.IKO.coefficientMatrix_familyB_det_ne_zero_iff
#check SupersingularCurves.IKO.coefficientMatrix_familyA_frobenius_square_zero_iff
#check SupersingularCurves.IKO.coefficientMatrix_familyB_frobenius_square_zero_iff
#print axioms SupersingularCurves.IKO.coefficientMatrix_familyA_frobenius_square_zero_iff
#print axioms SupersingularCurves.IKO.coefficientMatrix_familyB_frobenius_square_zero_iff

/- Checkpoint 3: actual Cartier and compatibility, including all reused dependencies. -/
#check SupersingularCurves.Differentials.existsUnique_cartier
#check SupersingularCurves.Differentials.cartier_mem_regularDifferentials
#check SupersingularCurves.Differentials.cartier_dx_div_y_two_coefficients
#check SupersingularCurves.Differentials.cartier_x_dx_div_y_two_coefficients
#check SupersingularCurves.IKO.differentialCombination_injective
#check SupersingularCurves.IKO.cartier_differentialCombination
#check SupersingularCurves.IKO.cartier_differentialSpan_square_zero_iff
#check SupersingularCurves.IKO.familyA_cartier_zero_iff
#check SupersingularCurves.IKO.familyB_cartier_zero_iff
#check SupersingularCurves.IKO.familyA_cartier_square_zero_iff
#check SupersingularCurves.IKO.familyB_cartier_square_zero_iff
#check SupersingularCurves.IKO.x_fifth_sub_one_three_cartier_distinction
#print axioms SupersingularCurves.Differentials.cartier_dx_div_y_two_coefficients
#print axioms SupersingularCurves.Differentials.cartier_x_dx_div_y_two_coefficients
#print axioms SupersingularCurves.IKO.cartier_differentialCombination
#print axioms SupersingularCurves.IKO.familyA_cartier_square_zero_iff
#print axioms SupersingularCurves.IKO.familyB_cartier_square_zero_iff
#print axioms SupersingularCurves.IKO.x_fifth_sub_one_three_cartier_distinction

/- Checkpoint 4: explicit fields, all-place regularity, and regular Cartier coordinates. -/
#check SupersingularCurves.Hyperelliptic.SimpleRootModel.irreducible_equation
#check SupersingularCurves.Hyperelliptic.SimpleRootModel.equation_in_functionField
#check SupersingularCurves.Hyperelliptic.SimpleRootModel.finrank_functionField
#check SupersingularCurves.Hyperelliptic.SimpleRootModel.dx_ne_zero
#check SupersingularCurves.Differentials.regularAt_dx_div_y_of_integral
#check SupersingularCurves.Differentials.hyperelliptic_pair_mem_regularDifferentials
#check SupersingularCurves.IKO.familyAModel_pair_regular
#check SupersingularCurves.IKO.familyBModel_pair_regular
#check SupersingularCurves.IKO.familyARegularCoordinates_finrank_range
#check SupersingularCurves.IKO.familyBRegularCoordinates_finrank_range
#check SupersingularCurves.IKO.familyA_regularCartier_action
#check SupersingularCurves.IKO.familyB_regularCartier_action
#check SupersingularCurves.IKO.familyA_regularCartier_zero_iff
#check SupersingularCurves.IKO.familyB_regularCartier_square_zero_iff
#print axioms SupersingularCurves.IKO.familyAModel_pair_regular
#print axioms SupersingularCurves.IKO.familyBModel_pair_regular
#print axioms SupersingularCurves.IKO.familyARegularCoordinates_finrank_range
#print axioms SupersingularCurves.IKO.familyA_regularCartier_zero_iff
#print axioms SupersingularCurves.IKO.familyB_regularCartier_square_zero_iff

/- A finite ground field is permitted; the definition still uses geometric points. -/
example : SupersingularCurves.Elliptic.IsSupersingular 3
    (WeierstrassCurve.legendreCurve (-1 : ZMod 3)) :=
  SupersingularCurves.Elliptic.legendre_neg_one_supersingular_char_three

/- A nonsupersingular elliptic example checks that the predicate is nonvacuous. -/
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

example : ¬ SupersingularCurves.Elliptic.IsSupersingular 5
    (WeierstrassCurve.legendreCurve (2 : ZMod 5)) := by
  rw [SupersingularCurves.Elliptic.legendre_isSupersingular_iff 5
    (by decide) 2 (by decide) (by decide)]
  norm_num [SupersingularCurves.Elliptic.hassePolynomial,
    Polynomial.deuringPolynomial, Finset.sum_range_succ]
  decide

/- Actual quadratic fields and actual regular forms: a root and a nonroot case. -/
local instance : NeZero (2 : ZMod 5) := ⟨by decide⟩
local instance : NeZero (2 : ZMod 3) := ⟨by decide⟩
open SupersingularCurves.IKO SupersingularCurves.Differentials in
example (v : Fin 2 → ZMod 5) :
    regularCartier 5 (familyAModel (4 : ZMod 5) (of_decide_eq_true rfl) (of_decide_eq_true rfl)).x
      (familyARegularCoordinates (4 : ZMod 5) (of_decide_eq_true rfl) (of_decide_eq_true rfl) (of_decide_eq_true rfl) v) = 0 := by
  have hz := (familyA_regularCartier_zero_iff 5 (of_decide_eq_true rfl)
    (4 : ZMod 5) (of_decide_eq_true rfl) (of_decide_eq_true rfl) (of_decide_eq_true rfl)).mpr
      (by norm_num [gPolynomial_five]; decide)
  exact hz v

open SupersingularCurves.IKO SupersingularCurves.Differentials in
example : ¬ ∀ v : Fin 2 → ZMod 3,
    regularCartier 3 (familyBModel (2 : ZMod 3) (of_decide_eq_true rfl)).x
      (familyBRegularCoordinates (2 : ZMod 3) (of_decide_eq_true rfl) (of_decide_eq_true rfl) (of_decide_eq_true rfl) v) = 0 := by
  rw [familyB_regularCartier_zero_iff 3 (of_decide_eq_true rfl) (2 : ZMod 3) (of_decide_eq_true rfl) (of_decide_eq_true rfl)]
  simp [hPolynomial_three]

/- Checkpoint 5: actual ramification, genus, full bases, and whole-space Cartier. -/
#check SupersingularCurves.Hyperelliptic.SimpleRootModel.total_ramification
#check SupersingularCurves.Hyperelliptic.SimpleRootModel.genus_eq_two
#check SupersingularCurves.Hyperelliptic.SimpleRootModel.finite_and_finrank_regularDifferentials
#check SupersingularCurves.IKO.familyARegularCoordinates_bijective
#check SupersingularCurves.IKO.familyBRegularCoordinates_bijective
#check SupersingularCurves.IKO.familyARegularBasis
#check SupersingularCurves.IKO.familyBRegularBasis
#check SupersingularCurves.IKO.familyA_regularCartier_coordinates
#check SupersingularCurves.IKO.familyB_regularCartier_coordinates
#check SupersingularCurves.IKO.familyA_all_regularCartier_zero_iff
#check SupersingularCurves.IKO.familyB_all_regularCartier_square_zero_iff
#print axioms SupersingularCurves.Hyperelliptic.SimpleRootModel.total_ramification
#print axioms SupersingularCurves.Hyperelliptic.SimpleRootModel.genus_eq_two
#print axioms SupersingularCurves.Hyperelliptic.SimpleRootModel.finite_and_finrank_regularDifferentials
#print axioms SupersingularCurves.IKO.familyARegularCoordinates_bijective
#print axioms SupersingularCurves.IKO.familyBRegularCoordinates_bijective
#print axioms SupersingularCurves.IKO.familyA_all_regularCartier_zero_iff
#print axioms SupersingularCurves.IKO.familyB_all_regularCartier_square_zero_iff

/- Checkpoint 6: actual Picard p-torsion and the logarithmic equivalence. -/
#check SupersingularCurves.PicardTorsion.toRegularFixed_surjective
#check SupersingularCurves.PicardTorsion.logarithmEquiv
#check SupersingularCurves.IKO.card_scalarRoots
#check SupersingularCurves.IKO.card_fixedVectors_antidiagonal
#check SupersingularCurves.IKO.familyATorsionEquiv
#check SupersingularCurves.IKO.familyBTorsionEquiv
#check SupersingularCurves.IKO.card_familyA_torsion
#check SupersingularCurves.IKO.card_familyB_torsion
#check SupersingularCurves.IKO.familyA_torsion_finite
#check SupersingularCurves.IKO.familyB_torsion_finite
#check SupersingularCurves.IKO.familyA_torsion_eq_zero_iff
#check SupersingularCurves.IKO.familyB_torsion_eq_zero_iff_regularCartier_zero
#print axioms SupersingularCurves.PicardTorsion.logarithmEquiv
#print axioms SupersingularCurves.IKO.card_familyA_torsion
#print axioms SupersingularCurves.IKO.card_familyB_torsion
#print axioms SupersingularCurves.IKO.familyA_torsion_eq_zero_iff_regularCartier_zero
#print axioms SupersingularCurves.IKO.familyB_torsion_eq_zero_iff_regularCartier_zero

/- Checkpoint 7: genuine group-scheme predicates, representing Jacobians, and Newton polygons. -/
#print SupersingularCurves.Geometry.IsIsogeny
#print SupersingularCurves.Geometry.AbelianVariety.IsSuperspecialOver
#print SupersingularCurves.Geometry.AbelianVariety.IsSupersingularOver
#print SupersingularCurves.Geometry.AbelianVariety.IsSuperspecial
#check SupersingularCurves.Geometry.AbelianVariety.baseChange
#check SupersingularCurves.Geometry.Jacobian
#check SupersingularCurves.Geometry.Jacobian.abelianVariety
#check SupersingularCurves.Geometry.CurveModel.IsSuperspecial
#check SupersingularCurves.Geometry.CurveModel.IsSupersingular
#print axioms SupersingularCurves.Geometry.AbelianVariety.IsSuperspecial.isSupersingular
#print axioms SupersingularCurves.Geometry.AbelianVariety.isSuperspecial_iff_of_iso
#print axioms SupersingularCurves.Geometry.AbelianVariety.isSupersingular_iff_of_iso
#print axioms SupersingularCurves.Geometry.AbelianVariety.isSuperspecialOver_iff_isSupersingularElliptic
#print axioms SupersingularCurves.Geometry.Jacobian.abelianVariety
#print axioms SupersingularCurves.Geometry.CurveModel.IsSuperspecial.isSupersingular
#print SupersingularCurves.NewtonPolygon.ofPolynomial
#print SupersingularCurves.NewtonPolygon.padic
#check SupersingularCurves.NewtonPolygon.ofEndomorphism
#print axioms SupersingularCurves.NewtonPolygon.lowerBoundary_vertical_unique
#print axioms SupersingularCurves.NewtonPolygon.padic_binomial_supersingular
#print axioms SupersingularCurves.NewtonPolygon.supersingular_half_slope
#print axioms SupersingularCurves.NewtonPolygon.ofEndomorphism_conj
#print axioms SupersingularCurves.NewtonPolygon.halfSlopeEndomorphism_newton
#print axioms SupersingularCurves.NewtonPolygon.genus_five_polynomial_newton
#print axioms SupersingularCurves.NewtonPolygon.ordinary_three_not_supersingular

/- Normalization is checked beyond the prime field; these are polynomial examples. -/
example : SupersingularCurves.NewtonPolygon.padic 3 2
    (1 + Polynomial.C (3 ^ 4 : ℚ) * Polynomial.X ^ 4) =
    SupersingularCurves.NewtonPolygon.supersingular 2 := by
  simpa using SupersingularCurves.NewtonPolygon.padic_binomial_supersingular 3 2
    (g := 2) (by decide)

/- Checkpoint 8: actual smooth proper curve models and Witt-vector F-isocrystals. -/
#check SupersingularCurves.Hyperelliptic.SimpleRootModel.curveModel
#check SupersingularCurves.Hyperelliptic.SimpleRootModel.curveModelBasepoint
#print axioms SupersingularCurves.Hyperelliptic.SimpleRootModel.curveModel_equation
#print axioms SupersingularCurves.IKO.familyA_pointed_curve
#print axioms SupersingularCurves.IKO.familyB_pointed_curve
#print SupersingularCurves.NewtonPolygon.ofIsocrystal
#check SupersingularCurves.NewtonPolygon.frobeniusPower
#print axioms SupersingularCurves.NewtonPolygon.wittValuation_prime
#print axioms SupersingularCurves.NewtonPolygon.fractionFrobenius_pow_eq_one
#print axioms SupersingularCurves.NewtonPolygon.ofIsocrystal_eq_of_equiv
#print axioms SupersingularCurves.NewtonPolygon.halfSlopeIsocrystal
#print axioms SupersingularCurves.NewtonPolygon.halfSlope_frobeniusPower_charpoly
#print axioms SupersingularCurves.NewtonPolygon.halfSlope_newton

/- Checkpoint 9: genuine Jacobians, their point groups, and global curve forms. -/
#check SupersingularCurves.Geometry.JacobianRealization
#print axioms SupersingularCurves.Geometry.jacobianRealization_nonempty
#print axioms SupersingularCurves.Geometry.Jacobian.picardPointsAddEquiv
#print axioms SupersingularCurves.Geometry.picardTorsionPointsEquiv
#print axioms SupersingularCurves.IKO.familyAJacobian
#print axioms SupersingularCurves.IKO.familyBJacobian
#print axioms SupersingularCurves.IKO.card_familyAJacobian_torsion
#print axioms SupersingularCurves.IKO.familyBJacobian_ordinary_iff
#print axioms SupersingularCurves.Geometry.DifferentialChart.regularEquiv_generic_restriction
#print axioms SupersingularCurves.IKO.familyAGlobalBasis_restrict
#print axioms SupersingularCurves.IKO.familyB_globalCartier_coordinates
#print axioms SupersingularCurves.IKO.familyA_all_globalCartier_square_zero_iff

/- Checkpoint 10: IKO's main differential-equation proof of Proposition 1.14. -/
#check SupersingularCurves.IKO.not_isRoot_derivative_of_hypergeometric
#print axioms SupersingularCurves.IKO.separable_of_hypergeometric
#print axioms SupersingularCurves.IKO.binomialPolynomial_separable
#print axioms SupersingularCurves.IKO.gPolynomial_separable
#print axioms SupersingularCurves.IKO.hPolynomial_separable
#print axioms SupersingularCurves.IKO.gPolynomial_root_admissible
#print axioms SupersingularCurves.IKO.hPolynomial_root_admissible
#print axioms SupersingularCurves.IKO.card_roots_gPolynomial
#print axioms SupersingularCurves.IKO.card_roots_hPolynomial
#print axioms SupersingularCurves.IKO.gPolynomial_equation_mod_six_one
#print axioms SupersingularCurves.IKO.gPolynomial_equation_mod_six_five
#print axioms SupersingularCurves.IKO.hPolynomial_equation_mod_four_one
#print axioms SupersingularCurves.IKO.hPolynomial_equation_mod_four_three

/- Checkpoint 11: actual geometric superspeciality imposes the Cartier/root condition. -/
#print axioms SupersingularCurves.Geometry.AbelianVariety.pointsBaseChange_injective
#print axioms SupersingularCurves.Geometry.AbelianVariety.IsSuperspecial.torsion_trivial
#print axioms SupersingularCurves.Geometry.AbelianVariety.IsSuperspecial.hasPRankOver_zero
#print axioms SupersingularCurves.Geometry.Jacobian.picardPoints_nonempty
#print axioms SupersingularCurves.Geometry.Jacobian.hasPRankOver_iff
#print axioms SupersingularCurves.Geometry.CurveModel.IsSuperspecial.hasPRankOver_zero
#print axioms SupersingularCurves.IKO.familyA_isSuperspecial_imp_root
#print axioms SupersingularCurves.IKO.familyB_isSuperspecial_imp_globalCartier_zero
#print axioms SupersingularCurves.IKO.familyB_not_isSuperspecial_char_three
#print axioms SupersingularCurves.IKO.ncard_familyASuperspecialParameters_le
#print axioms SupersingularCurves.IKO.ncard_familyBSuperspecialParameters_le

/- Checkpoint 12: all presented separable quintic/sextic genus-two models. -/
#print axioms SupersingularCurves.Hyperelliptic.reflect_six_separable
#print axioms SupersingularCurves.Hyperelliptic.quintic_sextic_pair_regular
#print axioms SupersingularCurves.Hyperelliptic.modelOfSeparable
#print axioms SupersingularCurves.Hyperelliptic.SimpleRootModel.regularCoordinates_bijective
#print axioms SupersingularCurves.Hyperelliptic.SimpleRootModel.regularBasis
#print axioms SupersingularCurves.Hyperelliptic.SimpleRootModel.all_regularCartier_square_zero_iff
#print axioms SupersingularCurves.Hyperelliptic.SimpleRootModel.globalCartier_coordinates
#print axioms SupersingularCurves.Hyperelliptic.SimpleRootModel.all_globalCartier_zero_iff
#print axioms SupersingularCurves.Hyperelliptic.SimpleRootModel.jacobian_hasPRankOver_zero_of_matrix
#print axioms SupersingularCurves.Hyperelliptic.CharacteristicThree.genus_eq_two
#print axioms SupersingularCurves.Hyperelliptic.CharacteristicThree.global_cartier_distinction
#print axioms SupersingularCurves.Hyperelliptic.CharacteristicThree.jacobian_hasPRankOver_zero
