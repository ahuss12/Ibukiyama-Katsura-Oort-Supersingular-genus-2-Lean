import SupersingularCurves.Geometry.JacobianIsogenyTorsion
import SupersingularCurves.Geometry.SupersingularGeometryTorsion
import SupersingularCurves.Geometry.SupersingularJacobian
import SupersingularCurves.Hyperelliptic.GenusTwoSupersingular
import SupersingularCurves.IKO.SupersingularObstructions

set_option autoImplicit false
set_option maxHeartbeats 0

/- Audit all new project and pinned vendor module declaration tables, including
private/generated entries and stored types/bodies. Retained modules have
unchanged source hashes and prior audits; new dependencies are checked transitively. -/
run_cmd do
  let env ← Lean.getEnv
  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
  let modules : Array Lean.Name := #[
    `SupersingularCurves.Geometry.JacobianIsogenyTorsion,
    `SupersingularCurves.Geometry.SupersingularGeometryTorsion,
    `SupersingularCurves.Geometry.SupersingularJacobian,
    `SupersingularCurves.Hyperelliptic.GenusTwoSupersingular,
    `SupersingularCurves.IKO.SupersingularObstructions,
    `Definitions.Def_AlgebraicCurve_Pic0Congr,
    `Definitions.Def_AlgebraicGeometry_Kmf2FiberSpecTensorStalkLeg1AffineDatum,
    `Definitions.Def_AlgebraicGeometry_KwFrobSemilinearFixedPointFiniteEngine,
    `Definitions.Def_AlgebraicGeometry_SchemeFibreEndo,
    `Definitions.Def_Mathlib_RingTheory_KmfloorsGlueFiberLocalizationQuotientEngine,
    `P2M.Sol.S_AlgHom_injective_of_finite_of_isFractionRing,
    `P2M.Sol.S_Algebra_trdeg_quotient_lt,
    `P2M.Sol.S_AlgebraicCurve_KwPke_kw_pke_hsep_of_isSeparable_adjoin,
    `P2M.Sol.S_AlgebraicCurve_Pic0_exists_injective_addMonoidHom_torsion_dlog,
    `P2M.Sol.S_AlgebraicCurve_Pic0_exists_nsmul_eq_of_charP,
    `P2M.Sol.S_AlgebraicCurve_Pic0_exists_relativeGroupLaw_equiv_of_curveModel,
    `P2M.Sol.S_AlgebraicCurve_Pic0_finite_torsion_char,
    `P2M.Sol.S_AlgebraicCurve_Pic0_finite_torsion_pow_char,
    `P2M.Sol.S_AlgebraicCurve_Place_exists_comap_eq_toValuationSubring,
    `P2M.Sol.S_AlgebraicCurve_Place_exists_ord_algebraMap_eq_mul_ord,
    `P2M.Sol.S_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed,
    `P2M.Sol.S_AlgebraicCurve_dlog_mem_regularDifferentials_of_forall_dvd_ord,
    `P2M.Sol.S_AlgebraicCurve_isCurveOver_iff_exists_transcendental_finiteDimensional,
    `P2M.Sol.S_AlgebraicGeometry_IsFinite_ringKrullDim_stalk_quotient_eq_zero,
    `P2M.Sol.S_AlgebraicGeometry_LocallyQuasiFinite_of_formallyUnramified_of_locallyOfFiniteType,
    `P2M.Sol.S_AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk,
    `P2M.Sol.S_AlgebraicGeometry_locallyQuasiFinite_of_forall_locallyQuasiFinite_schemeFibreEndo,
    `P2M.Sol.S_AlgebraicGeometry_ringKrullDim_stalk_eq_of_isFinite_endomorphism,
    `P2M.Sol.S_GoodReductionJacobian_AbelianSchemePropertyBundle_isIntegral_of_field,
    `P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_eq_one_of_sqZero_of_nsmul_eq_one_of_isUnit,
    `P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_fibre_mul_comm,
    `P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_fibre_schemeNsmul_eq_schemeFibreEndo,
    `P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_isFinite_of_abelianSchemePropertyBundle,
    `P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_isFinite_of_field,
    `P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_forall_sqZero,
    `P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul_of_isUnit,
    `P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_schemeNsmul_of_finite_torsionSubset,
    `P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_schemeNsmul_of_isUnit,
    `P2M.Sol.S_GoodReductionJacobian_abelianSchemePropertyBundle_fibreStr,
    `P2M.Sol.S_Ideal_height_eq_height_under_of_finiteType_of_isIntegral,
    `P2M.Sol.S_Ideal_height_eq_height_under_of_isIntegrallyClosed_of_isIntegral,
    `P2M.Sol.S_IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map_univ,
    `P2M.Sol.S_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero_univ,
    `P2M.Sol.S_Submodule_finite_torsionBy_pow_of_finite_torsionBy,
    `Theorems.Thm_AlgHom_injective_of_finite_of_isFractionRing,
    `Theorems.Thm_Algebra_trdeg_quotient_lt,
    `Theorems.Thm_AlgebraicCurve_KwPke_kw_pke_hsep_of_isSeparable_adjoin,
    `Theorems.Thm_AlgebraicCurve_Pic0_exists_injective_addMonoidHom_torsion_dlog,
    `Theorems.Thm_AlgebraicCurve_Pic0_exists_nsmul_eq_of_charP,
    `Theorems.Thm_AlgebraicCurve_Pic0_exists_relativeGroupLaw_equiv_of_curveModel,
    `Theorems.Thm_AlgebraicCurve_Pic0_finite_torsion_char,
    `Theorems.Thm_AlgebraicCurve_Pic0_finite_torsion_pow_char,
    `Theorems.Thm_AlgebraicCurve_Place_exists_comap_eq_toValuationSubring,
    `Theorems.Thm_AlgebraicCurve_Place_exists_ord_algebraMap_eq_mul_ord,
    `Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed,
    `Theorems.Thm_AlgebraicCurve_dlog_mem_regularDifferentials_of_forall_dvd_ord,
    `Theorems.Thm_AlgebraicCurve_isCurveOver_iff_exists_transcendental_finiteDimensional,
    `Theorems.Thm_AlgebraicGeometry_IsFinite_ringKrullDim_stalk_quotient_eq_zero,
    `Theorems.Thm_AlgebraicGeometry_LocallyQuasiFinite_of_formallyUnramified_of_locallyOfFiniteType,
    `Theorems.Thm_AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk,
    `Theorems.Thm_AlgebraicGeometry_locallyQuasiFinite_of_forall_locallyQuasiFinite_schemeFibreEndo,
    `Theorems.Thm_AlgebraicGeometry_ringKrullDim_stalk_eq_of_isFinite_endomorphism,
    `Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_isIntegral_of_field,
    `Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_one_of_sqZero_of_nsmul_eq_one_of_isUnit,
    `Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_fibre_mul_comm,
    `Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_fibre_schemeNsmul_eq_schemeFibreEndo,
    `Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_isFinite_of_abelianSchemePropertyBundle,
    `Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_isFinite_of_field,
    `Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_forall_sqZero,
    `Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul_of_isUnit,
    `Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_schemeNsmul_of_finite_torsionSubset,
    `Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_schemeNsmul_of_isUnit,
    `Theorems.Thm_GoodReductionJacobian_abelianSchemePropertyBundle_fibreStr,
    `Theorems.Thm_Ideal_height_eq_height_under_of_finiteType_of_isIntegral,
    `Theorems.Thm_Ideal_height_eq_height_under_of_isIntegrallyClosed_of_isIntegral,
    `Theorems.Thm_IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map_univ,
    `Theorems.Thm_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero_univ,
    `Theorems.Thm_Submodule_finite_torsionBy_pow_of_finite_torsionBy]
  let mut counts : Array Nat := Array.replicate modules.size 0
  let mut sharedEntries : Nat := 0
  for j in [:env.header.moduleNames.size] do
    let mod := env.header.moduleNames[j]!
    if modules.contains mod then
      let data := env.header.moduleData[j]!
      unless data.constNames == data.constants.map (·.name) do
        throwError "Inconsistent declaration table for {mod}"
      for info in data.constants do
        let name := info.name
        unless (env.checked.get.find? name).isSome do
          throwError "Missing checked declaration {name} from module {mod}"
        let origin := match env.getModuleIdxFor? name with
          | none => Lean.Name.anonymous
          | some idx => env.header.moduleNames[idx.toNat]!
        if origin != mod then sharedEntries := sharedEntries + 1
        if info.isAxiom && !allowed.contains name then
          throwError "Nonstandard axiom declaration {name} in {mod}"
        for i in [:modules.size] do
          if mod == modules[i]! then counts := counts.set! i (counts[i]! + 1)
        for ax in ← Lean.collectAxioms name do
          unless allowed.contains ax do
            throwError "Nonstandard axiom {ax} in {name} from module {mod}"
        let deps := info.type.getUsedConstants ++
          ((info.value? true).map (·.getUsedConstants)).getD #[]
        for dep in deps do
          unless (env.checked.get.find? dep).isSome do
            throwError "Missing dependency {dep} of {name} in {mod}"
          for ax in ← Lean.collectAxioms dep do
            unless allowed.contains ax do
              throwError "Nonstandard axiom {ax} in stored declaration {name} from {mod}"
  for i in [:modules.size] do
    unless counts[i]! > 0 do
      throwError "No declarations inspected in module {modules[i]!}"
    Lean.logInfo m!"Audited {counts[i]!} declarations from {modules[i]!}."
  Lean.logInfo m!"Inspected {sharedEntries} shared generated entries by stored type/body as well as resolved declaration."
  Lean.logInfo m!"Checkpoint 22 transitive axiom audit passed: {counts.foldl (· + ·) 0} new project/vendor declaration entries."
