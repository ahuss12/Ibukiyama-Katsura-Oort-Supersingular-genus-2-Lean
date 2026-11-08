import SupersingularCurves.Geometry.CotangentDifferentialKernel
import SupersingularCurves.Geometry.FrobeniusCotangentVanishing
import SupersingularCurves.Geometry.FrobeniusFactorGroup
import SupersingularCurves.Geometry.FrobeniusFactorIsomorphism
import SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup
import SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroupDimension
import SupersingularCurves.Geometry.LocalizedDifferentialDetection
import SupersingularCurves.Geometry.PRankZeroFiniteSubgroup
import SupersingularCurves.Geometry.PRankZeroVerschiebungKernel
import SupersingularCurves.Geometry.PointedCotangentFibre
import SupersingularCurves.Geometry.PointedCotangentFibreExact
import SupersingularCurves.Geometry.RationalCotangentFrobenius
import SupersingularCurves.Geometry.ReducedModuleDetection
import SupersingularCurves.Geometry.SmoothDifferentialDetection
import SupersingularCurves.Geometry.VerschiebungFrobeniusCriterion
import SupersingularCurves.Hyperelliptic.CharacteristicThreeObstruction
import SupersingularCurves.Hyperelliptic.GenusTwoFiniteSubgroup
import SupersingularCurves.Hyperelliptic.GenusTwoFrobeniusIsomorphism

set_option autoImplicit false
set_option maxHeartbeats 0

run_cmd do
  let env ← Lean.getEnv
  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
  let modules : Array Lean.Name := #[
    `SupersingularCurves.Geometry.CotangentDifferentialKernel,
    `SupersingularCurves.Geometry.FrobeniusCotangentVanishing,
    `SupersingularCurves.Geometry.FrobeniusFactorGroup,
    `SupersingularCurves.Geometry.FrobeniusFactorIsomorphism,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroupDimension,
    `SupersingularCurves.Geometry.LocalizedDifferentialDetection,
    `SupersingularCurves.Geometry.PRankZeroFiniteSubgroup,
    `SupersingularCurves.Geometry.PRankZeroVerschiebungKernel,
    `SupersingularCurves.Geometry.PointedCotangentFibre,
    `SupersingularCurves.Geometry.PointedCotangentFibreExact,
    `SupersingularCurves.Geometry.RationalCotangentFrobenius,
    `SupersingularCurves.Geometry.ReducedModuleDetection,
    `SupersingularCurves.Geometry.SmoothDifferentialDetection,
    `SupersingularCurves.Geometry.VerschiebungFrobeniusCriterion,
    `SupersingularCurves.Hyperelliptic.CharacteristicThreeObstruction,
    `SupersingularCurves.Hyperelliptic.GenusTwoFiniteSubgroup,
    `SupersingularCurves.Hyperelliptic.GenusTwoFrobeniusIsomorphism]
  let advertised : Array Lean.Name := #[
    `SupersingularCurves.Geometry.PointedCotangent.augmentation_pointedStalkMap,
    `SupersingularCurves.Geometry.PointedCotangent.liftHom_pointedStalkMap_of_differential_eq_zero,
    `SupersingularCurves.Geometry.PointedCotangent.pointedStalkMap_mem_sq_of_differential_eq_zero,
    `SupersingularCurves.Geometry.PointedCotangent.pointedStalkMap_sub_residue_mem_sq_of_differential_eq_zero,
    `SupersingularCurves.Geometry.PointedCotangent.D_mem_smul_of_mem_sq,
    `SupersingularCurves.Geometry.PointedCotangent.D_stalkMap_mem_maximalIdeal_smul_of_differential_eq_zero,
    `SupersingularCurves.Geometry.PointedCotangent.pointsEquiv_zero_coe,
    `SupersingularCurves.Geometry.SchemeFrobenius.squareZero_frobenius,
    `SupersingularCurves.Geometry.SchemeFrobenius.tangentPoint_relative,
    `SupersingularCurves.Geometry.SchemeFrobenius.relative_differential_eq_zero,
    `SupersingularCurves.Geometry.FrobeniusFactorGroup.factor_mul,
    `SupersingularCurves.Geometry.FrobeniusFactorGroup.factor_one,
    `SupersingularCurves.Geometry.FrobeniusFactorGroup.factor_over,
    `SupersingularCurves.Geometry.GroupScheme.isMonHom_of_pointMap,
    `SupersingularCurves.Geometry.AbelianVariety.frobeniusFactor_over,
    `SupersingularCurves.Geometry.AbelianVariety.frobeniusFactor_isMonHom,
    `SupersingularCurves.Geometry.AbelianVariety.frobeniusFactorGroupIso_hom_left,
    `SupersingularCurves.Geometry.FiniteFlatFactor.isFinite,
    `SupersingularCurves.Geometry.FiniteFlatFactor.isIso_of_equal_rank,
    `SupersingularCurves.Geometry.AbelianVariety.isIso_of_frobenius_factor_verschiebung,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.vInclusion_over,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.structure_eq_snd,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.inclusion_frobenius,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.inclusion_verschiebung,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.factors_iff,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.factors_iff_points,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.one_factors,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.mul_factors,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.inv_factors,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.inclusion_nsmul,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.identityPoint_inclusion,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.unique_point,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.subsingleton,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.vKernel_cotangent_finrank,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.cotangent_finrank_eq_vKernel,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.cotangent_finrank,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.cotangent_finrank_eq_one_of_surface_rank_one,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.cotangent_finrank_of_verschiebung_zero,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.verschiebung_rank_eq_one_of_surface_pRank_zero,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.cotangent_finrank_eq_one_of_surface_pRank_zero,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.cotangent_finrank_eq_one_of_dimension_two,
    `SupersingularCurves.Geometry.LocalizedDifferentialDetection.extendDual_D,
    `SupersingularCurves.Geometry.LocalizedDifferentialDetection.dual_D_mem_under_of_D_mem_smul,
    `SupersingularCurves.Geometry.LocalizedDifferentialDetection.dual_D_mem_under_maximalIdeal,
    `SupersingularCurves.Geometry.LocalizedDifferentialDetection.dual_D_mem_of_D_mem_maximalIdeal_smul,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.vInclusion_frobenius_over,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.vIdentityPoint_frobenius,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.vKernel_frobenius_differential_zero,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.cotangent_bijective,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.cotangent_not_subsingleton,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.vIdentityPoint_inclusion,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.vPoint_kernel_trivial,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.vKernel_unique_point,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.vKernel_subsingleton,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.vKernel_finrank,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.vKernel_cotangent_not_subsingleton,
    `SupersingularCurves.Geometry.PointedCotangent.Fibre.inclusion_over,
    `SupersingularCurves.Geometry.PointedCotangent.Fibre.point_inclusion,
    `SupersingularCurves.Geometry.PointedCotangent.Fibre.tangentPoint_lift_of_differential_zero,
    `SupersingularCurves.Geometry.PointedCotangent.Fibre.differential_bijective_of_zero,
    `SupersingularCurves.Geometry.PointedCotangent.finite_of_locallyOfFiniteType,
    `SupersingularCurves.Geometry.PointedCotangent.Fibre.tangentPoint_lift_of_comp_zero,
    `SupersingularCurves.Geometry.PointedCotangent.Fibre.exists_factor_of_comp_zero,
    `SupersingularCurves.Geometry.PointedCotangent.Fibre.cotangentMap_comp_differential,
    `SupersingularCurves.Geometry.PointedCotangent.Fibre.range_differential_eq_ker_cotangentMap,
    `SupersingularCurves.Geometry.PointedCotangent.Fibre.finrank_add_rank_differential,
    `SupersingularCurves.Geometry.PointedCotangent.Fibre.finrank_eq_sub_rank_differential,
    `SupersingularCurves.Geometry.PointedCotangent.existsUnique_relative_factor_of_differential_eq_zero,
    `SupersingularCurves.Geometry.GroupTranslation.existsUnique_relative_factor_of_identity_differential_eq_zero,
    `SupersingularCurves.Geometry.PerfectFieldVerschiebung.existsUnique_relative_factor_of_differential_eq_zero,
    `SupersingularCurves.Geometry.AbelianVariety.exists_frobenius_factor_iso_of_verschiebungCotangent_eq_zero,
    `SupersingularCurves.Geometry.Jacobian.exists_frobenius_factor_iso_of_verschiebungCotangent_eq_zero,
    `SupersingularCurves.Geometry.ReducedModuleDetection.one_tmul_eq_zero_iff_mem_smul,
    `SupersingularCurves.Geometry.ReducedModuleDetection.eq_zero_of_mem_maximal,
    `SupersingularCurves.Geometry.ReducedModuleDetection.eq_zero_of_forall_dual_mem_maximal,
    `SupersingularCurves.Geometry.ReducedModuleDetection.eq_zero_of_mem_maximal_smul,
    `SupersingularCurves.Geometry.ReducedModuleDetection.eq_zero_of_maximal_fibre_zero,
    `SupersingularCurves.Geometry.SmoothDifferentialDetection.section_stalk_tower,
    `SupersingularCurves.Geometry.SmoothDifferentialDetection.smooth_sectionAlgebra,
    `SupersingularCurves.Geometry.SmoothDifferentialDetection.D_eq_zero_of_closed_stalk_D_mem,
    `SupersingularCurves.Geometry.SmoothDifferentialDetection.stalk_D_eq_zero_of_closed_stalk_D_mem,
    `SupersingularCurves.Geometry.SmoothDifferentialDetection.existsUnique_relative_factor_of_closed_stalk_D_mem,
    `SupersingularCurves.Geometry.SmoothDifferentialDetection.existsUnique_relative_factor_of_rational_stalk_D_mem,
    `SupersingularCurves.Geometry.PointedCotangent.differential_eq_zero_of_relative_factor,
    `SupersingularCurves.Geometry.AbelianVariety.verschiebungCotangent_eq_zero_iff_exists_frobenius_factor,
    `SupersingularCurves.Geometry.AbelianVariety.verschiebungCotangent_eq_zero_iff_exists_frobenius_factor_iso,
    `SupersingularCurves.Geometry.AbelianVariety.verschiebungCotangent_eq_zero_iff_exists_frobenius_factor_groupIso,
    `SupersingularCurves.Geometry.Jacobian.verschiebungCotangent_eq_zero_iff_exists_frobenius_factor,
    `SupersingularCurves.Geometry.Jacobian.verschiebungCotangent_eq_zero_iff_exists_frobenius_factor_iso,
    `SupersingularCurves.Geometry.Jacobian.verschiebungCotangent_eq_zero_iff_exists_frobenius_factor_groupIso,
    `SupersingularCurves.IKO.coefficientMatrix_three_ne_zero_of_separable,
    `SupersingularCurves.Hyperelliptic.SimpleRootModel.not_all_regularCartier_three_zero,
    `SupersingularCurves.Hyperelliptic.SimpleRootModel.not_all_globalCartier_three_zero,
    `SupersingularCurves.Hyperelliptic.SimpleRootModel.jacobian_not_isSuperspecial_three,
    `SupersingularCurves.Hyperelliptic.SimpleRootModel.not_isSuperspecial_three,
    `SupersingularCurves.Hyperelliptic.SimpleRootModel.jacobian_subgroup_cotangent_finrank_one_of_matrix,
    `SupersingularCurves.Hyperelliptic.SimpleRootModel.jacobian_subgroup_cotangent_finrank_one_of_globalCartier,
    `SupersingularCurves.Hyperelliptic.SimpleRootModel.jacobian_subgroup_cotangent_finrank_two_of_matrix_zero,
    `SupersingularCurves.Hyperelliptic.SimpleRootModel.jacobian_exists_frobenius_factor_iso_of_matrix_zero,
    `SupersingularCurves.Hyperelliptic.SimpleRootModel.jacobian_exists_frobenius_factor_iso_of_regularCartier_zero,
    `SupersingularCurves.Hyperelliptic.SimpleRootModel.jacobian_exists_frobenius_factor_iso_of_globalCartier_zero,
    `SupersingularCurves.Hyperelliptic.SimpleRootModel.matrix_zero_iff_jacobian_exists_frobenius_factor_iso,
    `SupersingularCurves.Hyperelliptic.SimpleRootModel.matrix_zero_iff_jacobian_exists_frobenius_factor_groupIso,
    `SupersingularCurves.Hyperelliptic.SimpleRootModel.regularCartier_zero_iff_jacobian_exists_frobenius_factor_iso,
    `SupersingularCurves.Hyperelliptic.SimpleRootModel.globalCartier_zero_iff_jacobian_exists_frobenius_factor_iso,
    `SupersingularCurves.Hyperelliptic.SimpleRootModel.globalCartier_zero_iff_jacobian_exists_frobenius_factor_groupIso]
  for name in advertised do
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Advertised theorem missing or not a theorem: {name}"
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
  Lean.logInfo m!"Checkpoint 25 transitive axiom audit passed: {counts.foldl (· + ·) 0} new project/vendor declaration entries."
