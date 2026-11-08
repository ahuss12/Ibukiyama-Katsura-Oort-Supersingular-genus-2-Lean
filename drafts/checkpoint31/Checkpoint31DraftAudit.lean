import SupersingularCurves.Geometry.ScalarFrobeniusTateGraphQuotients
import SupersingularCurves.Geometry.ScalarFrobeniusTateQuotientRoots
import SupersingularCurves.Geometry.PolarizedFiniteModels

set_option autoImplicit false
set_option maxHeartbeats 0

run_cmd do
  let env ← Lean.getEnv
  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
  let modules : Array Lean.Name := #[
    `SupersingularCurves.Geometry.ScalarFrobeniusTateQuotientDegree,
    `SupersingularCurves.Geometry.ScalarFrobeniusTateQuotientPairing,
    `SupersingularCurves.Geometry.ScalarFrobeniusTateGraphQuotients,
    `SupersingularCurves.Geometry.PolarisationRootNumerics,
    `SupersingularCurves.Geometry.ScalarFrobeniusTateQuotientRoots,
    `SupersingularCurves.Geometry.PolarizedFiniteModels,
    `SupersingularCurves.Geometry.AbelianIsogenyRootNumerics,
    `SupersingularCurves.Geometry.ScalarFrobeniusPolarizedDescentRank]
  let advertised : Array Lean.Name := #[
    `SupersingularCurves.Geometry.ScalarFrobeniusTate.Quotient.multiplicationFactor_finrank_of_half_rank,
    `SupersingularCurves.Geometry.ScalarFrobeniusTate.exists_quotient_with_prescribed_lattice_and_degree,
    `SupersingularCurves.Geometry.ScalarFrobeniusTate.exists_prescribedLatticeQuotients_with_degree,
    `SupersingularCurves.Geometry.ScalarFrobeniusTate.pairing_dvd_of_mem_isotropic_lattice,
    `SupersingularCurves.Geometry.ScalarFrobeniusTate.PrescribedLatticeQuotients.pairing_dvd,
    `SupersingularCurves.Geometry.ScalarFrobeniusTate.exists_prescribedLatticeQuotients_with_degree_and_zeroDV,
    `SupersingularCurves.Geometry.ScalarFrobeniusTate.exists_complement_integralIntersection,
    `SupersingularCurves.Geometry.ScalarFrobeniusTate.finrank_integralIntersection_productGraph,
    `SupersingularCurves.Geometry.ScalarFrobeniusTate.integralIntersection_isotropic,
    `SupersingularCurves.Geometry.ScalarFrobeniusTate.exists_prescribed_graph_quotients_with_degree_and_zeroDV,
    `SupersingularCurves.Geometry.AbelianIsogenyRootNumerics.finiteBySections_pullback,
    `SupersingularCurves.Geometry.AbelianIsogenyRootNumerics.geomH0_pullback_eq_degree_mul,
    `SupersingularCurves.Geometry.AbelianIsogenyRootNumerics.geomH0_root_eq_of_degree_pow,
    `SupersingularCurves.Geometry.AbelianIsogenyRootNumerics.root_uniform_numerics,
    `SupersingularCurves.Geometry.AbelianIsogenyRootNumerics.exists_symmetric_bundle_with_uniform_rank,
    `SupersingularCurves.Geometry.PolarisationRootNumerics.kernelPts_eq_of_iso,
    `SupersingularCurves.Geometry.PolarisationRootNumerics.kernelPts_subset_tensorPow,
    `SupersingularCurves.Geometry.PolarisationRootNumerics.finite_kernelPts_of_root,
    `SupersingularCurves.Geometry.PolarisationRootNumerics.geomH0_eq_of_iso,
    `SupersingularCurves.Geometry.PolarisationRootNumerics.root_finiteKernel_positive_of_finiteBySections,
    `SupersingularCurves.Geometry.PolarisationRootNumerics.higherCohomology_zero,
    `SupersingularCurves.Geometry.PolarisationRootNumerics.geomH0_eq_eulerChar,
    `SupersingularCurves.Geometry.PolarisationRootNumerics.geomH0_tensorPow,
    `SupersingularCurves.Geometry.PolarisationRootNumerics.cube_finiteBySections,
    `SupersingularCurves.Geometry.PolarisationRootNumerics.geomH0_root_scaling,
    `SupersingularCurves.Geometry.PolarisationRootNumerics.exists_symmetric_finite_cube,
    `SupersingularCurves.Geometry.PolarizedFiniteModels.exists_finite_variety_representatives,
    `SupersingularCurves.Geometry.PolarizedFiniteModels.exists_finite_geometric_models_of_bounded_models,
    `SupersingularCurves.Geometry.ScalarFrobeniusTate.exists_finite_models_of_symmetric_veryAmple_fixed_rank,
    `SupersingularCurves.Geometry.AbelianVariety.exists_finiteField_polarized_model_with_rank,
    `SupersingularCurves.Geometry.ScalarFrobeniusTate.exists_root_of_isotropic_tate_image,
    `SupersingularCurves.Geometry.ScalarFrobeniusTate.exists_quotient_root_with_uniform_numerics]
  for name in advertised do
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Advertised theorem missing or not a theorem: {name}"
  let mut counts : Array Nat := Array.replicate modules.size 0
  let mut sharedEntries : Nat := 0
  let mut moduleIndices : Std.HashMap Lean.Name Nat := {}
  for i in [:modules.size] do
    moduleIndices := moduleIndices.insert modules[i]! i
  for j in [:env.header.moduleNames.size] do
    let mod := env.header.moduleNames[j]!
    if let some moduleIndex := moduleIndices[mod]? then
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
        counts := counts.set! moduleIndex (counts[moduleIndex]! + 1)
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
    if counts[i]! == 0 then
      throwError "No declarations inspected in module {modules[i]!}"
    Lean.logInfo m!"Audited {counts[i]!} declarations from {modules[i]!}."
  Lean.logInfo m!"Inspected {sharedEntries} shared generated entries by stored type/body as well as resolved declaration."
  Lean.logInfo m!"Checkpoint 31 transitive axiom audit passed: {counts.foldl (· + ·) 0} new project declaration entries."
