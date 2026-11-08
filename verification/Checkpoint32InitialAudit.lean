import SupersingularCurves.Geometry.ScalarFrobeniusTatePolarizedGraph
import SupersingularCurves.Geometry.AbelianVerschiebungBinaryProducts
import SupersingularCurves.Geometry.FiniteBySectionsExternalProduct
import SupersingularCurves.Geometry.PolarisationRootKernel

set_option autoImplicit false
set_option maxHeartbeats 0

run_cmd do
  let env ← Lean.getEnv
  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
  let modules : Array Lean.Name := #[
    `SupersingularCurves.Geometry.ScalarFrobeniusTatePolarizedGraph,
    `SupersingularCurves.Geometry.AbelianVerschiebungBinaryProducts,
    `SupersingularCurves.Geometry.FiniteBySectionsExternalProduct,
    `SupersingularCurves.Geometry.PolarisationRootKernel]
  let advertised : Array Lean.Name := #[
    `SupersingularCurves.Geometry.ScalarFrobeniusTate.mem_integralIntersection_productGraph_iff,
    `SupersingularCurves.Geometry.ScalarFrobeniusTate.integralProductPairing_graph_isotropic,
    `SupersingularCurves.Geometry.ScalarFrobeniusTate.exists_isotropic_productGraph_of_perfect_pairings,
    `SupersingularCurves.Geometry.ScalarFrobeniusTate.exists_isotropic_graph_quotients_with_degree_and_zeroDV,
    `SupersingularCurves.Geometry.PointedCotangent.differential_eq_zero_of_abelian_prod_components,
    `SupersingularCurves.Geometry.AbelianVariety.verschiebungCotangent_prod_eq_zero,
    `SupersingularCurves.Geometry.finiteBySections_externalProduct,
    `SupersingularCurves.Geometry.PolarisationRootNumerics.kernelPts_eq_of_iso,
    `SupersingularCurves.Geometry.PolarisationRootNumerics.kernelPts_subset_tensorPow,
    `SupersingularCurves.Geometry.PolarisationRootNumerics.finite_kernelPts_of_root]
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
  Lean.logInfo m!"Checkpoint 32 initial transitive axiom audit passed: {counts.foldl (· + ·) 0} new project declaration entries."
