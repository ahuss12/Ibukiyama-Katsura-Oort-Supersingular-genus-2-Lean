import SupersingularCurves.Geometry.PolarisationRootNumerics
import SupersingularCurves.Geometry.AbelianIsogenyRootNumerics
import SupersingularCurves.Geometry.AbelianTateProductPolarization

set_option autoImplicit false
set_option maxHeartbeats 0

run_cmd do
  let env ← Lean.getEnv
  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
  let modules : Array Lean.Name := #[
    `SupersingularCurves.Geometry.PolarisationRootNumerics,
    `SupersingularCurves.Geometry.AbelianIsogenyRootNumerics,
    `SupersingularCurves.Geometry.AbelianTateProductPolarization]
  let advertised : Array Lean.Name := #[
    `SupersingularCurves.Geometry.PolarisationRootNumerics.geomH0_eq_of_iso,
    `SupersingularCurves.Geometry.PolarisationRootNumerics.root_finiteKernel_positive_of_finiteBySections,
    `SupersingularCurves.Geometry.PolarisationRootNumerics.higherCohomology_zero,
    `SupersingularCurves.Geometry.PolarisationRootNumerics.geomH0_eq_eulerChar,
    `SupersingularCurves.Geometry.PolarisationRootNumerics.geomH0_tensorPow,
    `SupersingularCurves.Geometry.PolarisationRootNumerics.cube_finiteBySections,
    `SupersingularCurves.Geometry.PolarisationRootNumerics.geomH0_root_scaling,
    `SupersingularCurves.Geometry.PolarisationRootNumerics.exists_symmetric_finite_cube,
    `SupersingularCurves.Geometry.AbelianIsogenyRootNumerics.finiteBySections_pullback,
    `SupersingularCurves.Geometry.AbelianIsogenyRootNumerics.geomH0_pullback_eq_degree_mul,
    `SupersingularCurves.Geometry.AbelianIsogenyRootNumerics.geomH0_root_eq_of_degree_pow,
    `SupersingularCurves.Geometry.AbelianIsogenyRootNumerics.root_uniform_numerics,
    `SupersingularCurves.Geometry.AbelianIsogenyRootNumerics.exists_symmetric_bundle_with_uniform_rank,
    `SupersingularCurves.Geometry.AbelianTate.productLineBundle_isRiemannPairing,
    `SupersingularCurves.Geometry.AbelianTate.exists_common_perfect_pairings_bound,
    `SupersingularCurves.Geometry.AbelianTate.exists_polarized_zeroDV_graph_quotients_bound]
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
  Lean.logInfo m!"Checkpoint 33 transitive axiom audit passed: {counts.foldl (· + ·) 0} new project declaration entries."
