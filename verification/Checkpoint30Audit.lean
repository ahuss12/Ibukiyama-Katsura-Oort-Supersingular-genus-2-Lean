import SupersingularCurves.Geometry.ScalarFrobeniusTateFiniteModels

set_option autoImplicit false
set_option maxHeartbeats 0

run_cmd do
  let env ← Lean.getEnv
  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
  let modules : Array Lean.Name := #[
    `SupersingularCurves.Geometry.PadicLatticeCompactness,
    `SupersingularCurves.Geometry.PadicLatticeOperators,
    `SupersingularCurves.Geometry.ScalarFrobeniusTateRecurrence,
    `SupersingularCurves.Geometry.ScalarFrobeniusTateFiniteModels]
  let advertised : Array Lean.Name := #[
    `SupersingularCurves.Geometry.PadicLattice.continuous_rationalMatrix,
    `SupersingularCurves.Geometry.PadicLattice.exists_nonzero_mem_range_le,
    `SupersingularCurves.Geometry.PadicLattice.toMatrix_baseChange,
    `SupersingularCurves.Geometry.PadicLattice.equivFun_baseChange_tmul,
    `SupersingularCurves.Geometry.PadicLattice.exists_nonzero_mem_range_le_of_integral_errors,
    `SupersingularCurves.Geometry.PadicLattice.exists_integral_error_of_mem_lattice,
    `SupersingularCurves.Geometry.PadicLattice.exists_nonzero_integral_vector,
    `SupersingularCurves.Geometry.ScalarFrobeniusTate.exists_recurring_model,
    `SupersingularCurves.Geometry.ScalarFrobeniusTate.exists_actualEndSpan_operator_of_recurring_lattices,
    `SupersingularCurves.Geometry.ScalarFrobeniusTate.exists_actualEndSpan_operator_of_finite_quotient_models,
    `SupersingularCurves.Geometry.ScalarFrobeniusTate.nonempty_prescribedLatticeQuotients,
    `SupersingularCurves.Geometry.ScalarFrobeniusTate.exists_actualEndSpan_operator_of_finite_models,
    `SupersingularCurves.Geometry.ScalarFrobeniusTate.productGraph_ne_bot,
    `SupersingularCurves.Geometry.ScalarFrobeniusTate.exists_elliptic_map_of_finite_graph_quotient_models,
    `SupersingularCurves.Geometry.ScalarFrobeniusTate.exists_supersingular_product_isogenies_of_finite_graph_quotient_models]
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
  Lean.logInfo m!"Checkpoint 30 transitive axiom audit passed: {counts.foldl (· + ·) 0} new project declaration entries."
