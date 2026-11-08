import SupersingularCurves.Geometry.ScalarFrobeniusTateEllipticSubgroup

set_option autoImplicit false
set_option maxHeartbeats 0

run_cmd do
  let env ← Lean.getEnv
  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
  let modules : Array Lean.Name := #[
    `SupersingularCurves.Geometry.ProperCurveFiniteMap,
    `SupersingularCurves.Geometry.AbelianHomImage,
    `SupersingularCurves.Geometry.EllipticSubgroupFromMap,
    `SupersingularCurves.Geometry.AbelianSurfaceEllipticKernel,
    `SupersingularCurves.Geometry.ScalarFrobeniusTateEllipticSubgroup,
    `P2M.Sol.S_AlgebraicGeometry_Scheme_finite_of_isClosed_of_ne_univ_of_forall_isClosed_singleton,
    `P2M.Sol.S_AlgebraicGeometry_isClosed_singleton_or_isGenericPoint_and_exists_not_isGenericPoint_of_smoothOfRelativeDimension_one,
    `Theorems.Thm_AlgebraicGeometry_Scheme_finite_of_isClosed_of_ne_univ_of_forall_isClosed_singleton,
    `Theorems.Thm_AlgebraicGeometry_isClosed_singleton_or_isGenericPoint_and_exists_not_isGenericPoint_of_smoothOfRelativeDimension_one]
  let advertised : Array Lean.Name := #[
    `SupersingularCurves.Geometry.isFinite_of_proper_curve_of_not_constant,
    `SupersingularCurves.Geometry.surjective_of_target_proper_curve_of_not_constant,
    `SupersingularCurves.Geometry.isReduced_schemeImage,
    `SupersingularCurves.Geometry.AbelianVariety.hom_preserves_law,
    `SupersingularCurves.Geometry.AbelianVariety.exists_closed_subgroup_of_finite_hom,
    `SupersingularCurves.Geometry.AbelianTate.not_constant_of_rationalMap_ne_zero,
    `SupersingularCurves.Geometry.AbelianVariety.isFinite_of_elliptic_rationalMap_ne_zero,
    `SupersingularCurves.Geometry.AbelianVariety.exists_closed_elliptic_subgroup_of_rationalMap_ne_zero,
    `SupersingularCurves.Geometry.AbelianVariety.isSupersingularOver_of_elliptic_rationalMap_ne_zero,
    `SupersingularCurves.Geometry.isFinite_of_finite_rationalPoints,
    `SupersingularCurves.Geometry.AbelianVariety.surjective_of_to_elliptic_rationalMap_ne_zero,
    `SupersingularCurves.Geometry.AbelianVariety.exists_closed_elliptic_subgroup_of_to_elliptic_rationalMap_ne_zero,
    `SupersingularCurves.Geometry.AbelianVariety.isSupersingularOver_of_to_elliptic_rationalMap_ne_zero,
    `SupersingularCurves.Geometry.ScalarFrobeniusTate.exists_closed_elliptic_subgroup_of_actualEndSpan_graph,
    `SupersingularCurves.Geometry.ScalarFrobeniusTate.exists_supersingular_product_isogenies_of_actualEndSpan_graph,
    `SupersingularCurves.Geometry.ScalarFrobeniusTate.isSupersingularOver_of_actualEndSpan_graph]
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
    if i < 5 && counts[i]! == 0 then
      throwError "No declarations inspected in module {modules[i]!}"
    Lean.logInfo m!"Audited {counts[i]!} declarations from {modules[i]!}."
  Lean.logInfo m!"Inspected {sharedEntries} shared generated entries by stored type/body as well as resolved declaration."
  Lean.logInfo m!"Checkpoint 29 transitive axiom audit passed: {counts.foldl (· + ·) 0} new project/vendor declaration entries."
