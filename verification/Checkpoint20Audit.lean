import SupersingularCurves.Geometry.CechCurvePullback
import SupersingularCurves.Geometry.CechGluingPullback
import SupersingularCurves.Geometry.FrobeniusCechPullback
import SupersingularCurves.Geometry.CechCurveBaseChange
import SupersingularCurves.Geometry.CechCocycleNaturality
import SupersingularCurves.Geometry.CechDeformationNaturality
import SupersingularCurves.Geometry.FrobeniusCechComparison

set_option autoImplicit false
set_option maxHeartbeats 2000000

/- Audit every declaration from all seven new project modules and all eight
newly imported pinned modules, including full transitive axiom dependencies.
Retained sources are checked against their previous audited hashes. -/
run_cmd do
  let env ← Lean.getEnv
  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
  let modules : Array Lean.Name := #[
    `SupersingularCurves.Geometry.CechCurvePullback,
    `SupersingularCurves.Geometry.CechGluingPullback,
    `SupersingularCurves.Geometry.FrobeniusCechPullback,
    `SupersingularCurves.Geometry.CechCurveBaseChange,
    `SupersingularCurves.Geometry.CechCocycleNaturality,
    `SupersingularCurves.Geometry.CechDeformationNaturality,
    `SupersingularCurves.Geometry.FrobeniusCechComparison,
    `P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback,
    `P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback_of_le,
    `P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit,
    `P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_pullbackComp_hom_app_pullbackLocalSection,
    `Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback,
    `Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback_of_le,
    `Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit,
    `Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_hom_app_pullbackLocalSection]
  let mut counts : Array Nat := Array.replicate modules.size 0
  let mut sharedEntries : Nat := 0
  -- Inspect each selected module's own declaration table. Lazy equation
  -- lemmas can be generated in more than one imported module, so their
  -- canonical environment origin can differ. Audit the stored type/body
  -- as well as the resolved declaration: no duplicate entry is skipped.
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
  Lean.logInfo m!"Checkpoint 20 transitive axiom audit passed: {counts.foldl (· + ·) 0} new project/vendor declaration entries."
