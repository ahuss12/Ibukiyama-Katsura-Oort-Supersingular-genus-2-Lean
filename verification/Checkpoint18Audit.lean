import SupersingularCurves.Geometry.JacobianRepartition

set_option autoImplicit false
set_option maxHeartbeats 2000000

/- All declarations originating in the three new modules are audited,
including their full transitive axiom dependencies. The unchanged earlier
modules and vendor sources retain checkpoint 17's full origin audit, checked
separately by source hashes. The full Audit.lean remains available. -/
run_cmd do
  let env ← Lean.getEnv
  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
  let modules : Array Lean.Name := #[
    `SupersingularCurves.Geometry.SchemeCechCohomology,
    `SupersingularCurves.Geometry.CechRepartition,
    `SupersingularCurves.Geometry.JacobianRepartition]
  let mut counts : Array Nat := #[0, 0, 0]
  -- Read each selected module's own declaration table. This has the same
  -- coverage as filtering all environment constants, without traversing
  -- every unrelated imported declaration.
  for j in [:env.header.moduleNames.size] do
    let mod := env.header.moduleNames[j]!
    if modules.contains mod then
      for name in env.header.moduleData[j]!.constNames do
        unless (env.checked.get.find? name).isSome do
          throwError "Missing checked declaration {name} from module {mod}"
        let origin := match env.getModuleIdxFor? name with
          | none => Lean.Name.anonymous
          | some idx => env.header.moduleNames[idx.toNat]!
        unless origin == mod do
          throwError "Declaration origin mismatch: {name} from {origin}, expected {mod}"
        for i in [:modules.size] do
          if mod == modules[i]! then counts := counts.set! i (counts[i]! + 1)
        for ax in ← Lean.collectAxioms name do
          unless allowed.contains ax do
            throwError "Nonstandard axiom {ax} in {name} from module {mod}"
  for i in [:modules.size] do
    unless counts[i]! > 0 do
      throwError "No declarations inspected in module {modules[i]!}"
    Lean.logInfo m!"Audited {counts[i]!} declarations from {modules[i]!}."
  Lean.logInfo m!"Checkpoint 18 transitive axiom audit passed: {counts.foldl (· + ·) 0} new-module declarations."
