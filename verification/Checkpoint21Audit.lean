import SupersingularCurves.Geometry.FrobeniusDifferentialTwist
import SupersingularCurves.Geometry.CartierResidueAdjoint
import SupersingularCurves.Geometry.CartierResidueLocal
import SupersingularCurves.Geometry.CartierVerschiebung
import SupersingularCurves.Geometry.FrobeniusCechSemilinear
import SupersingularCurves.Geometry.CartierTransport
import SupersingularCurves.Geometry.JacobianFrobeniusUntwist
import SupersingularCurves.Geometry.GlobalCartierModels
import SupersingularCurves.Geometry.GlobalCartier
import SupersingularCurves.IKO.VerschiebungCriteria
import SupersingularCurves.IKO.GenusTwoFixedVectors
import SupersingularCurves.Hyperelliptic.GenusTwoPRank

set_option autoImplicit false
set_option maxHeartbeats 4000000

/- Audit each of the ten recovered and two newly written modules' own declaration
tables, including private and generated entries. Inspect stored types and bodies
as well as resolved declarations, so shared lazy equation lemmas are not silently
skipped. No new vendor modules are introduced by this continuation. -/
run_cmd do
  let env ← Lean.getEnv
  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
  let modules : Array Lean.Name := #[
    `SupersingularCurves.Geometry.FrobeniusDifferentialTwist,
    `SupersingularCurves.Geometry.CartierResidueAdjoint,
    `SupersingularCurves.Geometry.CartierResidueLocal,
    `SupersingularCurves.Geometry.CartierVerschiebung,
    `SupersingularCurves.Geometry.FrobeniusCechSemilinear,
    `SupersingularCurves.Geometry.CartierTransport,
    `SupersingularCurves.Geometry.JacobianFrobeniusUntwist,
    `SupersingularCurves.Geometry.GlobalCartierModels,
    `SupersingularCurves.Geometry.GlobalCartier,
    `SupersingularCurves.IKO.VerschiebungCriteria,
    `SupersingularCurves.IKO.GenusTwoFixedVectors,
    `SupersingularCurves.Hyperelliptic.GenusTwoPRank]
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
  Lean.logInfo m!"Checkpoint 21 transitive axiom audit passed: {counts.foldl (· + ·) 0} recovered/new module declaration entries."
