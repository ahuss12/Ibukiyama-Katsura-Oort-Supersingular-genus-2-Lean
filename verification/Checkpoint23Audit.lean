import SupersingularCurves.Geometry.CartierVerschiebungRank
import SupersingularCurves.Geometry.VerschiebungNaturality
import SupersingularCurves.Hyperelliptic.FifthPowerClassification
import SupersingularCurves.Hyperelliptic.GenusTwoOrdinary
import SupersingularCurves.Hyperelliptic.GenusTwoOrdinaryVerschiebung
import SupersingularCurves.IKO.FifthPowerCongruences
import SupersingularCurves.IKO.GenusTwoOrdinaryFixedVectors
import SupersingularCurves.IKO.SemilinearInvertibility

set_option autoImplicit false
set_option maxHeartbeats 0

run_cmd do
  let env ← Lean.getEnv
  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
  let modules : Array Lean.Name := #[
    `SupersingularCurves.Geometry.CartierVerschiebungRank,
    `SupersingularCurves.Geometry.VerschiebungNaturality,
    `SupersingularCurves.Hyperelliptic.FifthPowerClassification,
    `SupersingularCurves.Hyperelliptic.GenusTwoOrdinary,
    `SupersingularCurves.Hyperelliptic.GenusTwoOrdinaryVerschiebung,
    `SupersingularCurves.IKO.FifthPowerCongruences,
    `SupersingularCurves.IKO.GenusTwoOrdinaryFixedVectors,
    `SupersingularCurves.IKO.SemilinearInvertibility]
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
  Lean.logInfo m!"Checkpoint 23 transitive axiom audit passed: {counts.foldl (· + ·) 0} new project/vendor declaration entries."
