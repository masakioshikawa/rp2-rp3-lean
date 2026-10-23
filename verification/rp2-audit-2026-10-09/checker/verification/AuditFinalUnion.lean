import Lean
import Lean.Replay

/- Release check: audit the union once rather than recomputing overlapping
closures independently for each root. Every selected root must be a theorem.
The unsafe entry point only loads the environment and contributes no proof. -/
open Lean

partial def finalClosure (env : Environment) (todo : List Name)
    (seen : NameSet := {}) : IO NameSet := do
  match todo with
  | [] => return seen
  | n :: rest =>
    if seen.contains n then finalClosure env rest seen else
    let some ci := env.find? n
      | throw <| IO.userError s!"Missing declaration: {n}"
    let deps := ci.getUsedConstantsAsSet.toList
    let deps := match ci with
      | .inductInfo info => info.all ++ deps
      | _ => deps
    finalClosure env (deps ++ rest) (seen.insert n)

unsafe def main (_args : List String) : IO UInt32 := do
  let contents ← IO.FS.readFile "verification/public-theorems.txt"
  let roots := contents.splitOn "\n" |>.filterMap fun line =>
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then none else some line.toName
  if roots.isEmpty then throw <| IO.userError "No public roots"
  initSearchPath (← findSysroot)
  withImportModules #[{ module := `RP2 }] {} fun env => do
    for root in roots do
      let some ci := env.find? root
        | throw <| IO.userError s!"Missing root: {root}"
      unless ci.isTheorem do throw <| IO.userError s!"Root is not a theorem: {root}"
      IO.println s!"ROOT\t{root}"
    let selected ← finalClosure env roots
    let allowed := ([`propext, `Classical.choice, `Quot.sound] : List Name)
    let mut replay : Std.HashMap Name ConstantInfo := {}
    for n in selected.toArray.qsort Name.lt do
      let ci := env.find? n |>.get!
      if ci.isAxiom then
        IO.println s!"AXIOM\t{n}"
        unless allowed.contains n do throw <| IO.userError s!"Unexpected axiom: {n}"
      if ci.isUnsafe || ci.isPartial then
        throw <| IO.userError s!"Unsafe/partial dependency: {n}"
      IO.println s!"DEPENDENCY\t{n}"
      replay := replay.insert n ci
    IO.println s!"PUBLIC_CLOSURE\t{replay.size}"
    IO.println "DEPENDENCY_AUDIT_SUCCESS"
    IO.println s!"FRESH_REPLAY_START\t{replay.size}"
    (← IO.getStdout).flush
    discard <| (← mkEmptyEnvironment).toKernelEnv.replay replay
    IO.println "FRESH_REPLAY_SUCCESS"
  return 0
