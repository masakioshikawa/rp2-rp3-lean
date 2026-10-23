import Lean
import Lean.Replay

/- Release verification program; not imported by RP3.

The unsafe entry point is required by Lean's environment-loading API. It does
not contribute any proof declaration. We inspect raw declaration bodies,
reject nonstandard axioms and unsafe/partial public dependencies, and can
replay the whole public dependency closure into an empty kernel environment.
Replay uses the same Lean kernel, not an independently implemented checker.
-/

open Lean

def allowedAxioms : NameSet :=
  ([`propext, `Classical.choice, `Quot.sound] : List Name).foldl (·.insert ·) {}

def declarationKind (ci : ConstantInfo) : String := match ci with
  | .axiomInfo _ => "axiom"
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

partial def rawClosure (env : Environment) (todo : List Name)
    (seen : NameSet := {}) : IO NameSet := do
  match todo with
  | [] => return seen
  | n :: rest =>
    if seen.contains n then rawClosure env rest seen else
    let some ci := env.find? n
      | throw <| IO.userError s!"Missing raw declaration: {n}"
    let mut deps := ci.getUsedConstantsAsSet.toList
    -- Mutual inductive siblings must be replayed together.
    match ci with
    | .inductInfo info => deps := info.all ++ deps
    | _ => pure ()
    rawClosure env (deps ++ rest) (seen.insert n)

def publicNames (path : System.FilePath) : IO (Array Name) := do
  let source ← IO.FS.readFile path
  let names := source.splitOn "\n" |>.filterMap fun line =>
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then none else some line.toName
  if names.isEmpty then throw <| IO.userError "Public theorem list is empty"
  return names.toArray

unsafe def main (args : List String) : IO UInt32 := do
  let rootsPath := args.find? (fun arg => !arg.startsWith "--") |>.getD
    "verification/rp3-public-theorems.txt"
  let roots ← publicNames rootsPath
  initSearchPath (← findSysroot)
  withImportModules #[{ module := `RP3 }] {} fun env => do
    let mut selected : NameSet := {}
    for root in roots do
      let some rootInfo := env.find? root
        | throw <| IO.userError s!"Public theorem does not exist: {root}"
      unless rootInfo.isTheorem do
        throw <| IO.userError s!"Public audit root is not a theorem: {root}"
      let used ← rawClosure env [root]
      IO.println s!"ROOT\t{root}\tconstants={used.toList.length}"
      for n in used.toArray.qsort Name.lt do
        let ci := env.find? n |>.get!
        if ci.isAxiom then
          IO.println s!"ROOT_AXIOM\t{root}\t{n}"
          unless allowedAxioms.contains n do
            throw <| IO.userError s!"Unexpected axiom in {root}: {n}"
        if ci.isUnsafe || ci.isPartial then
          throw <| IO.userError s!"Unsafe/partial dependency in {root}: {n}"
      selected := selected ++ used
    IO.println s!"PUBLIC_CLOSURE\t{selected.toList.length}"
    if args.contains "--inventory" then
      for n in selected.toArray.qsort Name.lt do
        let ci := env.find? n |>.get!
        IO.println s!"DEPENDENCY\t{n}\t{declarationKind ci}"
    IO.println "DEPENDENCY_AUDIT_SUCCESS"
    if args.contains "--replay" then
      let mut declarations : Std.HashMap Name ConstantInfo := {}
      for n in selected do
        declarations := declarations.insert n (env.find? n |>.get!)
      IO.println s!"FRESH_REPLAY_START\t{declarations.size}"
      (← IO.getStdout).flush
      discard <| (← mkEmptyEnvironment).toKernelEnv.replay declarations
      IO.println "FRESH_REPLAY_SUCCESS"
  return 0
