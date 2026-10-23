import Lean

/-! Release-only semantic inventory; never imported by the proof library.

Adapted from the semantic-closure suggestion in the user-supplied Claude Opus
review. Unlike a names-only listing, this exports raw statement types and
definition bodies for hashing. It traverses dependencies through all namespaces
and identifies project declarations by their defining module. Theorem proof
bodies are excluded; the separate raw-proof audit checks them.
-/

open Lean

def isProjectConstant (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | none => false
  | some i =>
    let m := env.header.moduleNames[i.toNat]!
    (`RP3).isPrefixOf m || (`RP2).isPrefixOf m

def semanticKind : ConstantInfo → String
  | .defnInfo d => match d.safety with
      | .safe => "definition"
      | .unsafe => "UNSAFE definition"
      | .partial => "PARTIAL definition"
  | .thmInfo _ => "theorem"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

def semanticValue : ConstantInfo → Option Expr
  | .defnInfo d => some d.value
  | .opaqueInfo d => some d.value
  | _ => none

partial def semanticClosure (env : Environment) (todo : List Name)
    (seen : NameSet := {}) : IO NameSet := do
  match todo with
  | [] => return seen
  | n :: rest =>
    if seen.contains n then semanticClosure env rest seen else
    let some ci := env.find? n
      | throw <| IO.userError s!"Missing semantic declaration: {n}"
    let mut next := ci.type.getUsedConstants.toList
    if let some value := semanticValue ci then
      next := value.getUsedConstants.toList ++ next
    match ci with
    | .inductInfo d => next := d.ctors ++ d.all ++ next
    | _ => pure ()
    semanticClosure env (next ++ rest) (seen.insert n)

def semanticRecord (n : Name) (ci : ConstantInfo) : Json :=
  Json.mkObj [
    ("name", toJson n.toString),
    ("kind", toJson (semanticKind ci)),
    ("level_parameters", toJson (ci.levelParams.map Name.toString)),
    ("type", toJson (reprStr ci.type)),
    ("value", toJson ((semanticValue ci).map reprStr))]

unsafe def main (args : List String) : IO UInt32 := do
  let path := args.headD "verification/rp3-semantic-roots.txt"
  let source ← IO.FS.readFile path
  let roots := source.splitOn "\n" |>.filterMap fun line =>
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then none else some line.toName
  if roots.isEmpty then throw <| IO.userError "Empty semantic root list"
  initSearchPath (← findSysroot)
  withImportModules #[{ module := `RP3 }] {} fun env => do
    for root in roots do
      let some ci := env.find? root
        | throw <| IO.userError s!"Missing semantic root: {root}"
      unless ci.isTheorem do
        throw <| IO.userError s!"Semantic root is not a theorem: {root}"
      let used ← semanticClosure env ci.type.getUsedConstants.toList
      let names := used.toArray.filter (isProjectConstant env) |>.qsort Name.lt
      let records := names.map fun n => semanticRecord n (env.find? n |>.get!)
      IO.println (Json.mkObj [
        ("root", semanticRecord root ci),
        ("declarations", Json.arr records)]).compress
  return 0
