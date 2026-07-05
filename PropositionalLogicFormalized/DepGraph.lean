import Lean
import PropositionalLogicFormalized.Basic  -- import whatever top-level file(s) pull in everything you want graphed

open Lean

/-- Restrict to declarations that live in one of our own files (not core/Mathlib). -/
def isProjectDecl (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx =>
    match env.header.moduleNames[idx.toNat]? with
    | some modName => (`PropositionalLogicFormalized).isPrefixOf modName
    | none => false
  | none => true  -- declarations from the file currently being elaborated have no module idx yet

#eval show CoreM Unit from do
  let env ← getEnv
  let mut edges : Array (Name × Name) := #[]
  let mut nodes : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if isProjectDecl env name then
      match ci with
      | .thmInfo info =>
        nodes := nodes.push name
        for dep in info.value.getUsedConstants do
          if dep != name && isProjectDecl env dep then
            edges := edges.push (name, dep)
      | _ => pure ()
  let mut out := "digraph deps {\n  rankdir=LR;\n  node [shape=box, fontsize=10];\n"
  for n in nodes do
    out := out ++ s!"  \"{n}\";\n"
  for (a, b) in edges do
    out := out ++ s!"  \"{a}\" -> \"{b}\";\n"
  out := out ++ "}\n"
  IO.FS.writeFile "deps.dot" out
  IO.println s!"Wrote {nodes.size} nodes and {edges.size} edges to deps.dot"
