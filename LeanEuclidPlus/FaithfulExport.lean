/-
`faithful_export` — dump the faithfulness annotations recorded in a compiled module's `.olean`.

Usage:
    lake exe faithful_export <RootModule>        e.g.  lake exe faithful_export Book2

Loads the module (and its transitive imports) with `importModules`, reads back the two persistent
environment extensions populated during compilation —
  • `faithfulExt`  : the `euclid_sentence` / `euclid_intro_sentence` / `euclid_conclude_sentence`
                     annotations (locator, verbatim text, kind, module, line);
  • `appliedExt`   : every `euclid_apply (proposition_* …)`, with the COMPILER-RESOLVED
                     fully-qualified constant name, module, and line —
and emits them as a single JSON object on stdout:

    { "sentences": [ {loc, text, kind, mod, line}, … ],
      "applied":   [ {mod, name, line}, … ] }

`scripts/check_faithful.py --olean <json>` consumes this. This program is a dumb dumper: all
comparison / block-association / book-aware citation matching lives in the Python checker.

This is the CERTAIN faithfulness path: the texts are what the compiler elaborated (not regexed
from source) and the dependency names are book-aware fully-qualified constants.
-/
import Lean
import Batteries.Lean.Util.Path   -- `compile_time_search_path%`
import SystemE

open Lean SystemE.Tactics

/-- JSON-escape a string and wrap it in double quotes. -/
private def jstr (s : String) : String :=
  "\"" ++ (s.foldl (init := "") fun acc c =>
    acc ++ (match c with
      | '"'  => "\\\""
      | '\\' => "\\\\"
      | '\n' => "\\n"
      | '\r' => "\\r"
      | '\t' => "\\t"
      | _    => String.singleton c)) ++ "\""

private def sentenceJson (e : FaithfulEntry) : String :=
  "{" ++ String.intercalate "," [
    "\"loc\":"  ++ jstr e.loc,
    "\"text\":" ++ jstr e.text,
    "\"kind\":" ++ jstr e.kind,
    "\"mod\":"  ++ jstr e.mod,
    "\"line\":" ++ toString e.line ] ++ "}"

/-- Every `proposition_*` constant in the TRANSITIVE dependency closure of `root` (following the
constants used in each declaration's type and value, recursively). Resolved by constant identity in
the compiled environment, so it is book-aware and immune to string-name spoofing. Used so a citation
made INSIDE an applied `helper_<book>_step<n>` lemma still counts: criterion 3 matches the cited
`[Prop.~B.M]` against these names, not just the applied head. -/
private partial def propClosure (env : Environment) (root : Name) : Array String := Id.run do
  let mut seen  : NameSet := {}
  let mut out   : Array String := #[]
  let mut work  : Array Name := #[root]
  while _h : work.size > 0 do
    let n := work.back
    work := work.pop
    if seen.contains n then
      continue
    seen := seen.insert n
    -- Match the LAST name component safely: it may be `.num`/`.anonymous` for internal/auxiliary
    -- constants in the dependency graph (e.g. `foo._proof_5`), on which `getString!` PANICS. Only a
    -- `.str _ s` component can be a `proposition_*`; non-string-terminated names are never our props,
    -- so skipping them loses nothing.
    if let .str _ s := n then
      if s.startsWith "proposition_" then
        out := out.push n.toString
    -- PRUNE the descent: a Euclid `proposition_*` lives in `Elements`, and the dependency chain to
    -- reach one stays within `Elements`/`SystemE` (props use earlier props + System-E axioms, never
    -- routed THROUGH Mathlib/Lean core). So only recurse into those two roots. This cuts ~99% of the
    -- graph (all of Mathlib/Init/Std) that can never contain or bridge to a proposition — without
    -- dropping any prop — turning a graph walk over all of Mathlib into a tiny one.
    let root := n.getRoot.toString
    if root == "Elements" || root == "SystemE" then
      if let some ci := env.find? n then
        for d in ci.type.getUsedConstants do
          work := work.push d
        if let some v := ci.value? then
          for d in v.getUsedConstants do
            work := work.push d
  return out

private def appliedJson (env : Environment) (e : AppliedEntry) : String :=
  let deps := propClosure env e.name.toName
  "{" ++ String.intercalate "," [
    "\"mod\":"  ++ jstr e.mod,
    "\"name\":" ++ jstr e.name,
    "\"line\":" ++ toString e.line,
    "\"deps\":[" ++ String.intercalate "," (deps.map jstr).toList ++ "]" ] ++ "}"

unsafe def main (args : List String) : IO UInt32 := do
  let some modStr := args[0]? | do
    IO.eprintln "usage: lake exe faithful_export <RootModule>   (e.g. Book2)"
    return 1
  searchPathRef.set compile_time_search_path%
  withImportModules #[{ module := modStr.toName }] {} (trustLevel := 1024) fun env => do
    -- `getState` folds in entries from all transitive imports (addImportedFn), so loading the
    -- aggregate module (e.g. `Book2`) yields every proposition's annotations at once.
    let sentences := (faithfulExt.getState env).map sentenceJson
    let applied   := (appliedExt.getState env).map (appliedJson env)
    IO.println <| "{\"sentences\":[" ++ String.intercalate "," sentences ++
                  "],\"applied\":[" ++ String.intercalate "," applied ++ "]}"
    return 0
