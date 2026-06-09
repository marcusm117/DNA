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

private def appliedJson (e : AppliedEntry) : String :=
  "{" ++ String.intercalate "," [
    "\"mod\":"  ++ jstr e.mod,
    "\"name\":" ++ jstr e.name,
    "\"line\":" ++ toString e.line ] ++ "}"

unsafe def main (args : List String) : IO UInt32 := do
  let some modStr := args[0]? | do
    IO.eprintln "usage: lake exe faithful_export <RootModule>   (e.g. Book2)"
    return 1
  searchPathRef.set compile_time_search_path%
  withImportModules #[{ module := modStr.toName }] {} (trustLevel := 1024) fun env => do
    -- `getState` folds in entries from all transitive imports (addImportedFn), so loading the
    -- aggregate module (e.g. `Book2`) yields every proposition's annotations at once.
    let sentences := (faithfulExt.getState env).map sentenceJson
    let applied   := (appliedExt.getState env).map appliedJson
    IO.println <| "{\"sentences\":[" ++ String.intercalate "," sentences ++
                  "],\"applied\":[" ++ String.intercalate "," applied ++ "]}"
    return 0
