import Lake
open Lake DSL

package «lib» where
  leanOptions := #[⟨`relaxedAutoImplicit, true⟩]

@[default_target]
lean_lib SystemE {
}

lean_lib Book {
}

lean_lib Book2 {
}

lean_lib UniGeo {
}

lean_lib Examples {
}

lean_lib E3 {
}

/-- Staging area for the faithful-euclid pipeline (Phase B). Each Euclid sentence is proved as its
OWN isolated file `Scratch/Book<N>/Prop<NN>/helper_<book>_step<n>.lean`, so it builds alone in ~30s
instead of re-paying the whole proof; if one builds, we reunite them in Phase C.
`.submodules` makes EACH file its own buildable module — `scripts/safe_build.sh
Scratch.Book2.Prop02.helper_2_step3` builds that one file and nothing else. This is a SEPARATE lib
from Book/Book2, so `lake build Book2` and `faithful_export` never touch scratch; finished step
lemmas are moved into `Book<N>/Prop<NN>_steps.lean` in Phase C. -/
lean_lib Scratch {
  globs := #[.submodules `Scratch]
}

/-- Reads faithfulness annotations back from a compiled module's `.olean` and dumps them as JSON
for `scripts/check_faithful.py --olean`.  See `FaithfulExport.lean`. -/
lean_exe faithful_export {
  root := `FaithfulExport
  -- needs interpreter support: it loads compiled modules via `importModules` (Lean/Init code).
  supportInterpreter := true
}

require mathlib from git "https://github.com/leanprover-community/mathlib4"

require smt from git "https://github.com/yangky11/lean-smt.git" @ "main"

def tmpFileDir := "tmp"

def checkAvailable (cmd : String) : IO Unit := do
  let proc ← IO.Process.output {
    cmd := "which",
    args := #[cmd]
  }
  if proc.exitCode != 0 then
    throw $ IO.userError s!"Cannot find `{cmd}`."

script check do
  checkAvailable "smt-portfolio"
  checkAvailable "z3"
  checkAvailable "cvc5"
  println! "All requirements are satisfied."
  return 0

script cleanup do
  IO.FS.removeDirAll tmpFileDir
  return 0

script aggregate do
  let bookDir := (← IO.currentDir) / "Book"
  let leanPaths := (← System.FilePath.walkDir bookDir) |>.filter fun p => p.extension = some "lean"
  let sortedPaths := leanPaths.qsort (fun p₁ p₂ => p₁.toString < p₂.toString) |>.toList
  println! sortedPaths
  let code ← sortedPaths.mapM fun p => do
    let lines := (← IO.FS.lines p) |>.filter fun l =>
      ¬(l.startsWith "import" ∨ l.startsWith "namespace" ∨ l.startsWith "end")
    return (String.join $ (lines.map fun l => l ++ "\n").toList).trim ++ "\n\n"
  let codeAll := "import SystemE\n\nnamespace Elements\n\n" ++ String.join code ++ "\nend Elements\n"

  let outFile := bookDir / "All.lean"
  if ← outFile.pathExists then
    IO.FS.removeFile outFile
  IO.FS.writeFile outFile codeAll
  println! codeAll

  return 0

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"
