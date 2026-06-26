import SystemE.Meta.Tactics.Solve

/-!
# Faithfulness annotations (`euclid_sentence`)

This module makes the Euclid → Lean *sentence mapping* a first-class proof object.

A proof step that realizes one of Euclid's sentences is written with `euclid_sentence`
instead of a bare `have`.  It behaves exactly like `have name : type := by tac` (so the
proof term, local context and SMT query are unchanged) but additionally records, into a
persistent environment extension, the tuple

    (locator, euclid-text, lean-type, have-name, source-position)
-/

open Lean Elab Tactic Meta

namespace SystemE.Tactics

/-- One recorded faithfulness annotation: an Euclid sentence and the Lean step realizing it. -/
structure FaithfulEntry where
  /-- Source-anchored locator, e.g. `"2.1.8"` = Book 2, Prop 1, sentence 8. -/
  loc  : String
  /-- Euclid's verbatim sentence (the thing concatenation must recover). -/
  text : String
  /-- Surface syntax of the realizing step's type (for the human review table).
  Empty for `structural` entries, which emit no `have`. -/
  type : String
  /-- The `have` name introduced by the step, e.g. `"step8"`. Empty for `structural` entries. -/
  name : String
  /-- Source position `"line:col"` of the annotation. -/
  pos  : String
  /-- Module the annotation occurred in, e.g. `"Book2.Prop01"`. Used by the external checker to
  associate this sentence's block (same module) with `appliedExt` dependency entries. -/
  mod  : String
  /-- Source line of the annotation (integer; matches `appliedExt.line` for block association). -/
  line : Nat
  /-- `"logical"` = a real proof step (`euclid_sentence`, emits a `have`); `"structural"` =
  enunciation / "I say that" / QED boilerplate (`euclid_intro_sentence` /
  `euclid_conclude_sentence`) that contributes its text to the criterion-1 concatenation but is
  NOT a logical step — it attaches to `euclid_intros` / the final `exact` and emits no `have`. -/
  kind : String
  deriving Inhabited, Repr

/-- Persistent env extension storing all `FaithfulEntry`s.  Entries from imported modules
are folded in, so a reader sees the current module plus its transitive imports.
(Shape follows Mathlib's `Mathlib/Tactic/Hint.lean`.) -/
initialize faithfulExt :
    SimplePersistentEnvExtension FaithfulEntry (List FaithfulEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := (·.cons)
    addImportedFn := mkStateFromImportedEntries (·.cons) {}
  }

/-- Current annotation's location: `(pos "line:col", module string, line number)`. -/
private def refLoc : TacticM (String × String × Nat) := do
  let fileMap ← getFileMap
  let modName := (← getMainModule).toString
  return match (← getRef).getPos? with
    | some p => let lc := fileMap.toPosition p; (s!"{lc.line}:{lc.column}", modName, lc.line)
    | none   => ("?", modName, 0)

/-- `euclid_sentence "loc" "euclid text" (name : type) := by tac`

Realizes one Euclid sentence.  Elaborates to `have name : type := by tac` (identical proof
term / context to a plain `have`) and records a `logical` annotation into `faithfulExt`. -/
syntax (name := euclidSentence)
  "euclid_sentence " str str "(" ident " : " term ")" ":=" "by " tacticSeq : tactic

elab_rules : tactic
  | `(tactic| euclid_sentence $loc:str $txt:str ($nm:ident : $ty:term) := by $tac) => do
    let (posStr, modName, lineNo) ← refLoc
    -- Surface syntax of the type (verbatim slice when available).
    let typeStr := (ty.raw.reprint).getD (toString ty)
    modifyEnv fun env => faithfulExt.addEntry env {
      loc  := loc.getString
      text := txt.getString
      type := typeStr
      name := nm.getId.toString
      pos  := posStr
      mod  := modName
      line := lineNo
      kind := "logical" }
    -- Emit the real `have`; proof term and local context unchanged.
    evalTactic (← `(tactic| have $nm:ident : $ty := by $tac))

/-- `euclid_intro_sentence "loc" "euclid text"` and `euclid_conclude_sentence "loc" "euclid text"`

Record a *structural* Euclid sentence — the enunciation / "I say that" preamble (placed right
after `euclid_intros`) or the closing restatement + QED boilerplate (placed at the final step).
These contribute their text to the criterion-1 concatenation but are NOT logical steps: they emit
no `have` (the tactic is a `skip`), so the proof term and local context are unchanged. -/
syntax (name := euclidIntroSentence)
  "euclid_intro_sentence " str str : tactic
syntax (name := euclidConcludeSentence)
  "euclid_conclude_sentence " str str : tactic

/-- Shared recorder for the two structural tactics. -/
private def recordStructural (loc txt : TSyntax `str) : TacticM Unit := do
  let (posStr, modName, lineNo) ← refLoc
  modifyEnv fun env => faithfulExt.addEntry env {
    loc  := loc.getString
    text := txt.getString
    type := ""
    name := ""
    pos  := posStr
    mod  := modName
    line := lineNo
    kind := "structural" }
  -- No tactic is emitted: this is a pure annotation, valid whether or not goals remain (it may
  -- follow the final `exact`). Recording only — proof term and local context are untouched.
  pure ()

elab_rules : tactic
  | `(tactic| euclid_intro_sentence $loc:str $txt:str)    => recordStructural loc txt
  | `(tactic| euclid_conclude_sentence $loc:str $txt:str) => recordStructural loc txt

-- Faithfulness CHECKING (criterion 1: concatenate sentence texts, compare to the canonical
-- source) is done OUTSIDE Lean by `scripts/check_faithful.py`, which reads these annotations
-- from the source file. That keeps text-checking instant (no recompile / no SMT). This module
-- only RECORDS the annotations; the optional `lake exe` gate that reads them back from the
-- compiled .olean is deferred (see plan / todos).

/-- `euclid_assumption "euclid text" T` — discharge a reasoning-hypothesis slot in a wired proof.

Used by `wire_main.py` for hypothesis binders that correspond to an explicit `-- @assumption`
annotation: the English text is documentary (Lean ignores it); `show T` checks the binder type
matches the expected goal; `assumption` closes it from the local context.

The `use_override pf` form is used when the cited input is a conjunct projection (e.g. `step2.1`)
that plain `assumption` cannot find — `exact pf` closes it instead. -/
syntax (name := euclidAssumption)
  "euclid_assumption" str term : tactic
syntax (name := euclidAssumptionOverride)
  "euclid_assumption" str term "use_override" term : tactic

elab_rules : tactic
  | `(tactic| euclid_assumption $_:str $t:term) => do
    evalTactic (← `(tactic| show $t; assumption))
  | `(tactic| euclid_assumption $_:str $t:term use_override $pf:term) => do
    evalTactic (← `(tactic| show $t; exact $pf))

end SystemE.Tactics
