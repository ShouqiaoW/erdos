import Erdos1038.CompleteProof
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Lean.Util.Path

set_option warningAsError true
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Lean Elab Command

private inductive SourceScanState where
  | code
  | lineComment
  | blockComment (depth : Nat)
  | stringLiteral (escaped : Bool)

/-- Detect an executable occurrence of the native evaluator tactic while
ignoring line comments, nested block comments, and string literals.  The
search word is assembled in two pieces so this audit does not flag itself. -/
private partial def containsExecutableNativeDecide
    (chars : List Char) (state : SourceScanState := .code) : Bool :=
  let needle := ("native" ++ "_decide").toList
  match state, chars with
  | _, [] => false
  | .code, '-' :: '-' :: rest =>
      containsExecutableNativeDecide rest .lineComment
  | .code, '/' :: '-' :: rest =>
      containsExecutableNativeDecide rest (.blockComment 1)
  | .code, '"' :: rest =>
      containsExecutableNativeDecide rest (.stringLiteral false)
  | .code, _ :: rest =>
      chars.take needle.length == needle ||
        containsExecutableNativeDecide rest .code
  | .lineComment, '\n' :: rest =>
      containsExecutableNativeDecide rest .code
  | .lineComment, _ :: rest =>
      containsExecutableNativeDecide rest .lineComment
  | .blockComment depth, '/' :: '-' :: rest =>
      containsExecutableNativeDecide rest (.blockComment (depth + 1))
  | .blockComment 1, '-' :: '/' :: rest =>
      containsExecutableNativeDecide rest .code
  | .blockComment (depth + 1), '-' :: '/' :: rest =>
      containsExecutableNativeDecide rest (.blockComment depth)
  | .blockComment depth, _ :: rest =>
      containsExecutableNativeDecide rest (.blockComment depth)
  | .stringLiteral false, '\\' :: rest =>
      containsExecutableNativeDecide rest (.stringLiteral true)
  | .stringLiteral true, _ :: rest =>
      containsExecutableNativeDecide rest (.stringLiteral false)
  | .stringLiteral false, '"' :: rest =>
      containsExecutableNativeDecide rest .code
  | .stringLiteral false, _ :: rest =>
      containsExecutableNativeDecide rest (.stringLiteral false)

#check Erdos1038.mainTheorem
#print axioms Erdos1038.mainTheorem

/-! Reject every imported project declaration whose transitive axiom set
contains proof admission or a native-evaluator trust axiom.  This is a gate,
not merely an informational migration report. -/
run_cmd do
  let env ← getEnv
  let mut projectDecls : Array Name := #[]
  for (declName, _) in env.constants do
    if declName.toString.startsWith "Erdos1038" then
      projectDecls := projectDecls.push declName
  /- Traverse the union once with a shared visited set.  Re-running
  `collectAxioms` independently for every generated leaf would recompute the
  same large dependency closures thousands of times. -/
  let collectAll : Lean.CollectAxioms.M Unit :=
    projectDecls.forM Lean.CollectAxioms.collect
  let (_, state) := (collectAll.run env).run {}
  let forbidden := state.axioms.filter fun axiomName =>
    axiomName == ``sorryAx ||
      axiomName == ``Lean.ofReduceBool ||
      axiomName == ``Lean.trustCompiler
  if !forbidden.isEmpty then
    throwError m!"project declarations use disallowed axioms: \
      {forbidden.qsort Name.lt |>.toList}"

/-! Reject executable uses even in project source files that are not reachable
from `CompleteProof`.  This prevents an unimported native certificate or probe
from surviving the final repository-wide gate. -/
run_cmd do
  let paths ← System.FilePath.walkDir "Erdos1038"
  let leanPaths := paths.filter fun path => path.extension == some "lean"
  let mut bad : Array System.FilePath := #[]
  for path in leanPaths do
    let source ← IO.FS.readFile path
    if containsExecutableNativeDecide source.toList then
      bad := bad.push path
  let sortedBad := bad.qsort fun a b => a.toString < b.toString
  if !sortedBad.isEmpty then
    throwError m!"Lean sources contain executable native evaluator tactics: {sortedBad.toList}"

/-! The exact public theorem may depend only on the three standard logical
axioms below.  Checking the complement of this allow-list rejects all current
and future unexpected axioms, including proof admission and native-evaluator
trust axioms. -/
run_cmd do
  let axioms ← Lean.collectAxioms ``Erdos1038.mainTheorem
  let unexpected := axioms.filter fun axiomName =>
    axiomName != ``propext &&
      axiomName != ``Classical.choice &&
      axiomName != ``Quot.sound
  if !unexpected.isEmpty then
    throwError m!"mainTheorem uses axioms outside the standard allow-list: \
      {unexpected.qsort Name.lt |>.toList}"
