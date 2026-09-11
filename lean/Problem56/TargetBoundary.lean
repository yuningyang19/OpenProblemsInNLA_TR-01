import Lean

open Lean Elab Command Meta

/-!
Development checks in the pinned solution environment. These do not compare
independent environments or certify a natural-language statement. Freeze this
module and the reference definitions before proof work; use Comparator for
independent Challenge/Solution closure.
-/

/-- Require an exact public type up to Lean definitional equality. -/
elab "#check_public_type " name:ident " : " expected:term : command => do
  let env ← getEnv
  let some info := env.find? name.getId
    | throwErrorAt name "unknown public declaration {name.getId}"
  liftTermElabM do
    let target ← Term.elabType expected
    Term.synthesizeSyntheticMVarsNoPostponing
    let target ← instantiateMVars target
    if target.hasMVar then
      throwError "public target has unresolved metavariables"
    unless ← isDefEq info.type target do
      throwErrorAt name "public type differs from frozen target"

/-- Reject even an unused, transitively imported Challenge module. -/
elab "#reject_imports " names:ident,* : command => do
  let env ← getEnv
  for name in names.getElems do
    if env.header.moduleNames.contains name.getId then
      throwErrorAt name "forbidden reference import: {name.getId}"
