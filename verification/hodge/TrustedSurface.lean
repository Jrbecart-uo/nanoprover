import HodgeConjecture.Statement

/-!
Audit helper (not part of upstream): list every repo-loc constant whose *meaning* the
statement `HodgeConjecture` depends on.

Traversal from `HodgeConjecture`: for definitions / instances / opaques / inductives we
follow both type and value (their content matters); for theorems we follow only the type
(proofs are kernel-checked and proof-irrelevant, but a theorem's statement matters when a
definition uses it, e.g. through `Classical.choose`). Constants from outside the repo
(Mathlib, core) are counted but treated as trusted.
-/

open Lean Meta Elab Command

partial def collect (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := #[root]
  while h : stack.size > 0 do
    let n := stack.back
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let mut refs := ci.type.getUsedConstants
    match ci with
    | .thmInfo _ => pure ()
    | _ => if let some v := ci.value? (allowOpaque := true) then refs := refs ++ v.getUsedConstants
    if let .inductInfo ii := ci then refs := refs ++ ii.ctors.toArray
    for r in refs do
      if !seen.contains r then stack := stack.push r
  return seen

def kindOf : ConstantInfo → String
  | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "AXIOM" | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec" | .quotInfo _ => "quot"

run_cmd do
  let env ← getEnv
  let all := collect env `HodgeConjecture
  let mut loc : Array (String × String × Name) := #[]
  let mut external : Nat := 0
  for n in all.toList do
    let some ci := env.find? n | continue
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    if (`HodgeConjecture).isPrefixOf mod then
      if !(n.isInternal) then loc := loc.push (mod.toString, kindOf ci, n)
    else external := external + 1
  loc := loc.qsort (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.2.toString < b.2.2.toString))
  logInfo m!"repo-loc constants reachable: {loc.size}; external (Mathlib/core): {external}"
  for (mod, k, n) in loc do
    IO.println s!"{mod}\t{k}\t{n}"
