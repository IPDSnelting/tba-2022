import Aesop

namespace TBA

open Lean
open Lean.Meta
open Lean.Elab.Tactic

@[aesop norm tactic]
def substVars : TacticM Unit :=
  liftMetaTactic fun mvarId => do
    for localDecl in (← getLCtx) do
      if let some (_, mvarId) ← observing? (substCore mvarId localDecl.fvarId <|> substCore mvarId localDecl.fvarId (symm := true)) then
        return [mvarId]
    throwError "nope"

@[aesop safe 100 tactic]
def split : TacticM Unit :=
  liftMetaTactic fun mvarId => do
    if let some mvarIds ← splitTarget? mvarId then
      return mvarIds
    throwError "nope"

@[aesop safe 1000 tactic]
def splitAt : TacticM Unit :=
  liftMetaTactic fun mvarId => do
    for localDecl in (← getLCtx) do
      if let some mvarIds ← splitLocalDecl? mvarId localDecl.fvarId then
        return mvarIds
    throwError "nope"

def simpAll : TacticM Unit := do
  let m ← getMainGoal
  evalTactic (← `(tactic| simp_all))
  if (← getGoals).isEmpty then
    return
  if (← getMainGoal) == m || (← inferType (mkMVar (← getMainGoal))) == (← inferType (mkMVar m)) then
    throwError "nope"

def elimAny : Aesop.RuleTac := fun input => do
  for localDecl in (← getLCtx) do
    if localDecl.isAuxDecl then
      continue
    try
    let imm ← Aesop.RuleBuilder.getImmediatePremises localDecl.userName localDecl.type none
    let out ← Aesop.RuleTac.forwardFVar localDecl.userName imm (clear := true) input
    if !out.applications.isEmpty then
      return out
    catch _ => pure ()
  return { applications := #[], postBranchState? := none }

end TBA
