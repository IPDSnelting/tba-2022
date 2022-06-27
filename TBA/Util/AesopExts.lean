import Aesop

namespace TBA

open Lean
open Lean.Meta
open Lean.Elab.Tactic

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
