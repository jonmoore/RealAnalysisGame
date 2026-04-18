import Lake
open Lake DSL

-- Use v4.21.0 - this is what lean4game currently supports
def stableLeanVersion : String := s!"v{Lean.versionString}"

/--
Use the GameServer from a `lean4game` folder lying next to the game on your local computer.
Activated with `lake update -Klean4game.local`.
-/
def LocalGameServer : Dependency := {
  name := `GameServer
  scope := "hhu-adam"
  src? := DependencySrc.path "../lean4game/server"
  version? := none
  opts := ∅
}

/--
Use the GameServer version from github.
Deactivate local version with `lake update -R`.
-/
def RemoteGameServer : Dependency := {
  name := `GameServer
  scope := "hhu-adam"
  src? := DependencySrc.git "https://github.com/leanprover-community/lean4game.git" "bump-v4.23.0" "server" -- TODO
  version? := none
  opts := ∅
}

/-
Choose GameServer dependency depending on whether `-Klean4game.local` has been passed to `lake`.
-/
open Lean in
#eval (do
  let gameServerName := if get_config? lean4game.local |>.isSome then
    ``LocalGameServer else ``RemoteGameServer
  modifyEnv (fun env => Lake.packageDepAttr.ext.addEntry env gameServerName)
  : Elab.Command.CommandElabM Unit)

-- Use latest stable mathlib
-- require "leanprover-community" / mathlib @ git stableLeanVersion
require mathlib from git "https://github.com/hrmacbeth/mathlib4" @ "fieldsimp-ineq"

package Game where
  /- Used in all cases. -/
  leanOptions := #[
    /- linter warnings might block the player. (IMPORTANT) -/
    ⟨`linter.all, false⟩,

-- THIS \/
    /- to display the values of let declarations, like `:= 42` (IMPORTANT)  -/
--    ⟨`pp.showLetValues, true⟩,
-- THIS /\

    /- make all assumptions always accessible. -/
    ⟨`tactic.hygienic, false⟩]
  /- Used when calling `lake build`. -/
  moreLeanArgs := #[
    -- TODO: replace with `lean4game.verbose`
    "-Dtrace.debug=false"]
  /- Used when opening a file in VSCode or when playing the game. -/
  moreServerOptions := #[
    -- TODO: replace with `lean4game.verbose`
    ⟨`trace.debug, true⟩]
  -- moreGlobalServerArgs := #["-M", "4096"]         --  jm


@[default_target]
lean_lib Game

@[test_driver]
lean_lib Test where
  globs := #[.submodules `Test]
