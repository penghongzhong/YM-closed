import Lake
open Lake DSL

package «YMUICV128Verify» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "516d31250e96c4e8e76888c3d8e2e43a9642b9ee"

lean_lib «YMUICV128Verify» where

-- Isolated, non-manuscript public verification workspace (feature branch only).
lean_lib PublicC30 where
  globs := #[.submodules `PublicC30]
  moreLeanArgs := #["-DwarningAsError=true"]

-- Existing kernel-proved Schwartz helper dependency closure, ported from the active YM workstream.
lean_lib YM where
  globs := #[.submodules `YM]
  moreLeanArgs := #["-DwarningAsError=true"]

-- Reused, previously official-pin audited Original15/16 analytic chain.
lean_lib YMConditional where
  globs := #[.submodules `YMConditional]
  moreLeanArgs := #["-DwarningAsError=true"]

-- Current isolated original-environment theorem certificates.
lean_lib YMOriginal where
  globs := #[.submodules `YMOriginal]
  moreLeanArgs := #["-DwarningAsError=true"]
