import Lake
open Lake DSL

package «YMUICV128Verify» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "516d31250e96c4e8e76888c3d8e2e43a9642b9ee"

lean_lib «YMUICV128Verify» where
