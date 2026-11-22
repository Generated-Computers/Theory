import Lake

open System Lake DSL

package GC where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩]

-- The same Mathlib commit as the Lean library of the OpenAI mathematics release.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

@[default_target] lean_lib GC where
  globs := #[`GC.+]

lean_lib ComparatorChallenges where globs := #[`ComparatorChallenges.+]

-- Fingerprints of statements, used by scripts/check_statements.py.
lean_lib StmtDump where srcDir := "scripts"
