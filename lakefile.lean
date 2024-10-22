Basic Lean Project lakefile

import Lake
open Lake DSL

package «myProject» where
  -- add package configuration options here
  lean-version := "leanprover/lean4:stable"
  -- Needed if you want mathlib
  -- dependencies := #[{
  --   name := "mathlib",
  --   src := Source.git "https://github.com/leanprover-community/mathlib4.git" "main"
  -- }]
