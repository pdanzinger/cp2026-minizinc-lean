import Lake
open Lake DSL

package «leanproject» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.9.0-rc1"

require Qq from git
  --"https://github.com/leanprover-community/quote4" @ "v4.11.0"
  "https://github.com/leanprover-community/quote4" @ "a7bfa63f5dddbcab2d4e0569c4cac74b2585e2c6" --"44f57616b0d9b8f9e5606f2c58d01df54840eba7"


@[default_target]
lean_exe «leanproject» where
  root := `Main
