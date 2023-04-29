import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

package categories {
  -- add package configuration options here
}

lean_lib Categories {
  -- add library configuration options here
}

@[default_target]
lean_exe categories {
  root := `Main
}
