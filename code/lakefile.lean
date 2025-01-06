import Lake
open Lake DSL

package "cse230wi25" where
  -- add package configuration options here

lean_lib «Cse230wi25» where
  -- add library configuration options here

@[default_target]
lean_exe "cse230wi25" where
  root := `Main
