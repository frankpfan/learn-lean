import Lake
open Lake DSL

package "TestProject" where
  version := v!"0.1.0"

@[default_target]
lean_lib «TestProject» where
  -- add library configuration options here
