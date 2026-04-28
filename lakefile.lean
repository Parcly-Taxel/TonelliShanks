import Lake
open Lake DSL

package "TonelliShanks" where
  version := v!"0.1.0"

lean_lib «TonelliShanks» where
  -- add library configuration options here

@[default_target]
lean_exe "tonellishanks" where
  root := `Main

require Velvet from git "https://github.com/verse-lab/velvet.git" @ "master"
