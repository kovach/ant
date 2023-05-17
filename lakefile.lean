import Lake
open Lake DSL

package «dc» {
  -- add package configuration options here
}

lean_lib «DC» {
  -- add library configuration options here
}

@[default_target]
lean_exe «dc» {
  root := `Main
}

require std from git "https://github.com/leanprover/std4"@"6006307d2ceb8743fea7e00ba0036af8654d0347"