import Lake
open Lake DSL

package pb006audit

@[default_target]
lean_lib PB006Audit

lean_exe pb006bench where
  root := `Main
