import Lake
open Lake DSL

package «lean-tcb» where
  version := v!"0.1.0"
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «LeanTcb» where
  srcDir := "."

lean_lib «LeanTcbTest» where
  srcDir := "test"
  globs := #[.submodules `LeanTcbTest]
