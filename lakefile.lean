import Lake
open Lake DSL

package «lean-tcb» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «LeanTcb» where
  srcDir := "."

lean_lib «LeanTcbTest» where
  srcDir := "test"
  globs := #[.submodules `LeanTcbTest]
