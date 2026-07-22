import Lake
open Lake DSL

package tapl

/-- One library per TAPL chapter; each chapter lives in its own subdirectory. -/
@[default_target] lean_lib «Chapter03» where
  globs := #[.submodules `Chapter03]

@[default_target] lean_lib «Chapter05» where
  globs := #[.submodules `Chapter05]
