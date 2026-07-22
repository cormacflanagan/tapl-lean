import Lake
open Lake DSL

package tapl

/-- One library per TAPL chapter; each chapter lives in its own subdirectory. -/
@[default_target] lean_lib «Chapter03» where
  globs := #[.submodules `Chapter03]

@[default_target] lean_lib «Chapter05» where
  globs := #[.submodules `Chapter05]

@[default_target] lean_lib «Chapter06» where
  globs := #[.submodules `Chapter06]

@[default_target] lean_lib «Chapter07» where
  globs := #[.submodules `Chapter07]

@[default_target] lean_lib «Chapter08» where
  globs := #[.submodules `Chapter08]

@[default_target] lean_lib «Chapter09» where
  globs := #[.submodules `Chapter09]

@[default_target] lean_lib «Chapter10» where
  globs := #[.submodules `Chapter10]

@[default_target] lean_lib «Chapter11» where
  globs := #[.submodules `Chapter11]

@[default_target] lean_lib «Chapter15» where
  globs := #[.submodules `Chapter15]

@[default_target] lean_lib «Chapter20» where
  globs := #[.submodules `Chapter20]
