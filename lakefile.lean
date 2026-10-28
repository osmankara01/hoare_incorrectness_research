import Lake
open Lake DSL

package hoare_incorrectness

@[default_target]
lean_lib Language where
  roots := #[`Language]

@[default_target]
lean_lib AExp where
  roots := #[`AExp]

@[default_target]
lean_lib PExp where
  roots := #[`PExp]

@[default_target]
lean_lib Incorrectness where
  globs := #[.submodules `Incorrectness]

@[default_target]
lean_lib MapLang
