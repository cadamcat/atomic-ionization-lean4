import Lake
open Lake DSL

package AtomicIonization where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

/-- OpenAI's Coulomb libraries (Apache-2.0), vendored unchanged; see `THIRD_PARTY.md`. -/
lean_lib OAI where
  globs := #[.submodules `OAI.Analysis.CoulombRadii, .submodules `OAI.Analysis.CoulombIonization]

@[default_target]
lean_lib AtomicIonization
