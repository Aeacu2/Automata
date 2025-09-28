import Lake
open Lake DSL

package "automata" where
  version := v!"0.1.0"
  keywords := #["math"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

@[default_target]
lean_lib «Automata» where
  -- add any library configuration options here

require Hammer from git "https://github.com/JOSHCLUNE/LeanHammer" @ "v4.23.0"

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.23.0"

require "chasenorman" / "Canonical"
