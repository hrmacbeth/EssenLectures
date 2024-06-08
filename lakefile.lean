import Lake
open Lake DSL

package «gromov-hyperbolicity» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, true⟩,
    ⟨`warningAsError, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ s!"c995db1feabfe4b1d204e24ac689001d44484bc9"

@[default_target]
lean_lib GromovHyperbolicity
