import Lake
open Lake DSL

package «gromov-hyperbolicity» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, true⟩,
    ⟨`warningAsError, false⟩,
    ⟨`linter.docPrime, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ s!"81eef4025c7e481f517bcb7369aad6db1be6ce51"

lean_lib Examples

lean_lib EssenLectures

@[default_target]
lean_lib GromovHyperbolicity
