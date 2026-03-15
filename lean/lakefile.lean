import Lake
open Lake DSL

package «Penumbra» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.24.0"

-- Mathlib v4.24.0 transitive dependency pins for reproducibility.
-- These match the revisions in Mathlib's lake-manifest.json for v4.24.0.
require Cli from git
  "https://github.com/leanprover/lean4-cli" @ "91c18fa62838ad0ab7384c03c9684d99d306e1da"
require Qq from git
  "https://github.com/leanprover-community/quote4" @ "dea6a3361fa36d5a13f87333dc506ada582e025c"
require aesop from git
  "https://github.com/leanprover-community/aesop" @ "725ac8cd67acd70a7beaf47c3725e23484c1ef50"
require importGraph from git
  "https://github.com/leanprover-community/import-graph" @ "d768126816be17600904726ca7976b185786e6b9"
require LeanSearchClient from git
  "https://github.com/leanprover-community/LeanSearchClient" @ "99657ad92e23804e279f77ea6dbdeebaa1317b98"
require plausible from git
  "https://github.com/leanprover-community/plausible" @ "dfd06ebfe8d0e8fa7faba9cb5e5a2e74e7bd2805"
require batteries from git
  "https://github.com/leanprover-community/batteries" @ "8da40b72fece29b7d3fe3d768bac4c8910ce9bee"
require proofwidgets from git
  "https://github.com/leanprover-community/ProofWidgets4" @ "b21695ed5db9bd30f7816621fa9ac142cae39a8f"
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.24.0"

@[default_target]
lean_lib «HeytingLean» where

lean_lib «Penumbra» where
