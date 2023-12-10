import Lake
open Lake DSL

package GMLAlgebra {
  moreLeanArgs := #["-Dlinter.unusedVariables=false"]
}

@[default_target]
lean_lib GMLAlgebra {}

require std from git "https://github.com/leanprover/std4" @ "main"

require extra from git "https://github.com/fgdorais/extra4" @ "main"

require logic from git "https://github.com/fgdorais/logic4" @ "main"

--require GMLInit from git "https://github.com/fgdorais/GMLInit"@"main"
