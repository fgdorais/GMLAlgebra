import Lake
open Lake DSL

package GMLAlgebra {
  moreLeanArgs := #["-Dlinter.unusedVariables=false"]
}

@[default_target]
lean_lib GMLAlgebra {}

require GMLInit from git "https://github.com/fgdorais/GMLInit"@"main"
