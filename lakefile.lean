import Lake
open Lake DSL

package GMLAlgebra {
  moreLeanArgs := #["-Dlinter.unusedVariables=false"]
}

@[default_target]
lean_lib GMLAlgebra {}

require std from git "https://github.com/leanprover/std4.git"@"main"

require GMLInit from git "https://github.com/fgdorais/GMLInit.git"@"main"
