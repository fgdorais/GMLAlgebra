import Lake
open Lake DSL

package GMLAlgebra {
  moreLeanArgs := #["-Dlinter.unusedVariables=false"]
}

@[defaultTarget]
lean_lib GMLAlgebra {}

require std from git "https://github.com/leanprover/std4.git"@"e564a554a3aa40ca8542928494ef161a1f79f2df"

require GMLInit from git "https://github.com/fgdorais/GMLInit.git"@"c4f9ed1507ec528e64be72bd1564b93ed973a713"
