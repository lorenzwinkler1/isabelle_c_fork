theory Tree_01_02_shallow imports "../../src/OCL_main" "../../src/OCL_compiler_static" begin
generation_syntax [ shallow (generation_semantics [ analysis ]) ]

Class Aazz End
Class Bbyy < Aazz End

(* 2 *)

Class.end

end
