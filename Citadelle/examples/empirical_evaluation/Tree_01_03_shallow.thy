theory Tree_01_03_shallow imports "../../src/UML_Main" "../../src/compiler/OCL_compiler_static" "../../src/compiler/OCL_compiler_generator_dynamic" begin
generation_syntax [ shallow (generation_semantics [ analysis ]) ]

Class Aazz End
Class Bbyy < Aazz End
Class Ccxx < Bbyy End

(* 3 *)

Class.end

end
