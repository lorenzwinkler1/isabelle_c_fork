theory Tree_03_02_shallow imports "../../src/UML_Main" "../../src/compiler/OCL_compiler_static" "../../src/compiler/OCL_compiler_generator_dynamic" begin
generation_syntax [ shallow (generation_semantics [ analysis ]) ]

Class Aazz End
Class Bbyy End
Class Ccxx End
Class Ddww < Aazz End
Class Eevv < Aazz End
Class Ffuu < Aazz End
Class Ggtt < Bbyy End
Class Hhss < Bbyy End
Class Iirr < Bbyy End
Class Jjqq < Ccxx End
Class Kkpp < Ccxx End
Class Lloo < Ccxx End

(* 12 *)

Class.end

end
