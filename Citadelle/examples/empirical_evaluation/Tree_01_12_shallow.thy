theory Tree_01_12_shallow imports "../../src/uml_main/UML_Main" "../../src/compiler/Static" "../../src/compiler/Generator_dynamic_sequential" begin
generation_syntax [ shallow (generation_semantics [ analysis ]) ]

Class Aazz End
Class Bbyy < Aazz End
Class Ccxx < Bbyy End
Class Ddww < Ccxx End
Class Eevv < Ddww End
Class Ffuu < Eevv End
Class Ggtt < Ffuu End
Class Hhss < Ggtt End
Class Iirr < Hhss End
Class Jjqq < Iirr End
Class Kkpp < Jjqq End
Class Lloo < Kkpp End

(* 12 *)

End!

end
