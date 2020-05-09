theory Tree_05_01_deep_self imports  "../../src/compiler/Generator_dynamic_sequential" begin
generation_syntax [ deep
                      (generation_semantics [ analysis (*, oid_start 10*) ])
                      skip_export
                      (THEORY Tree_05_01_generated_self)
                      (IMPORTS ["../../../src/uml_main/UML_Main", "../../../src/compiler/Static"]
                               "../../../src/compiler/Generator_dynamic_sequential")
                      SECTION
                      [ in self  ]
                      (output_directory "./doc") ]

Class Aazz End
Class Bbyy End
Class Ccxx End
Class Ddww End
Class Eevv End

(* 5 *)

generation_syntax deep flush_all


end
