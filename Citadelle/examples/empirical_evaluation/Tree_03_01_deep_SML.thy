theory Tree_03_01_deep_SML imports  "../../src/compiler/Generator_dynamic" begin
generation_syntax [ deep
                      (generation_semantics [ analysis (*, oid_start 10*) ])
                      skip_export
                      (THEORY Tree_03_01_generated_SML)
                      (IMPORTS ["../../../src/UML_Main", "../../../src/compiler/Static"]
                               "../../../src/compiler/Generator_dynamic")
                      SECTION
                      [ in SML module_name M ]
                      (output_directory "./doc") ]

Class Aazz End
Class Bbyy End
Class Ccxx End

(* 3 *)

generation_syntax deep flush_all


end
