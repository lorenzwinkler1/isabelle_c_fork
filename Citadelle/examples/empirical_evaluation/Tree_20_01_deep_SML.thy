theory Tree_20_01_deep_SML imports  "../../src/compiler/Generator_dynamic" begin
generation_syntax [ deep
                      (generation_semantics [ analysis (*, oid_start 10*) ])
                      skip_export
                      (THEORY Tree_20_01_generated_SML)
                      (IMPORTS ["../../../src/UML_Main", "../../../src/compiler/Static"]
                               "../../../src/compiler/Generator_dynamic")
                      SECTION
                      [ in SML module_name M ]
                      (output_directory "./doc") ]

Class Aazz End
Class Bbyy End
Class Ccxx End
Class Ddww End
Class Eevv End
Class Ffuu End
Class Ggtt End
Class Hhss End
Class Iirr End
Class Jjqq End
Class Kkpp End
Class Lloo End
Class Mmnn End
Class Nnmm End
Class Ooll End
Class Ppkk End
Class Qqjj End
Class Rrii End
Class Sshh End
Class Ttgg End

(* 20 *)

generation_syntax deep flush_all


end
