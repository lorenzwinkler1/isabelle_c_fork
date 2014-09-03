theory Tree_07_02_deep_SML imports  "../../src/compiler/OCL_compiler_generator_dynamic" begin
generation_syntax [ deep
                      (generation_semantics [ analysis (*, oid_start 10*) ])
                      skip_export
                      (THEORY Tree_07_02_generated_SML)
                      (IMPORTS ["../../../src/UML_Main", "../../../src/compiler/OCL_compiler_static"]
                               "../../../src/compiler/OCL_compiler_generator_dynamic")
                      SECTION
                      [ in SML module_name M (no_signatures) ]
                      (output_directory "./doc") ]

Class Aazz End
Class Bbyy End
Class Ccxx End
Class Ddww End
Class Eevv End
Class Ffuu End
Class Ggtt End
Class Hhss < Aazz End
Class Iirr < Aazz End
Class Jjqq < Aazz End
Class Kkpp < Aazz End
Class Lloo < Aazz End
Class Mmnn < Aazz End
Class Nnmm < Aazz End
Class Ooll < Bbyy End
Class Ppkk < Bbyy End
Class Qqjj < Bbyy End
Class Rrii < Bbyy End
Class Sshh < Bbyy End
Class Ttgg < Bbyy End
Class Uuff < Bbyy End
Class Vvee < Ccxx End
Class Wwdd < Ccxx End
Class Xxcc < Ccxx End
Class Yybb < Ccxx End
Class Zzaa < Ccxx End
Class Baba < Ccxx End
Class Bbbb < Ccxx End
Class Bcbc < Ddww End
Class Bdbd < Ddww End
Class Bebe < Ddww End
Class Bfbf < Ddww End
Class Bgbg < Ddww End
Class Bhbh < Ddww End
Class Bibi < Ddww End
Class Bjbj < Eevv End
Class Bkbk < Eevv End
Class Blbl < Eevv End
Class Bmbm < Eevv End
Class Bnbn < Eevv End
Class Bobo < Eevv End
Class Bpbp < Eevv End
Class Bqbq < Ffuu End
Class Brbr < Ffuu End
Class Bsbs < Ffuu End
Class Btbt < Ffuu End
Class Bubu < Ffuu End
Class Bvbv < Ffuu End
Class Bwbw < Ffuu End
Class Bxbx < Ggtt End
Class Byby < Ggtt End
Class Bzbz < Ggtt End
Class Caca < Ggtt End
Class Cbcb < Ggtt End
Class Cccc < Ggtt End
Class Cdcd < Ggtt End

(* 56 *)

generation_syntax deep flush_all


end
