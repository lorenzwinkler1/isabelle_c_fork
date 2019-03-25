(*
 * Portions Copyright 2018-2019 Université Paris-Saclay, Univ. Paris-Sud, France
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory TestSEL4
imports
  "../src/tools/c-parser/CTranslation"
begin

(*
 * Test to see if we can parse all of seL4.
 * Test to see if all C parsed values are equal without considering positions.
 *)
declare [[allow_underscore_idents]]
install_C_file all_parsing parse_then_stop
               \<comment> \<open>The following file can be meanwhile CTRL-clicked on it:\<close>
               \<open>../generated/spec/cspec/c/build/ARM/kernel_all.c_pp\<close>

end
