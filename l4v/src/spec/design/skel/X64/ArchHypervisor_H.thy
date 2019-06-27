(*
 * Copyright 2016, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

(*
  Hypervisor stub for X64
*)

theory ArchHypervisor_H
imports
  "../CNode_H"
  "../KI_Decls_H"
begin
context Arch begin global_naming X64_H


#INCLUDE_HASKELL SEL4/Kernel/Hypervisor/X64.lhs Arch= CONTEXT X64_H decls_only ArchInv= ArchLabels=
#INCLUDE_HASKELL SEL4/Kernel/Hypervisor/X64.lhs Arch= CONTEXT X64_H bodies_only ArchInv= ArchLabels=

end
end
