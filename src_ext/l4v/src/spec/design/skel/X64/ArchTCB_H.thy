(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchTCB_H
imports TCBDecls_H
begin

context Arch begin global_naming X64_H

#INCLUDE_HASKELL SEL4/Object/TCB/X64.lhs RegisterSet= CONTEXT X64_H

#INCLUDE_HASKELL SEL4/Object/TCB.lhs Arch= ONLY archThreadGet archThreadSet

end
end
