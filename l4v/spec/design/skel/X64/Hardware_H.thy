(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory Hardware_H
imports
  "../../machine/X64/MachineOps"
  State_H
begin

context Arch begin global_naming X64_H

#INCLUDE_HASKELL SEL4/Machine/Hardware/X64.lhs Platform=Platform.X64 CONTEXT X64_H NOT getMemoryRegions getDeviceRegions getKernelDevices loadWord storeWord storeWordVM getActiveIRQ ackInterrupt maskInterrupt configureTimer resetTimer debugPrint getRestartPC setNextPC clearMemory clearMemoryVM initMemory freeMemory setCurrentPD setGlobalPD setHardwareASID wordFromPDE wordFromPTE VMFaultType HypFaultType VMMapType VMPageSize pageBits pageBitsForSize toPAddr addrFromPPtr ptrFromPAddr setCurrentCR3 getCurrentCR3 invalidateTLB invalidateTLBEntry mfence wordFromPML4E wordFromPDPTE firstValidIODomain numIODomainIDBits hwASIDInvalidate getFaultAddress irqIntOffset maxPCIBus maxPCIDev maxPCIFunc numIOAPICs ioapicIRQLines ioapicMapPinToVector irqStateIRQIOAPICNew irqStateIRQMSINew updateIRQState X64IRQState in8 out8 in16 out16 in32 out32 invalidatePageStructureCache resetCR3 physBase archSetCurrentVSpaceRoot writeCR3 invalidateASID invalidateTranslationSingleASID invalidatePageStructureCacheASID ptTranslationBits

end

context begin interpretation Arch .
requalify_types vmrights
end

context Arch begin global_naming X64_H

#INCLUDE_HASKELL SEL4/Machine/Hardware/X64.lhs CONTEXT X64_H instanceproofs NOT HardwareASID VMFaultType VMPageSize VMPageEntry VMMapType HypFaultType

#INCLUDE_HASKELL SEL4/Machine/Hardware/X64.lhs CONTEXT X64_H ONLY wordFromPDE wordFromPTE wordFromPML4E wordFromPDPTE

end (* context X64 *)

end
