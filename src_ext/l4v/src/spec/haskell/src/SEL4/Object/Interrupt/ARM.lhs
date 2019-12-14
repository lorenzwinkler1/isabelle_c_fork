%
% Copyright 2014, General Dynamics C4 Systems
%
% This software may be distributed and modified according to the terms of
% the GNU General Public License version 2. Note that NO WARRANTY is provided.
% See "LICENSE_GPLv2.txt" for details.
%
% @TAG(GD_GPL)
%

This module defines the machine-specific interrupt handling routines.

\begin{impdetails}

> {-# LANGUAGE CPP #-}

\end{impdetails}

> module SEL4.Object.Interrupt.ARM where

\begin{impdetails}

> import Prelude hiding (Word)
> import SEL4.Machine
> import SEL4.Model
> import SEL4.Object.Structures
> import SEL4.API.Failures
> import SEL4.API.Types
> import SEL4.API.InvocationLabels
> import SEL4.API.Invocation.ARM as ArchInv
> import SEL4.API.InvocationLabels.ARM as ArchLabels
> import {-# SOURCE #-} SEL4.Object.Interrupt (setIRQState, isIRQActive)
> import {-# SOURCE #-} SEL4.Kernel.CSpace
> import {-# SOURCE #-} SEL4.Object.CNode
> import qualified SEL4.Machine.Hardware.ARM as Arch
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
> import SEL4.Object.VCPU.TARGET (vgicMaintenance)
> import SEL4.Machine.Hardware.ARM.PLATFORM (irqVGICMaintenance, irqSMMU)
#endif

\end{impdetails}


> decodeIRQControlInvocation :: Word -> [Word] -> PPtr CTE -> [Capability] ->
>         KernelF SyscallError ArchInv.IRQControlInvocation
> decodeIRQControlInvocation label args srcSlot extraCaps =
>     case (invocationType label, args, extraCaps) of
>         (ArchInvocationLabel ArchLabels.ARMIRQIssueIRQHandler, irqW:triggerW:index:depth:_, cnode:_) -> do
>             checkIRQ irqW
>             let irq = toEnum (fromIntegral irqW) :: IRQ
>             irqActive <- withoutFailure $ isIRQActive irq
>             when irqActive $ throw RevokeFirst
>
>             destSlot <- lookupTargetSlot cnode
>                 (CPtr index) (fromIntegral depth)
>             ensureEmptySlot destSlot
>             return $ ArchInv.IssueIRQHandler irq destSlot srcSlot (triggerW /= 0)
>         (ArchInvocationLabel ArchLabels.ARMIRQIssueIRQHandler,_,_) -> throw TruncatedMessage
>         _ -> throw IllegalOperation

> performIRQControl :: ArchInv.IRQControlInvocation -> KernelP ()
> performIRQControl (ArchInv.IssueIRQHandler (IRQ irq) destSlot srcSlot trigger) = withoutPreemption $ do
>     doMachineOp $ Arch.setIRQTrigger irq trigger
>     -- do same thing as generic path in performIRQControl in Interrupt.lhs
>     setIRQState IRQSignal (IRQ irq)
>     cteInsert (IRQHandlerCap (IRQ irq)) srcSlot destSlot
>     return ()

> checkIRQ :: Word -> KernelF SyscallError ()
> checkIRQ irq = rangeCheck irq (fromEnum minIRQ) (fromEnum maxIRQ)

> handleReservedIRQ :: IRQ -> Kernel ()
> handleReservedIRQ irq = do
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>     -- case irq of IRQ irqVGICMaintenance -> vgicMaintenance -- FIXME how to properly handle IRQ for haskell translator here?
>     when (fromEnum irq == fromEnum irqVGICMaintenance) vgicMaintenance
>     return ()
#else
>     return () -- handleReservedIRQ does nothing on ARM
#endif

> initInterruptController :: Kernel ()
> initInterruptController = do
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>     setIRQState IRQReserved $ IRQ irqVGICMaintenance
#endif
#ifdef CONFIG_SMMU
>     setIRQState IRQReserved $ IRQ irqSMMU
#endif
>     return ()

