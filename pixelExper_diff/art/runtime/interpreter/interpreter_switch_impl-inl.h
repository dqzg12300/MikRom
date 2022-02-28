/*
 * Copyright (C) 2012 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#ifndef ART_RUNTIME_INTERPRETER_INTERPRETER_SWITCH_IMPL_INL_H_
#define ART_RUNTIME_INTERPRETER_INTERPRETER_SWITCH_IMPL_INL_H_

#include "interpreter_switch_impl.h"

#include "base/enums.h"
#include "base/globals.h"
#include "base/memory_tool.h"
#include "base/quasi_atomic.h"
#include "dex/dex_file_types.h"
#include "dex/dex_instruction_list.h"
#include "experimental_flags.h"
#include "handle_scope.h"
#include "interpreter_common.h"
#include "interpreter/shadow_frame.h"
#include "jit/jit-inl.h"
#include "jvalue-inl.h"
#include "mirror/string-alloc-inl.h"
#include "mirror/throwable.h"
#include "nth_caller_visitor.h"
#include "safe_math.h"
#include "shadow_frame-inl.h"
#include "thread.h"
#include "verifier/method_verifier.h"

namespace art {
namespace interpreter {

// Short-lived helper class which executes single DEX bytecode.  It is inlined by compiler.
//
// The function names must match the names from dex_instruction_list.h and have no arguments.
//
// Any relevant execution information is stored in the fields - it should be kept to minimum.
//
// Helper methods may return boolean value - in which case 'false' always means
// "stop executing current opcode" (which does not necessarily exit the interpreter loop).
//
template<bool do_access_check, bool transaction_active>
class InstructionHandler {
 public:
  template <bool kMonitorCounting>
  static NO_INLINE void UnlockHeldMonitors(Thread* self, ShadowFrame* shadow_frame)
      REQUIRES_SHARED(Locks::mutator_lock_) {
    DCHECK(shadow_frame->GetForcePopFrame());
    // Unlock all monitors.
    if (kMonitorCounting && shadow_frame->GetMethod()->MustCountLocks()) {
      // Get the monitors from the shadow-frame monitor-count data.
      shadow_frame->GetLockCountData().VisitMonitors(
        [&](mirror::Object** obj) REQUIRES_SHARED(Locks::mutator_lock_) {
          // Since we don't use the 'obj' pointer after the DoMonitorExit everything should be fine
          // WRT suspension.
          DoMonitorExit<do_assignability_check>(self, shadow_frame, *obj);
        });
    } else {
      std::vector<verifier::MethodVerifier::DexLockInfo> locks;
      verifier::MethodVerifier::FindLocksAtDexPc(shadow_frame->GetMethod(),
                                                  shadow_frame->GetDexPC(),
                                                  &locks,
                                                  Runtime::Current()->GetTargetSdkVersion());
      for (const auto& reg : locks) {
        if (UNLIKELY(reg.dex_registers.empty())) {
          LOG(ERROR) << "Unable to determine reference locked by "
                      << shadow_frame->GetMethod()->PrettyMethod() << " at pc "
                      << shadow_frame->GetDexPC();
        } else {
          DoMonitorExit<do_assignability_check>(
              self, shadow_frame, shadow_frame->GetVRegReference(*reg.dex_registers.begin()));
        }
      }
    }
  }

  ALWAYS_INLINE WARN_UNUSED bool CheckForceReturn()
      REQUIRES_SHARED(Locks::mutator_lock_) {
    if (UNLIKELY(shadow_frame.GetForcePopFrame())) {
      DCHECK(PrevFrameWillRetry(self, shadow_frame))
          << "Pop frame forced without previous frame ready to retry instruction!";
      DCHECK(Runtime::Current()->AreNonStandardExitsEnabled());
      UnlockHeldMonitors<do_assignability_check>(self, &shadow_frame);
      DoMonitorCheckOnExit<do_assignability_check>(self, &shadow_frame);
      if (UNLIKELY(NeedsMethodExitEvent(instrumentation))) {
        SendMethodExitEvents(self,
                             instrumentation,
                             shadow_frame,
                             shadow_frame.GetThisObject(Accessor().InsSize()),
                             shadow_frame.GetMethod(),
                             inst->GetDexPc(Insns()),
                             JValue());
      }
      ctx->result = JValue(); /* Handled in caller. */
      exit_interpreter_loop = true;
      return false;
    }
    return true;
  }

  NO_INLINE WARN_UNUSED bool HandlePendingExceptionWithInstrumentationImpl(
      const instrumentation::Instrumentation* instr)
      REQUIRES_SHARED(Locks::mutator_lock_) {
    DCHECK(self->IsExceptionPending());
    self->AllowThreadSuspension();
    if (!CheckForceReturn()) {
      return false;
    }
    if (!MoveToExceptionHandler(self, shadow_frame, instr)) {
      /* Structured locking is to be enforced for abnormal termination, too. */
      DoMonitorCheckOnExit<do_assignability_check>(self, &shadow_frame);
      if (ctx->interpret_one_instruction) {
        /* Signal mterp to return to caller */
        shadow_frame.SetDexPC(dex::kDexNoIndex);
      }
      ctx->result = JValue(); /* Handled in caller. */
      exit_interpreter_loop = true;
      return false;  // Return to caller.
    }
    if (!CheckForceReturn()) {
      return false;
    }
    int32_t displacement =
        static_cast<int32_t>(shadow_frame.GetDexPC()) - static_cast<int32_t>(dex_pc);
    inst = inst->RelativeAt(displacement);
    return false;  // Stop executing this opcode and continue in the exception handler.
  }

  // Forwards the call to the NO_INLINE HandlePendingExceptionWithInstrumentationImpl.
  ALWAYS_INLINE WARN_UNUSED bool HandlePendingExceptionWithInstrumentation(
      const instrumentation::Instrumentation* instr)
      REQUIRES_SHARED(Locks::mutator_lock_) {
    // We need to help the compiler a bit to make the NO_INLINE call efficient.
    //  * All handler fields should be in registers, so we do not want to take the object
    //    address (for 'this' argument). Make a copy of the handler just for the slow path.
    //  * The modifiable fields should also be in registers, so we don't want to store their
    //    address even in the handler copy. Make a copy of them just for the call as well.
    const Instruction* inst_copy = inst;
    bool exit_loop_copy = exit_interpreter_loop;
    InstructionHandler<do_access_check, transaction_active> handler_copy(
        ctx, instrumentation, self, shadow_frame, dex_pc, inst_copy, inst_data, exit_loop_copy);
    bool result = handler_copy.HandlePendingExceptionWithInstrumentationImpl(instr);
    inst = inst_copy;
    exit_interpreter_loop = exit_loop_copy;
    return result;
  }

  ALWAYS_INLINE WARN_UNUSED bool HandlePendingException()
      REQUIRES_SHARED(Locks::mutator_lock_) {
    return HandlePendingExceptionWithInstrumentation(instrumentation);
  }

  ALWAYS_INLINE WARN_UNUSED bool PossiblyHandlePendingExceptionOnInvokeImpl(
      bool is_exception_pending,
      const Instruction* next_inst)
      REQUIRES_SHARED(Locks::mutator_lock_) {
    if (UNLIKELY(shadow_frame.GetForceRetryInstruction())) {
      /* Don't need to do anything except clear the flag and exception. We leave the */
      /* instruction the same so it will be re-executed on the next go-around.       */
      DCHECK(inst->IsInvoke());
      shadow_frame.SetForceRetryInstruction(false);
      if (UNLIKELY(is_exception_pending)) {
        DCHECK(self->IsExceptionPending());
        if (kIsDebugBuild) {
          LOG(WARNING) << "Suppressing exception for instruction-retry: "
                       << self->GetException()->Dump();
        }
        self->ClearException();
      }
    } else if (UNLIKELY(is_exception_pending)) {
      /* Should have succeeded. */
      DCHECK(!shadow_frame.GetForceRetryInstruction());
      if (!HandlePendingException()) {
        return false;
      }
    } else {
      inst = next_inst;
    }
    return true;
  }

  ALWAYS_INLINE WARN_UNUSED bool PossiblyHandlePendingException(
      bool is_exception_pending,
      const Instruction* next_inst)
      REQUIRES_SHARED(Locks::mutator_lock_) {
    /* Should only be on invoke instructions. */
    DCHECK(!shadow_frame.GetForceRetryInstruction());
    if (UNLIKELY(is_exception_pending)) {
      if (!HandlePendingException()) {
        return false;
      }
    } else {
      inst = next_inst;
    }
    return true;
  }

  ALWAYS_INLINE WARN_UNUSED bool HandleMonitorChecks()
      REQUIRES_SHARED(Locks::mutator_lock_) {
    if (!DoMonitorCheckOnExit<do_assignability_check>(self, &shadow_frame)) {
      if (!HandlePendingException()) {
        return false;
      }
    }
    return true;
  }

  // Code to run before each dex instruction.
  ALWAYS_INLINE WARN_UNUSED bool Preamble()
      REQUIRES_SHARED(Locks::mutator_lock_) {
    /* We need to put this before & after the instrumentation to avoid having to put in a */
    /* post-script macro.                                                                 */
    if (!CheckForceReturn()) {
      return false;
    }
    if (UNLIKELY(instrumentation->HasDexPcListeners())) {
      uint8_t opcode = inst->Opcode(inst_data);
      bool is_move_result_object = (opcode == Instruction::MOVE_RESULT_OBJECT);
      JValue* save_ref = is_move_result_object ? &ctx->result_register : nullptr;
      if (UNLIKELY(!DoDexPcMoveEvent(self,
                                     Accessor(),
                                     shadow_frame,
                                     dex_pc,
                                     instrumentation,
                                     save_ref))) {
        if (!HandlePendingException()) {
          return false;
        }
      }
      if (!CheckForceReturn()) {
        return false;
      }
    }
    return true;
  }

  ALWAYS_INLINE WARN_UNUSED bool BranchInstrumentation(int32_t offset)
      REQUIRES_SHARED(Locks::mutator_lock_) {
    if (UNLIKELY(instrumentation->HasBranchListeners())) {
      instrumentation->Branch(self, shadow_frame.GetMethod(), dex_pc, offset);
    }
    JValue result;
    if (jit::Jit::MaybeDoOnStackReplacement(self,
                                            shadow_frame.GetMethod(),
                                            dex_pc,
                                            offset,
                                            &result)) {
      if (ctx->interpret_one_instruction) {
        /* OSR has completed execution of the method.  Signal mterp to return to caller */
        shadow_frame.SetDexPC(dex::kDexNoIndex);
      }
      ctx->result = result;
      exit_interpreter_loop = true;
      return false;
    }
    return true;
  }

  ALWAYS_INLINE void HotnessUpdate()
      REQUIRES_SHARED(Locks::mutator_lock_) {
    jit::Jit* jit = Runtime::Current()->GetJit();
    if (jit != nullptr) {
      jit->AddSamples(self, shadow_frame.GetMethod(), 1, /*with_backedges=*/ true);
    }
  }

  ALWAYS_INLINE WARN_UNUSED bool HandleAsyncException()
      REQUIRES_SHARED(Locks::mutator_lock_) {
    if (UNLIKELY(self->ObserveAsyncException())) {
      if (!HandlePendingException()) {
        return false;
      }
    }
    return true;
  }

  ALWAYS_INLINE void HandleBackwardBranch(int32_t offset)
      REQUIRES_SHARED(Locks::mutator_lock_) {
    if (IsBackwardBranch(offset)) {
      HotnessUpdate();
      /* Record new dex pc early to have consistent suspend point at loop header. */
      shadow_frame.SetDexPC(inst->GetDexPc(Insns()));
      self->AllowThreadSuspension();
    }
  }

  // Unlike most other events the DexPcMovedEvent can be sent when there is a pending exception (if
  // the next instruction is MOVE_EXCEPTION). This means it needs to be handled carefully to be able
  // to detect exceptions thrown by the DexPcMovedEvent itself. These exceptions could be thrown by
  // jvmti-agents while handling breakpoint or single step events. We had to move this into its own
  // function because it was making ExecuteSwitchImpl have too large a stack.
  NO_INLINE static bool DoDexPcMoveEvent(Thread* self,
                                         const CodeItemDataAccessor& accessor,
                                         const ShadowFrame& shadow_frame,
                                         uint32_t dex_pc,
                                         const instrumentation::Instrumentation* instrumentation,
                                         JValue* save_ref)
      REQUIRES_SHARED(Locks::mutator_lock_) {
    DCHECK(instrumentation->HasDexPcListeners());
    StackHandleScope<2> hs(self);
    Handle<mirror::Throwable> thr(hs.NewHandle(self->GetException()));
    mirror::Object* null_obj = nullptr;
    HandleWrapper<mirror::Object> h(
        hs.NewHandleWrapper(LIKELY(save_ref == nullptr) ? &null_obj : save_ref->GetGCRoot()));
    self->ClearException();
    instrumentation->DexPcMovedEvent(self,
                                     shadow_frame.GetThisObject(accessor.InsSize()),
                                     shadow_frame.GetMethod(),
                                     dex_pc);
    if (UNLIKELY(self->IsExceptionPending())) {
      // We got a new exception in the dex-pc-moved event.
      // We just let this exception replace the old one.
      // TODO It would be good to add the old exception to the
      // suppressed exceptions of the new one if possible.
      return false;
    } else {
      if (UNLIKELY(!thr.IsNull())) {
        self->SetException(thr.Get());
      }
      return true;
    }
  }

  static bool NeedsMethodExitEvent(const instrumentation::Instrumentation* ins)
      REQUIRES_SHARED(Locks::mutator_lock_) {
    return ins->HasMethodExitListeners() || ins->HasWatchedFramePopListeners();
  }

  // Sends the normal method exit event.
  // Returns true if the events succeeded and false if there is a pending exception.
  NO_INLINE static bool SendMethodExitEvents(
      Thread* self,
      const instrumentation::Instrumentation* instrumentation,
      const ShadowFrame& frame,
      ObjPtr<mirror::Object> thiz,
      ArtMethod* method,
      uint32_t dex_pc,
      const JValue& result)
      REQUIRES_SHARED(Locks::mutator_lock_) {
    bool had_event = false;
    // We don't send method-exit if it's a pop-frame. We still send frame_popped though.
    if (UNLIKELY(instrumentation->HasMethodExitListeners() && !frame.GetForcePopFrame())) {
      had_event = true;
      instrumentation->MethodExitEvent(self, thiz.Ptr(), method, dex_pc, result);
    }
    if (UNLIKELY(frame.NeedsNotifyPop() && instrumentation->HasWatchedFramePopListeners())) {
      had_event = true;
      instrumentation->WatchedFramePopped(self, frame);
    }
    if (UNLIKELY(had_event)) {
      return !self->IsExceptionPending();
    } else {
      return true;
    }
  }

#define BRANCH_INSTRUMENTATION(offset)                                                            \
  if (!BranchInstrumentation(offset)) {                                                           \
    return;                                                                                       \
  }

#define HANDLE_PENDING_EXCEPTION()                                                                \
  if (!HandlePendingException()) {                                                                \
    return;                                                                                       \
  }

#define POSSIBLY_HANDLE_PENDING_EXCEPTION(is_exception_pending, next_function)                    \
  if (!PossiblyHandlePendingException(is_exception_pending, inst->next_function())) {             \
    return;                                                                                       \
  }

#define POSSIBLY_HANDLE_PENDING_EXCEPTION_ON_INVOKE_POLYMORPHIC(is_exception_pending)             \
  if (!PossiblyHandlePendingExceptionOnInvokeImpl(is_exception_pending, inst->Next_4xx())) {      \
    return;                                                                                       \
  }

#define POSSIBLY_HANDLE_PENDING_EXCEPTION_ON_INVOKE(is_exception_pending)                         \
  if (!PossiblyHandlePendingExceptionOnInvokeImpl(is_exception_pending, inst->Next_3xx())) {      \
    return;                                                                                       \
  }

  ALWAYS_INLINE void NOP() REQUIRES_SHARED(Locks::mutator_lock_) {
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void MOVE() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVReg(inst->VRegA_12x(inst_data),
                         shadow_frame.GetVReg(inst->VRegB_12x(inst_data)));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void MOVE_FROM16() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVReg(inst->VRegA_22x(inst_data),
                         shadow_frame.GetVReg(inst->VRegB_22x()));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void MOVE_16() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVReg(inst->VRegA_32x(),
                         shadow_frame.GetVReg(inst->VRegB_32x()));
    inst = inst->Next_3xx();
  }

  ALWAYS_INLINE void MOVE_WIDE() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegLong(inst->VRegA_12x(inst_data),
                             shadow_frame.GetVRegLong(inst->VRegB_12x(inst_data)));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void MOVE_WIDE_FROM16() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegLong(inst->VRegA_22x(inst_data),
                             shadow_frame.GetVRegLong(inst->VRegB_22x()));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void MOVE_WIDE_16() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegLong(inst->VRegA_32x(),
                             shadow_frame.GetVRegLong(inst->VRegB_32x()));
    inst = inst->Next_3xx();
  }

  ALWAYS_INLINE void MOVE_OBJECT() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegReference(inst->VRegA_12x(inst_data),
                                  shadow_frame.GetVRegReference(inst->VRegB_12x(inst_data)));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void MOVE_OBJECT_FROM16() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegReference(inst->VRegA_22x(inst_data),
                                  shadow_frame.GetVRegReference(inst->VRegB_22x()));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void MOVE_OBJECT_16() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegReference(inst->VRegA_32x(),
                                  shadow_frame.GetVRegReference(inst->VRegB_32x()));
    inst = inst->Next_3xx();
  }

  ALWAYS_INLINE void MOVE_RESULT() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVReg(inst->VRegA_11x(inst_data), ResultRegister()->GetI());
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void MOVE_RESULT_WIDE() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegLong(inst->VRegA_11x(inst_data), ResultRegister()->GetJ());
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void MOVE_RESULT_OBJECT() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegReference(inst->VRegA_11x(inst_data), ResultRegister()->GetL());
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void MOVE_EXCEPTION() REQUIRES_SHARED(Locks::mutator_lock_) {
    ObjPtr<mirror::Throwable> exception = self->GetException();
    DCHECK(exception != nullptr) << "No pending exception on MOVE_EXCEPTION instruction";
    shadow_frame.SetVRegReference(inst->VRegA_11x(inst_data), exception);
    self->ClearException();
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void RETURN_VOID_NO_BARRIER() REQUIRES_SHARED(Locks::mutator_lock_) {
    JValue result;
    self->AllowThreadSuspension();
    if (!HandleMonitorChecks()) {
      return;
    }
    if (UNLIKELY(NeedsMethodExitEvent(instrumentation) &&
                 !SendMethodExitEvents(self,
                                       instrumentation,
                                       shadow_frame,
                                       shadow_frame.GetThisObject(Accessor().InsSize()),
                                       shadow_frame.GetMethod(),
                                       inst->GetDexPc(Insns()),
                                       result))) {
      if (!HandlePendingExceptionWithInstrumentation(nullptr)) {
        return;
      }
    }
    if (ctx->interpret_one_instruction) {
      /* Signal mterp to return to caller */
      shadow_frame.SetDexPC(dex::kDexNoIndex);
    }
    ctx->result = result;
    exit_interpreter_loop = true;
  }

  ALWAYS_INLINE void RETURN_VOID() REQUIRES_SHARED(Locks::mutator_lock_) {
    QuasiAtomic::ThreadFenceForConstructor();
    JValue result;
    self->AllowThreadSuspension();
    if (!HandleMonitorChecks()) {
      return;
    }
    if (UNLIKELY(NeedsMethodExitEvent(instrumentation) &&
                 !SendMethodExitEvents(self,
                                       instrumentation,
                                       shadow_frame,
                                       shadow_frame.GetThisObject(Accessor().InsSize()),
                                       shadow_frame.GetMethod(),
                                       inst->GetDexPc(Insns()),
                                       result))) {
      if (!HandlePendingExceptionWithInstrumentation(nullptr)) {
        return;
      }
    }
    if (ctx->interpret_one_instruction) {
      /* Signal mterp to return to caller */
      shadow_frame.SetDexPC(dex::kDexNoIndex);
    }
    ctx->result = result;
    exit_interpreter_loop = true;
  }

  ALWAYS_INLINE void RETURN() REQUIRES_SHARED(Locks::mutator_lock_) {
    JValue result;
    result.SetJ(0);
    result.SetI(shadow_frame.GetVReg(inst->VRegA_11x(inst_data)));
    self->AllowThreadSuspension();
    if (!HandleMonitorChecks()) {
      return;
    }
    if (UNLIKELY(NeedsMethodExitEvent(instrumentation) &&
                 !SendMethodExitEvents(self,
                                       instrumentation,
                                       shadow_frame,
                                       shadow_frame.GetThisObject(Accessor().InsSize()),
                                       shadow_frame.GetMethod(),
                                       inst->GetDexPc(Insns()),
                                       result))) {
      if (!HandlePendingExceptionWithInstrumentation(nullptr)) {
        return;
      }
    }
    if (ctx->interpret_one_instruction) {
      /* Signal mterp to return to caller */
      shadow_frame.SetDexPC(dex::kDexNoIndex);
    }
    ctx->result = result;
    exit_interpreter_loop = true;
  }

  ALWAYS_INLINE void RETURN_WIDE() REQUIRES_SHARED(Locks::mutator_lock_) {
    JValue result;
    result.SetJ(shadow_frame.GetVRegLong(inst->VRegA_11x(inst_data)));
    self->AllowThreadSuspension();
    if (!HandleMonitorChecks()) {
      return;
    }
    if (UNLIKELY(NeedsMethodExitEvent(instrumentation) &&
                 !SendMethodExitEvents(self,
                                       instrumentation,
                                       shadow_frame,
                                       shadow_frame.GetThisObject(Accessor().InsSize()),
                                       shadow_frame.GetMethod(),
                                       inst->GetDexPc(Insns()),
                                       result))) {
      if (!HandlePendingExceptionWithInstrumentation(nullptr)) {
        return;
      }
    }
    if (ctx->interpret_one_instruction) {
      /* Signal mterp to return to caller */
      shadow_frame.SetDexPC(dex::kDexNoIndex);
    }
    ctx->result = result;
    exit_interpreter_loop = true;
  }

  ALWAYS_INLINE void RETURN_OBJECT() REQUIRES_SHARED(Locks::mutator_lock_) {
    JValue result;
    self->AllowThreadSuspension();
    if (!HandleMonitorChecks()) {
      return;
    }
    const size_t ref_idx = inst->VRegA_11x(inst_data);
    ObjPtr<mirror::Object> obj_result = shadow_frame.GetVRegReference(ref_idx);
    if (do_assignability_check && obj_result != nullptr) {
      ObjPtr<mirror::Class> return_type = shadow_frame.GetMethod()->ResolveReturnType();
      // Re-load since it might have moved.
      obj_result = shadow_frame.GetVRegReference(ref_idx);
      if (return_type == nullptr) {
        // Return the pending exception.
        HANDLE_PENDING_EXCEPTION();
      }
      if (!obj_result->VerifierInstanceOf(return_type)) {
        // This should never happen.
        std::string temp1, temp2;
        self->ThrowNewExceptionF("Ljava/lang/InternalError;",
                                 "Returning '%s' that is not instance of return type '%s'",
                                 obj_result->GetClass()->GetDescriptor(&temp1),
                                 return_type->GetDescriptor(&temp2));
        HANDLE_PENDING_EXCEPTION();
      }
    }
    result.SetL(obj_result);
    if (UNLIKELY(NeedsMethodExitEvent(instrumentation) &&
                 !SendMethodExitEvents(self,
                                       instrumentation,
                                       shadow_frame,
                                       shadow_frame.GetThisObject(Accessor().InsSize()),
                                       shadow_frame.GetMethod(),
                                       inst->GetDexPc(Insns()),
                                       result))) {
      if (!HandlePendingExceptionWithInstrumentation(nullptr)) {
        return;
      }
    }
    // Re-load since it might have moved during the MethodExitEvent.
    result.SetL(shadow_frame.GetVRegReference(ref_idx));
    if (ctx->interpret_one_instruction) {
      /* Signal mterp to return to caller */
      shadow_frame.SetDexPC(dex::kDexNoIndex);
    }
    ctx->result = result;
    exit_interpreter_loop = true;
  }

  ALWAYS_INLINE void CONST_4() REQUIRES_SHARED(Locks::mutator_lock_) {
    uint4_t dst = inst->VRegA_11n(inst_data);
    int4_t val = inst->VRegB_11n(inst_data);
    shadow_frame.SetVReg(dst, val);
    if (val == 0) {
      shadow_frame.SetVRegReference(dst, nullptr);
    }
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void CONST_16() REQUIRES_SHARED(Locks::mutator_lock_) {
    uint8_t dst = inst->VRegA_21s(inst_data);
    int16_t val = inst->VRegB_21s();
    shadow_frame.SetVReg(dst, val);
    if (val == 0) {
      shadow_frame.SetVRegReference(dst, nullptr);
    }
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void CONST() REQUIRES_SHARED(Locks::mutator_lock_) {
    uint8_t dst = inst->VRegA_31i(inst_data);
    int32_t val = inst->VRegB_31i();
    shadow_frame.SetVReg(dst, val);
    if (val == 0) {
      shadow_frame.SetVRegReference(dst, nullptr);
    }
    inst = inst->Next_3xx();
  }

  ALWAYS_INLINE void CONST_HIGH16() REQUIRES_SHARED(Locks::mutator_lock_) {
    uint8_t dst = inst->VRegA_21h(inst_data);
    int32_t val = static_cast<int32_t>(inst->VRegB_21h() << 16);
    shadow_frame.SetVReg(dst, val);
    if (val == 0) {
      shadow_frame.SetVRegReference(dst, nullptr);
    }
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void CONST_WIDE_16() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegLong(inst->VRegA_21s(inst_data), inst->VRegB_21s());
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void CONST_WIDE_32() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegLong(inst->VRegA_31i(inst_data), inst->VRegB_31i());
    inst = inst->Next_3xx();
  }

  ALWAYS_INLINE void CONST_WIDE() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegLong(inst->VRegA_51l(inst_data), inst->VRegB_51l());
    inst = inst->Next_51l();
  }

  ALWAYS_INLINE void CONST_WIDE_HIGH16() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegLong(inst->VRegA_21h(inst_data),
                             static_cast<uint64_t>(inst->VRegB_21h()) << 48);
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void CONST_STRING() REQUIRES_SHARED(Locks::mutator_lock_) {
    ObjPtr<mirror::String> s = ResolveString(self,
                                             shadow_frame,
                                             dex::StringIndex(inst->VRegB_21c()));
    if (UNLIKELY(s == nullptr)) {
      HANDLE_PENDING_EXCEPTION();
    } else {
      shadow_frame.SetVRegReference(inst->VRegA_21c(inst_data), s);
      inst = inst->Next_2xx();
    }
  }

  ALWAYS_INLINE void CONST_STRING_JUMBO() REQUIRES_SHARED(Locks::mutator_lock_) {
    ObjPtr<mirror::String> s = ResolveString(self,
                                             shadow_frame,
                                             dex::StringIndex(inst->VRegB_31c()));
    if (UNLIKELY(s == nullptr)) {
      HANDLE_PENDING_EXCEPTION();
    } else {
      shadow_frame.SetVRegReference(inst->VRegA_31c(inst_data), s);
      inst = inst->Next_3xx();
    }
  }

  ALWAYS_INLINE void CONST_CLASS() REQUIRES_SHARED(Locks::mutator_lock_) {
    ObjPtr<mirror::Class> c = ResolveVerifyAndClinit(dex::TypeIndex(inst->VRegB_21c()),
                                                     shadow_frame.GetMethod(),
                                                     self,
                                                     false,
                                                     do_access_check);
    if (UNLIKELY(c == nullptr)) {
      HANDLE_PENDING_EXCEPTION();
    } else {
      shadow_frame.SetVRegReference(inst->VRegA_21c(inst_data), c);
      inst = inst->Next_2xx();
    }
  }

  ALWAYS_INLINE void CONST_METHOD_HANDLE() REQUIRES_SHARED(Locks::mutator_lock_) {
    ClassLinker* cl = Runtime::Current()->GetClassLinker();
    ObjPtr<mirror::MethodHandle> mh = cl->ResolveMethodHandle(self,
                                                              inst->VRegB_21c(),
                                                              shadow_frame.GetMethod());
    if (UNLIKELY(mh == nullptr)) {
      HANDLE_PENDING_EXCEPTION();
    } else {
      shadow_frame.SetVRegReference(inst->VRegA_21c(inst_data), mh);
      inst = inst->Next_2xx();
    }
  }

  ALWAYS_INLINE void CONST_METHOD_TYPE() REQUIRES_SHARED(Locks::mutator_lock_) {
    ClassLinker* cl = Runtime::Current()->GetClassLinker();
    ObjPtr<mirror::MethodType> mt = cl->ResolveMethodType(self,
                                                          dex::ProtoIndex(inst->VRegB_21c()),
                                                          shadow_frame.GetMethod());
    if (UNLIKELY(mt == nullptr)) {
      HANDLE_PENDING_EXCEPTION();
    } else {
      shadow_frame.SetVRegReference(inst->VRegA_21c(inst_data), mt);
      inst = inst->Next_2xx();
    }
  }

  ALWAYS_INLINE void MONITOR_ENTER() REQUIRES_SHARED(Locks::mutator_lock_) {
    if (!HandleAsyncException()) {
      return;
    }
    ObjPtr<mirror::Object> obj = shadow_frame.GetVRegReference(inst->VRegA_11x(inst_data));
    if (UNLIKELY(obj == nullptr)) {
      ThrowNullPointerExceptionFromInterpreter();
      HANDLE_PENDING_EXCEPTION();
    } else {
      DoMonitorEnter<do_assignability_check>(self, &shadow_frame, obj);
      POSSIBLY_HANDLE_PENDING_EXCEPTION(self->IsExceptionPending(), Next_1xx);
    }
  }

  ALWAYS_INLINE void MONITOR_EXIT() REQUIRES_SHARED(Locks::mutator_lock_) {
    if (!HandleAsyncException()) {
      return;
    }
    ObjPtr<mirror::Object> obj = shadow_frame.GetVRegReference(inst->VRegA_11x(inst_data));
    if (UNLIKELY(obj == nullptr)) {
      ThrowNullPointerExceptionFromInterpreter();
      HANDLE_PENDING_EXCEPTION();
    } else {
      DoMonitorExit<do_assignability_check>(self, &shadow_frame, obj);
      POSSIBLY_HANDLE_PENDING_EXCEPTION(self->IsExceptionPending(), Next_1xx);
    }
  }

  ALWAYS_INLINE void CHECK_CAST() REQUIRES_SHARED(Locks::mutator_lock_) {
    ObjPtr<mirror::Class> c = ResolveVerifyAndClinit(dex::TypeIndex(inst->VRegB_21c()),
                                                     shadow_frame.GetMethod(),
                                                     self,
                                                     false,
                                                     do_access_check);
    if (UNLIKELY(c == nullptr)) {
      HANDLE_PENDING_EXCEPTION();
    } else {
      ObjPtr<mirror::Object> obj = shadow_frame.GetVRegReference(inst->VRegA_21c(inst_data));
      if (UNLIKELY(obj != nullptr && !obj->InstanceOf(c))) {
        ThrowClassCastException(c, obj->GetClass());
        HANDLE_PENDING_EXCEPTION();
      } else {
        inst = inst->Next_2xx();
      }
    }
  }

  ALWAYS_INLINE void INSTANCE_OF() REQUIRES_SHARED(Locks::mutator_lock_) {
    ObjPtr<mirror::Class> c = ResolveVerifyAndClinit(dex::TypeIndex(inst->VRegC_22c()),
                                                     shadow_frame.GetMethod(),
                                                     self,
                                                     false,
                                                     do_access_check);
    if (UNLIKELY(c == nullptr)) {
      HANDLE_PENDING_EXCEPTION();
    } else {
      ObjPtr<mirror::Object> obj = shadow_frame.GetVRegReference(inst->VRegB_22c(inst_data));
      shadow_frame.SetVReg(inst->VRegA_22c(inst_data),
                           (obj != nullptr && obj->InstanceOf(c)) ? 1 : 0);
      inst = inst->Next_2xx();
    }
  }

  ALWAYS_INLINE void ARRAY_LENGTH() REQUIRES_SHARED(Locks::mutator_lock_) {
    ObjPtr<mirror::Object> array = shadow_frame.GetVRegReference(inst->VRegB_12x(inst_data));
    if (UNLIKELY(array == nullptr)) {
      ThrowNullPointerExceptionFromInterpreter();
      HANDLE_PENDING_EXCEPTION();
    } else {
      shadow_frame.SetVReg(inst->VRegA_12x(inst_data), array->AsArray()->GetLength());
      inst = inst->Next_1xx();
    }
  }

  ALWAYS_INLINE void NEW_INSTANCE() REQUIRES_SHARED(Locks::mutator_lock_) {
    ObjPtr<mirror::Object> obj = nullptr;
    ObjPtr<mirror::Class> c = ResolveVerifyAndClinit(dex::TypeIndex(inst->VRegB_21c()),
                                                     shadow_frame.GetMethod(),
                                                     self,
                                                     false,
                                                     do_access_check);
    if (LIKELY(c != nullptr)) {
      if (UNLIKELY(c->IsStringClass())) {
        gc::AllocatorType allocator_type = Runtime::Current()->GetHeap()->GetCurrentAllocator();
        obj = mirror::String::AllocEmptyString<true>(self, allocator_type);
      } else {
        obj = AllocObjectFromCode<true>(
            c.Ptr(),
            self,
            Runtime::Current()->GetHeap()->GetCurrentAllocator());
      }
    }
    if (UNLIKELY(obj == nullptr)) {
      HANDLE_PENDING_EXCEPTION();
    } else {
      obj->GetClass()->AssertInitializedOrInitializingInThread(self);
      // Don't allow finalizable objects to be allocated during a transaction since these can't
      // be finalized without a started runtime.
      if (transaction_active && obj->GetClass()->IsFinalizable()) {
        AbortTransactionF(self, "Allocating finalizable object in transaction: %s",
                          obj->PrettyTypeOf().c_str());
        HANDLE_PENDING_EXCEPTION();
      }
      shadow_frame.SetVRegReference(inst->VRegA_21c(inst_data), obj);
      inst = inst->Next_2xx();
    }
  }

  ALWAYS_INLINE void NEW_ARRAY() REQUIRES_SHARED(Locks::mutator_lock_) {
    int32_t length = shadow_frame.GetVReg(inst->VRegB_22c(inst_data));
    ObjPtr<mirror::Object> obj = AllocArrayFromCode<do_access_check, true>(
        dex::TypeIndex(inst->VRegC_22c()),
        length,
        shadow_frame.GetMethod(),
        self,
        Runtime::Current()->GetHeap()->GetCurrentAllocator());
    if (UNLIKELY(obj == nullptr)) {
      HANDLE_PENDING_EXCEPTION();
    } else {
      shadow_frame.SetVRegReference(inst->VRegA_22c(inst_data), obj);
      inst = inst->Next_2xx();
    }
  }

  ALWAYS_INLINE void FILLED_NEW_ARRAY() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success =
        DoFilledNewArray<false, do_access_check, transaction_active>(inst, shadow_frame, self,
                                                                     ResultRegister());
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_3xx);
  }

  ALWAYS_INLINE void FILLED_NEW_ARRAY_RANGE() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success =
        DoFilledNewArray<true, do_access_check, transaction_active>(inst, shadow_frame,
                                                                    self, ResultRegister());
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_3xx);
  }

  ALWAYS_INLINE void FILL_ARRAY_DATA() REQUIRES_SHARED(Locks::mutator_lock_) {
    const uint16_t* payload_addr = reinterpret_cast<const uint16_t*>(inst) + inst->VRegB_31t();
    const Instruction::ArrayDataPayload* payload =
        reinterpret_cast<const Instruction::ArrayDataPayload*>(payload_addr);
    ObjPtr<mirror::Object> obj = shadow_frame.GetVRegReference(inst->VRegA_31t(inst_data));
    bool success = FillArrayData(obj, payload);
    if (!success) {
      HANDLE_PENDING_EXCEPTION();
    }
    if (transaction_active) {
      RecordArrayElementsInTransaction(obj->AsArray(), payload->element_count);
    }
    inst = inst->Next_3xx();
  }

  ALWAYS_INLINE void THROW() REQUIRES_SHARED(Locks::mutator_lock_) {
    if (!HandleAsyncException()) {
      return;
    }
    ObjPtr<mirror::Object> exception =
        shadow_frame.GetVRegReference(inst->VRegA_11x(inst_data));
    if (UNLIKELY(exception == nullptr)) {
      ThrowNullPointerException("throw with null exception");
    } else if (do_assignability_check && !exception->GetClass()->IsThrowableClass()) {
      // This should never happen.
      std::string temp;
      self->ThrowNewExceptionF("Ljava/lang/InternalError;",
                               "Throwing '%s' that is not instance of Throwable",
                               exception->GetClass()->GetDescriptor(&temp));
    } else {
      self->SetException(exception->AsThrowable());
    }
    HANDLE_PENDING_EXCEPTION();
  }

  ALWAYS_INLINE void GOTO() REQUIRES_SHARED(Locks::mutator_lock_) {
    if (!HandleAsyncException()) {
      return;
    }
    int8_t offset = inst->VRegA_10t(inst_data);
    BRANCH_INSTRUMENTATION(offset);
    inst = inst->RelativeAt(offset);
    HandleBackwardBranch(offset);
  }

  ALWAYS_INLINE void GOTO_16() REQUIRES_SHARED(Locks::mutator_lock_) {
    if (!HandleAsyncException()) {
      return;
    }
    int16_t offset = inst->VRegA_20t();
    BRANCH_INSTRUMENTATION(offset);
    inst = inst->RelativeAt(offset);
    HandleBackwardBranch(offset);
  }

  ALWAYS_INLINE void GOTO_32() REQUIRES_SHARED(Locks::mutator_lock_) {
    if (!HandleAsyncException()) {
      return;
    }
    int32_t offset = inst->VRegA_30t();
    BRANCH_INSTRUMENTATION(offset);
    inst = inst->RelativeAt(offset);
    HandleBackwardBranch(offset);
  }

  ALWAYS_INLINE void PACKED_SWITCH() REQUIRES_SHARED(Locks::mutator_lock_) {
    int32_t offset = DoPackedSwitch(inst, shadow_frame, inst_data);
    BRANCH_INSTRUMENTATION(offset);
    inst = inst->RelativeAt(offset);
    HandleBackwardBranch(offset);
  }

  ALWAYS_INLINE void SPARSE_SWITCH() REQUIRES_SHARED(Locks::mutator_lock_) {
    int32_t offset = DoSparseSwitch(inst, shadow_frame, inst_data);
    BRANCH_INSTRUMENTATION(offset);
    inst = inst->RelativeAt(offset);
    HandleBackwardBranch(offset);
  }

#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wfloat-equal"


  ALWAYS_INLINE void CMPL_FLOAT() REQUIRES_SHARED(Locks::mutator_lock_) {
    float val1 = shadow_frame.GetVRegFloat(inst->VRegB_23x());
    float val2 = shadow_frame.GetVRegFloat(inst->VRegC_23x());
    int32_t result;
    if (val1 > val2) {
      result = 1;
    } else if (val1 == val2) {
      result = 0;
    } else {
      result = -1;
    }
    shadow_frame.SetVReg(inst->VRegA_23x(inst_data), result);
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void CMPG_FLOAT() REQUIRES_SHARED(Locks::mutator_lock_) {
    float val1 = shadow_frame.GetVRegFloat(inst->VRegB_23x());
    float val2 = shadow_frame.GetVRegFloat(inst->VRegC_23x());
    int32_t result;
    if (val1 < val2) {
      result = -1;
    } else if (val1 == val2) {
      result = 0;
    } else {
      result = 1;
    }
    shadow_frame.SetVReg(inst->VRegA_23x(inst_data), result);
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void CMPL_DOUBLE() REQUIRES_SHARED(Locks::mutator_lock_) {
    double val1 = shadow_frame.GetVRegDouble(inst->VRegB_23x());
    double val2 = shadow_frame.GetVRegDouble(inst->VRegC_23x());
    int32_t result;
    if (val1 > val2) {
      result = 1;
    } else if (val1 == val2) {
      result = 0;
    } else {
      result = -1;
    }
    shadow_frame.SetVReg(inst->VRegA_23x(inst_data), result);
    inst = inst->Next_2xx();
  }


  ALWAYS_INLINE void CMPG_DOUBLE() REQUIRES_SHARED(Locks::mutator_lock_) {
    double val1 = shadow_frame.GetVRegDouble(inst->VRegB_23x());
    double val2 = shadow_frame.GetVRegDouble(inst->VRegC_23x());
    int32_t result;
    if (val1 < val2) {
      result = -1;
    } else if (val1 == val2) {
      result = 0;
    } else {
      result = 1;
    }
    shadow_frame.SetVReg(inst->VRegA_23x(inst_data), result);
    inst = inst->Next_2xx();
  }

#pragma clang diagnostic pop


  ALWAYS_INLINE void CMP_LONG() REQUIRES_SHARED(Locks::mutator_lock_) {
    int64_t val1 = shadow_frame.GetVRegLong(inst->VRegB_23x());
    int64_t val2 = shadow_frame.GetVRegLong(inst->VRegC_23x());
    int32_t result;
    if (val1 > val2) {
      result = 1;
    } else if (val1 == val2) {
      result = 0;
    } else {
      result = -1;
    }
    shadow_frame.SetVReg(inst->VRegA_23x(inst_data), result);
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void IF_EQ() REQUIRES_SHARED(Locks::mutator_lock_) {
    if (shadow_frame.GetVReg(inst->VRegA_22t(inst_data)) ==
        shadow_frame.GetVReg(inst->VRegB_22t(inst_data))) {
      int16_t offset = inst->VRegC_22t();
      BRANCH_INSTRUMENTATION(offset);
      inst = inst->RelativeAt(offset);
      HandleBackwardBranch(offset);
    } else {
      BRANCH_INSTRUMENTATION(2);
      inst = inst->Next_2xx();
    }
  }

  ALWAYS_INLINE void IF_NE() REQUIRES_SHARED(Locks::mutator_lock_) {
    if (shadow_frame.GetVReg(inst->VRegA_22t(inst_data)) !=
        shadow_frame.GetVReg(inst->VRegB_22t(inst_data))) {
      int16_t offset = inst->VRegC_22t();
      BRANCH_INSTRUMENTATION(offset);
      inst = inst->RelativeAt(offset);
      HandleBackwardBranch(offset);
    } else {
      BRANCH_INSTRUMENTATION(2);
      inst = inst->Next_2xx();
    }
  }

  ALWAYS_INLINE void IF_LT() REQUIRES_SHARED(Locks::mutator_lock_) {
    if (shadow_frame.GetVReg(inst->VRegA_22t(inst_data)) <
        shadow_frame.GetVReg(inst->VRegB_22t(inst_data))) {
      int16_t offset = inst->VRegC_22t();
      BRANCH_INSTRUMENTATION(offset);
      inst = inst->RelativeAt(offset);
      HandleBackwardBranch(offset);
    } else {
      BRANCH_INSTRUMENTATION(2);
      inst = inst->Next_2xx();
    }
  }

  ALWAYS_INLINE void IF_GE() REQUIRES_SHARED(Locks::mutator_lock_) {
    if (shadow_frame.GetVReg(inst->VRegA_22t(inst_data)) >=
        shadow_frame.GetVReg(inst->VRegB_22t(inst_data))) {
      int16_t offset = inst->VRegC_22t();
      BRANCH_INSTRUMENTATION(offset);
      inst = inst->RelativeAt(offset);
      HandleBackwardBranch(offset);
    } else {
      BRANCH_INSTRUMENTATION(2);
      inst = inst->Next_2xx();
    }
  }

  ALWAYS_INLINE void IF_GT() REQUIRES_SHARED(Locks::mutator_lock_) {
    if (shadow_frame.GetVReg(inst->VRegA_22t(inst_data)) >
    shadow_frame.GetVReg(inst->VRegB_22t(inst_data))) {
      int16_t offset = inst->VRegC_22t();
      BRANCH_INSTRUMENTATION(offset);
      inst = inst->RelativeAt(offset);
      HandleBackwardBranch(offset);
    } else {
      BRANCH_INSTRUMENTATION(2);
      inst = inst->Next_2xx();
    }
  }

  ALWAYS_INLINE void IF_LE() REQUIRES_SHARED(Locks::mutator_lock_) {
    if (shadow_frame.GetVReg(inst->VRegA_22t(inst_data)) <=
        shadow_frame.GetVReg(inst->VRegB_22t(inst_data))) {
      int16_t offset = inst->VRegC_22t();
      BRANCH_INSTRUMENTATION(offset);
      inst = inst->RelativeAt(offset);
      HandleBackwardBranch(offset);
    } else {
      BRANCH_INSTRUMENTATION(2);
      inst = inst->Next_2xx();
    }
  }

  ALWAYS_INLINE void IF_EQZ() REQUIRES_SHARED(Locks::mutator_lock_) {
    if (shadow_frame.GetVReg(inst->VRegA_21t(inst_data)) == 0) {
      int16_t offset = inst->VRegB_21t();
      BRANCH_INSTRUMENTATION(offset);
      inst = inst->RelativeAt(offset);
      HandleBackwardBranch(offset);
    } else {
      BRANCH_INSTRUMENTATION(2);
      inst = inst->Next_2xx();
    }
  }

  ALWAYS_INLINE void IF_NEZ() REQUIRES_SHARED(Locks::mutator_lock_) {
    if (shadow_frame.GetVReg(inst->VRegA_21t(inst_data)) != 0) {
      int16_t offset = inst->VRegB_21t();
      BRANCH_INSTRUMENTATION(offset);
      inst = inst->RelativeAt(offset);
      HandleBackwardBranch(offset);
    } else {
      BRANCH_INSTRUMENTATION(2);
      inst = inst->Next_2xx();
    }
  }

  ALWAYS_INLINE void IF_LTZ() REQUIRES_SHARED(Locks::mutator_lock_) {
    if (shadow_frame.GetVReg(inst->VRegA_21t(inst_data)) < 0) {
      int16_t offset = inst->VRegB_21t();
      BRANCH_INSTRUMENTATION(offset);
      inst = inst->RelativeAt(offset);
      HandleBackwardBranch(offset);
    } else {
      BRANCH_INSTRUMENTATION(2);
      inst = inst->Next_2xx();
    }
  }

  ALWAYS_INLINE void IF_GEZ() REQUIRES_SHARED(Locks::mutator_lock_) {
    if (shadow_frame.GetVReg(inst->VRegA_21t(inst_data)) >= 0) {
      int16_t offset = inst->VRegB_21t();
      BRANCH_INSTRUMENTATION(offset);
      inst = inst->RelativeAt(offset);
      HandleBackwardBranch(offset);
    } else {
      BRANCH_INSTRUMENTATION(2);
      inst = inst->Next_2xx();
    }
  }

  ALWAYS_INLINE void IF_GTZ() REQUIRES_SHARED(Locks::mutator_lock_) {
    if (shadow_frame.GetVReg(inst->VRegA_21t(inst_data)) > 0) {
      int16_t offset = inst->VRegB_21t();
      BRANCH_INSTRUMENTATION(offset);
      inst = inst->RelativeAt(offset);
      HandleBackwardBranch(offset);
    } else {
      BRANCH_INSTRUMENTATION(2);
      inst = inst->Next_2xx();
    }
  }

  ALWAYS_INLINE void IF_LEZ() REQUIRES_SHARED(Locks::mutator_lock_) {
    if (shadow_frame.GetVReg(inst->VRegA_21t(inst_data)) <= 0) {
      int16_t offset = inst->VRegB_21t();
      BRANCH_INSTRUMENTATION(offset);
      inst = inst->RelativeAt(offset);
      HandleBackwardBranch(offset);
    } else {
      BRANCH_INSTRUMENTATION(2);
      inst = inst->Next_2xx();
    }
  }

  ALWAYS_INLINE void AGET_BOOLEAN() REQUIRES_SHARED(Locks::mutator_lock_) {
    ObjPtr<mirror::Object> a = shadow_frame.GetVRegReference(inst->VRegB_23x());
    if (UNLIKELY(a == nullptr)) {
      ThrowNullPointerExceptionFromInterpreter();
      HANDLE_PENDING_EXCEPTION();
    }
    int32_t index = shadow_frame.GetVReg(inst->VRegC_23x());
    ObjPtr<mirror::BooleanArray> array = a->AsBooleanArray();
    if (array->CheckIsValidIndex(index)) {
      shadow_frame.SetVReg(inst->VRegA_23x(inst_data), array->GetWithoutChecks(index));
      inst = inst->Next_2xx();
    } else {
      HANDLE_PENDING_EXCEPTION();
    }
  }

  ALWAYS_INLINE void AGET_BYTE() REQUIRES_SHARED(Locks::mutator_lock_) {
    ObjPtr<mirror::Object> a = shadow_frame.GetVRegReference(inst->VRegB_23x());
    if (UNLIKELY(a == nullptr)) {
      ThrowNullPointerExceptionFromInterpreter();
      HANDLE_PENDING_EXCEPTION();
    }
    int32_t index = shadow_frame.GetVReg(inst->VRegC_23x());
    ObjPtr<mirror::ByteArray> array = a->AsByteArray();
    if (array->CheckIsValidIndex(index)) {
      shadow_frame.SetVReg(inst->VRegA_23x(inst_data), array->GetWithoutChecks(index));
      inst = inst->Next_2xx();
    } else {
      HANDLE_PENDING_EXCEPTION();
    }
  }

  ALWAYS_INLINE void AGET_CHAR() REQUIRES_SHARED(Locks::mutator_lock_) {
    ObjPtr<mirror::Object> a = shadow_frame.GetVRegReference(inst->VRegB_23x());
    if (UNLIKELY(a == nullptr)) {
      ThrowNullPointerExceptionFromInterpreter();
      HANDLE_PENDING_EXCEPTION();
    }
    int32_t index = shadow_frame.GetVReg(inst->VRegC_23x());
    ObjPtr<mirror::CharArray> array = a->AsCharArray();
    if (array->CheckIsValidIndex(index)) {
      shadow_frame.SetVReg(inst->VRegA_23x(inst_data), array->GetWithoutChecks(index));
      inst = inst->Next_2xx();
    } else {
      HANDLE_PENDING_EXCEPTION();
    }
  }

  ALWAYS_INLINE void AGET_SHORT() REQUIRES_SHARED(Locks::mutator_lock_) {
    ObjPtr<mirror::Object> a = shadow_frame.GetVRegReference(inst->VRegB_23x());
    if (UNLIKELY(a == nullptr)) {
      ThrowNullPointerExceptionFromInterpreter();
      HANDLE_PENDING_EXCEPTION();
    }
    int32_t index = shadow_frame.GetVReg(inst->VRegC_23x());
    ObjPtr<mirror::ShortArray> array = a->AsShortArray();
    if (array->CheckIsValidIndex(index)) {
      shadow_frame.SetVReg(inst->VRegA_23x(inst_data), array->GetWithoutChecks(index));
      inst = inst->Next_2xx();
    } else {
      HANDLE_PENDING_EXCEPTION();
    }
  }

  ALWAYS_INLINE void AGET() REQUIRES_SHARED(Locks::mutator_lock_) {
    ObjPtr<mirror::Object> a = shadow_frame.GetVRegReference(inst->VRegB_23x());
    if (UNLIKELY(a == nullptr)) {
      ThrowNullPointerExceptionFromInterpreter();
      HANDLE_PENDING_EXCEPTION();
    }
    int32_t index = shadow_frame.GetVReg(inst->VRegC_23x());
    DCHECK(a->IsIntArray() || a->IsFloatArray()) << a->PrettyTypeOf();
    ObjPtr<mirror::IntArray> array = ObjPtr<mirror::IntArray>::DownCast(a);
    if (array->CheckIsValidIndex(index)) {
      shadow_frame.SetVReg(inst->VRegA_23x(inst_data), array->GetWithoutChecks(index));
      inst = inst->Next_2xx();
    } else {
      HANDLE_PENDING_EXCEPTION();
    }
  }

  ALWAYS_INLINE void AGET_WIDE() REQUIRES_SHARED(Locks::mutator_lock_) {
    ObjPtr<mirror::Object> a = shadow_frame.GetVRegReference(inst->VRegB_23x());
    if (UNLIKELY(a == nullptr)) {
      ThrowNullPointerExceptionFromInterpreter();
      HANDLE_PENDING_EXCEPTION();
    }
    int32_t index = shadow_frame.GetVReg(inst->VRegC_23x());
    DCHECK(a->IsLongArray() || a->IsDoubleArray()) << a->PrettyTypeOf();
    ObjPtr<mirror::LongArray> array = ObjPtr<mirror::LongArray>::DownCast(a);
    if (array->CheckIsValidIndex(index)) {
      shadow_frame.SetVRegLong(inst->VRegA_23x(inst_data), array->GetWithoutChecks(index));
      inst = inst->Next_2xx();
    } else {
      HANDLE_PENDING_EXCEPTION();
    }
  }

  ALWAYS_INLINE void AGET_OBJECT() REQUIRES_SHARED(Locks::mutator_lock_) {
    ObjPtr<mirror::Object> a = shadow_frame.GetVRegReference(inst->VRegB_23x());
    if (UNLIKELY(a == nullptr)) {
      ThrowNullPointerExceptionFromInterpreter();
      HANDLE_PENDING_EXCEPTION();
    }
    int32_t index = shadow_frame.GetVReg(inst->VRegC_23x());
    ObjPtr<mirror::ObjectArray<mirror::Object>> array = a->AsObjectArray<mirror::Object>();
    if (array->CheckIsValidIndex(index)) {
      shadow_frame.SetVRegReference(inst->VRegA_23x(inst_data), array->GetWithoutChecks(index));
      inst = inst->Next_2xx();
    } else {
      HANDLE_PENDING_EXCEPTION();
    }
  }

  ALWAYS_INLINE void APUT_BOOLEAN() REQUIRES_SHARED(Locks::mutator_lock_) {
    ObjPtr<mirror::Object> a = shadow_frame.GetVRegReference(inst->VRegB_23x());
    if (UNLIKELY(a == nullptr)) {
      ThrowNullPointerExceptionFromInterpreter();
      HANDLE_PENDING_EXCEPTION();
    }
    uint8_t val = shadow_frame.GetVReg(inst->VRegA_23x(inst_data));
    int32_t index = shadow_frame.GetVReg(inst->VRegC_23x());
    ObjPtr<mirror::BooleanArray> array = a->AsBooleanArray();
    if (array->CheckIsValidIndex(index)) {
      array->SetWithoutChecks<transaction_active>(index, val);
      inst = inst->Next_2xx();
    } else {
      HANDLE_PENDING_EXCEPTION();
    }
  }

  ALWAYS_INLINE void APUT_BYTE() REQUIRES_SHARED(Locks::mutator_lock_) {
    ObjPtr<mirror::Object> a = shadow_frame.GetVRegReference(inst->VRegB_23x());
    if (UNLIKELY(a == nullptr)) {
      ThrowNullPointerExceptionFromInterpreter();
      HANDLE_PENDING_EXCEPTION();
    }
    int8_t val = shadow_frame.GetVReg(inst->VRegA_23x(inst_data));
    int32_t index = shadow_frame.GetVReg(inst->VRegC_23x());
    ObjPtr<mirror::ByteArray> array = a->AsByteArray();
    if (array->CheckIsValidIndex(index)) {
      array->SetWithoutChecks<transaction_active>(index, val);
      inst = inst->Next_2xx();
    } else {
      HANDLE_PENDING_EXCEPTION();
    }
  }

  ALWAYS_INLINE void APUT_CHAR() REQUIRES_SHARED(Locks::mutator_lock_) {
    ObjPtr<mirror::Object> a = shadow_frame.GetVRegReference(inst->VRegB_23x());
    if (UNLIKELY(a == nullptr)) {
      ThrowNullPointerExceptionFromInterpreter();
      HANDLE_PENDING_EXCEPTION();
    }
    uint16_t val = shadow_frame.GetVReg(inst->VRegA_23x(inst_data));
    int32_t index = shadow_frame.GetVReg(inst->VRegC_23x());
    ObjPtr<mirror::CharArray> array = a->AsCharArray();
    if (array->CheckIsValidIndex(index)) {
      array->SetWithoutChecks<transaction_active>(index, val);
      inst = inst->Next_2xx();
    } else {
      HANDLE_PENDING_EXCEPTION();
    }
  }

  ALWAYS_INLINE void APUT_SHORT() REQUIRES_SHARED(Locks::mutator_lock_) {
    ObjPtr<mirror::Object> a = shadow_frame.GetVRegReference(inst->VRegB_23x());
    if (UNLIKELY(a == nullptr)) {
      ThrowNullPointerExceptionFromInterpreter();
      HANDLE_PENDING_EXCEPTION();
    }
    int16_t val = shadow_frame.GetVReg(inst->VRegA_23x(inst_data));
    int32_t index = shadow_frame.GetVReg(inst->VRegC_23x());
    ObjPtr<mirror::ShortArray> array = a->AsShortArray();
    if (array->CheckIsValidIndex(index)) {
      array->SetWithoutChecks<transaction_active>(index, val);
      inst = inst->Next_2xx();
    } else {
      HANDLE_PENDING_EXCEPTION();
    }
  }

  ALWAYS_INLINE void APUT() REQUIRES_SHARED(Locks::mutator_lock_) {
    ObjPtr<mirror::Object> a = shadow_frame.GetVRegReference(inst->VRegB_23x());
    if (UNLIKELY(a == nullptr)) {
      ThrowNullPointerExceptionFromInterpreter();
      HANDLE_PENDING_EXCEPTION();
    }
    int32_t val = shadow_frame.GetVReg(inst->VRegA_23x(inst_data));
    int32_t index = shadow_frame.GetVReg(inst->VRegC_23x());
    DCHECK(a->IsIntArray() || a->IsFloatArray()) << a->PrettyTypeOf();
    ObjPtr<mirror::IntArray> array = ObjPtr<mirror::IntArray>::DownCast(a);
    if (array->CheckIsValidIndex(index)) {
      array->SetWithoutChecks<transaction_active>(index, val);
      inst = inst->Next_2xx();
    } else {
      HANDLE_PENDING_EXCEPTION();
    }
  }

  ALWAYS_INLINE void APUT_WIDE() REQUIRES_SHARED(Locks::mutator_lock_) {
    ObjPtr<mirror::Object> a = shadow_frame.GetVRegReference(inst->VRegB_23x());
    if (UNLIKELY(a == nullptr)) {
      ThrowNullPointerExceptionFromInterpreter();
      HANDLE_PENDING_EXCEPTION();
    }
    int64_t val = shadow_frame.GetVRegLong(inst->VRegA_23x(inst_data));
    int32_t index = shadow_frame.GetVReg(inst->VRegC_23x());
    DCHECK(a->IsLongArray() || a->IsDoubleArray()) << a->PrettyTypeOf();
    ObjPtr<mirror::LongArray> array = ObjPtr<mirror::LongArray>::DownCast(a);
    if (array->CheckIsValidIndex(index)) {
      array->SetWithoutChecks<transaction_active>(index, val);
      inst = inst->Next_2xx();
    } else {
      HANDLE_PENDING_EXCEPTION();
    }
  }

  ALWAYS_INLINE void APUT_OBJECT() REQUIRES_SHARED(Locks::mutator_lock_) {
    ObjPtr<mirror::Object> a = shadow_frame.GetVRegReference(inst->VRegB_23x());
    if (UNLIKELY(a == nullptr)) {
      ThrowNullPointerExceptionFromInterpreter();
      HANDLE_PENDING_EXCEPTION();
    }
    int32_t index = shadow_frame.GetVReg(inst->VRegC_23x());
    ObjPtr<mirror::Object> val = shadow_frame.GetVRegReference(inst->VRegA_23x(inst_data));
    ObjPtr<mirror::ObjectArray<mirror::Object>> array = a->AsObjectArray<mirror::Object>();
    if (array->CheckIsValidIndex(index) && array->CheckAssignable(val)) {
      array->SetWithoutChecks<transaction_active>(index, val);
      inst = inst->Next_2xx();
    } else {
      HANDLE_PENDING_EXCEPTION();
    }
  }

  ALWAYS_INLINE void IGET_BOOLEAN() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoFieldGet<InstancePrimitiveRead, Primitive::kPrimBoolean, do_access_check>(
        self, shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void IGET_BYTE() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoFieldGet<InstancePrimitiveRead, Primitive::kPrimByte, do_access_check>(
        self, shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void IGET_CHAR() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoFieldGet<InstancePrimitiveRead, Primitive::kPrimChar, do_access_check>(
        self, shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void IGET_SHORT() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoFieldGet<InstancePrimitiveRead, Primitive::kPrimShort, do_access_check>(
        self, shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void IGET() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoFieldGet<InstancePrimitiveRead, Primitive::kPrimInt, do_access_check>(
        self, shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void IGET_WIDE() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoFieldGet<InstancePrimitiveRead, Primitive::kPrimLong, do_access_check>(
        self, shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void IGET_OBJECT() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoFieldGet<InstanceObjectRead, Primitive::kPrimNot, do_access_check>(
        self, shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void IGET_QUICK() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoIGetQuick<Primitive::kPrimInt>(shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void IGET_WIDE_QUICK() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoIGetQuick<Primitive::kPrimLong>(shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void IGET_OBJECT_QUICK() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoIGetQuick<Primitive::kPrimNot>(shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void IGET_BOOLEAN_QUICK() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoIGetQuick<Primitive::kPrimBoolean>(shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void IGET_BYTE_QUICK() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoIGetQuick<Primitive::kPrimByte>(shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void IGET_CHAR_QUICK() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoIGetQuick<Primitive::kPrimChar>(shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void IGET_SHORT_QUICK() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoIGetQuick<Primitive::kPrimShort>(shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void SGET_BOOLEAN() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoFieldGet<StaticPrimitiveRead, Primitive::kPrimBoolean, do_access_check,
        transaction_active>(self, shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void SGET_BYTE() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoFieldGet<StaticPrimitiveRead, Primitive::kPrimByte, do_access_check,
        transaction_active>(self, shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void SGET_CHAR() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoFieldGet<StaticPrimitiveRead, Primitive::kPrimChar, do_access_check,
        transaction_active>(self, shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void SGET_SHORT() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoFieldGet<StaticPrimitiveRead, Primitive::kPrimShort, do_access_check,
        transaction_active>(self, shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void SGET() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoFieldGet<StaticPrimitiveRead, Primitive::kPrimInt, do_access_check,
        transaction_active>(self, shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void SGET_WIDE() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoFieldGet<StaticPrimitiveRead, Primitive::kPrimLong, do_access_check,
        transaction_active>(self, shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void SGET_OBJECT() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoFieldGet<StaticObjectRead, Primitive::kPrimNot, do_access_check,
        transaction_active>(self, shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void IPUT_BOOLEAN() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoFieldPut<InstancePrimitiveWrite, Primitive::kPrimBoolean, do_access_check,
        transaction_active>(self, shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void IPUT_BYTE() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoFieldPut<InstancePrimitiveWrite, Primitive::kPrimByte, do_access_check,
        transaction_active>(self, shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void IPUT_CHAR() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoFieldPut<InstancePrimitiveWrite, Primitive::kPrimChar, do_access_check,
        transaction_active>(self, shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void IPUT_SHORT() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoFieldPut<InstancePrimitiveWrite, Primitive::kPrimShort, do_access_check,
        transaction_active>(self, shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void IPUT() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoFieldPut<InstancePrimitiveWrite, Primitive::kPrimInt, do_access_check,
        transaction_active>(self, shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void IPUT_WIDE() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoFieldPut<InstancePrimitiveWrite, Primitive::kPrimLong, do_access_check,
        transaction_active>(self, shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void IPUT_OBJECT() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoFieldPut<InstanceObjectWrite, Primitive::kPrimNot, do_access_check,
        transaction_active>(self, shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void IPUT_QUICK() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoIPutQuick<Primitive::kPrimInt, transaction_active>(
        shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void IPUT_BOOLEAN_QUICK() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoIPutQuick<Primitive::kPrimBoolean, transaction_active>(
        shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void IPUT_BYTE_QUICK() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoIPutQuick<Primitive::kPrimByte, transaction_active>(
        shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void IPUT_CHAR_QUICK() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoIPutQuick<Primitive::kPrimChar, transaction_active>(
        shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void IPUT_SHORT_QUICK() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoIPutQuick<Primitive::kPrimShort, transaction_active>(
        shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void IPUT_WIDE_QUICK() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoIPutQuick<Primitive::kPrimLong, transaction_active>(
        shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void IPUT_OBJECT_QUICK() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoIPutQuick<Primitive::kPrimNot, transaction_active>(
        shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void SPUT_BOOLEAN() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoFieldPut<StaticPrimitiveWrite, Primitive::kPrimBoolean, do_access_check,
        transaction_active>(self, shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void SPUT_BYTE() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoFieldPut<StaticPrimitiveWrite, Primitive::kPrimByte, do_access_check,
        transaction_active>(self, shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void SPUT_CHAR() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoFieldPut<StaticPrimitiveWrite, Primitive::kPrimChar, do_access_check,
        transaction_active>(self, shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void SPUT_SHORT() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoFieldPut<StaticPrimitiveWrite, Primitive::kPrimShort, do_access_check,
        transaction_active>(self, shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void SPUT() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoFieldPut<StaticPrimitiveWrite, Primitive::kPrimInt, do_access_check,
        transaction_active>(self, shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void SPUT_WIDE() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoFieldPut<StaticPrimitiveWrite, Primitive::kPrimLong, do_access_check,
        transaction_active>(self, shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void SPUT_OBJECT() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoFieldPut<StaticObjectWrite, Primitive::kPrimNot, do_access_check,
        transaction_active>(self, shadow_frame, inst, inst_data);
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void INVOKE_VIRTUAL() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoInvoke<kVirtual, false, do_access_check, /*is_mterp=*/ false>(
        self, shadow_frame, inst, inst_data, ResultRegister());
    POSSIBLY_HANDLE_PENDING_EXCEPTION_ON_INVOKE(!success);
  }

  ALWAYS_INLINE void INVOKE_VIRTUAL_RANGE() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoInvoke<kVirtual, true, do_access_check, /*is_mterp=*/ false>(
        self, shadow_frame, inst, inst_data, ResultRegister());
    POSSIBLY_HANDLE_PENDING_EXCEPTION_ON_INVOKE(!success);
  }

  ALWAYS_INLINE void INVOKE_SUPER() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoInvoke<kSuper, false, do_access_check, /*is_mterp=*/ false>(
        self, shadow_frame, inst, inst_data, ResultRegister());
    POSSIBLY_HANDLE_PENDING_EXCEPTION_ON_INVOKE(!success);
  }

  ALWAYS_INLINE void INVOKE_SUPER_RANGE() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoInvoke<kSuper, true, do_access_check, /*is_mterp=*/ false>(
        self, shadow_frame, inst, inst_data, ResultRegister());
    POSSIBLY_HANDLE_PENDING_EXCEPTION_ON_INVOKE(!success);
  }

  ALWAYS_INLINE void INVOKE_DIRECT() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoInvoke<kDirect, false, do_access_check, /*is_mterp=*/ false>(
        self, shadow_frame, inst, inst_data, ResultRegister());
    POSSIBLY_HANDLE_PENDING_EXCEPTION_ON_INVOKE(!success);
  }

  ALWAYS_INLINE void INVOKE_DIRECT_RANGE() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoInvoke<kDirect, true, do_access_check, /*is_mterp=*/ false>(
        self, shadow_frame, inst, inst_data, ResultRegister());
    POSSIBLY_HANDLE_PENDING_EXCEPTION_ON_INVOKE(!success);
  }

  ALWAYS_INLINE void INVOKE_INTERFACE() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoInvoke<kInterface, false, do_access_check, /*is_mterp=*/ false>(
        self, shadow_frame, inst, inst_data, ResultRegister());
    POSSIBLY_HANDLE_PENDING_EXCEPTION_ON_INVOKE(!success);
  }

  ALWAYS_INLINE void INVOKE_INTERFACE_RANGE() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoInvoke<kInterface, true, do_access_check, /*is_mterp=*/ false>(
        self, shadow_frame, inst, inst_data, ResultRegister());
    POSSIBLY_HANDLE_PENDING_EXCEPTION_ON_INVOKE(!success);
  }

  ALWAYS_INLINE void INVOKE_STATIC() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoInvoke<kStatic, false, do_access_check, /*is_mterp=*/ false>(
        self, shadow_frame, inst, inst_data, ResultRegister());
    POSSIBLY_HANDLE_PENDING_EXCEPTION_ON_INVOKE(!success);
  }

  ALWAYS_INLINE void INVOKE_STATIC_RANGE() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoInvoke<kStatic, true, do_access_check, /*is_mterp=*/ false>(
        self, shadow_frame, inst, inst_data, ResultRegister());
    POSSIBLY_HANDLE_PENDING_EXCEPTION_ON_INVOKE(!success);
  }

  ALWAYS_INLINE void INVOKE_VIRTUAL_QUICK() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoInvoke<kVirtual, false, do_access_check, /*is_mterp=*/ false,
        /*is_quick=*/ true>(self, shadow_frame, inst, inst_data, ResultRegister());
    POSSIBLY_HANDLE_PENDING_EXCEPTION_ON_INVOKE(!success);
  }

  ALWAYS_INLINE void INVOKE_VIRTUAL_RANGE_QUICK() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoInvoke<kVirtual, true, do_access_check, /*is_mterp=*/ false,
        /*is_quick=*/ true>(self, shadow_frame, inst, inst_data, ResultRegister());
    POSSIBLY_HANDLE_PENDING_EXCEPTION_ON_INVOKE(!success);
  }

  ALWAYS_INLINE void INVOKE_POLYMORPHIC() REQUIRES_SHARED(Locks::mutator_lock_) {
    DCHECK(Runtime::Current()->IsMethodHandlesEnabled());
    bool success = DoInvokePolymorphic</* is_range= */ false>(
        self, shadow_frame, inst, inst_data, ResultRegister());
    POSSIBLY_HANDLE_PENDING_EXCEPTION_ON_INVOKE_POLYMORPHIC(!success);
  }

  ALWAYS_INLINE void INVOKE_POLYMORPHIC_RANGE() REQUIRES_SHARED(Locks::mutator_lock_) {
    DCHECK(Runtime::Current()->IsMethodHandlesEnabled());
    bool success = DoInvokePolymorphic</* is_range= */ true>(
        self, shadow_frame, inst, inst_data, ResultRegister());
    POSSIBLY_HANDLE_PENDING_EXCEPTION_ON_INVOKE_POLYMORPHIC(!success);
  }

  ALWAYS_INLINE void INVOKE_CUSTOM() REQUIRES_SHARED(Locks::mutator_lock_) {
    DCHECK(Runtime::Current()->IsMethodHandlesEnabled());
    bool success = DoInvokeCustom</* is_range= */ false>(
        self, shadow_frame, inst, inst_data, ResultRegister());
    POSSIBLY_HANDLE_PENDING_EXCEPTION_ON_INVOKE(!success);
  }

  ALWAYS_INLINE void INVOKE_CUSTOM_RANGE() REQUIRES_SHARED(Locks::mutator_lock_) {
    DCHECK(Runtime::Current()->IsMethodHandlesEnabled());
    bool success = DoInvokeCustom</* is_range= */ true>(
        self, shadow_frame, inst, inst_data, ResultRegister());
    POSSIBLY_HANDLE_PENDING_EXCEPTION_ON_INVOKE(!success);
  }

  ALWAYS_INLINE void NEG_INT() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVReg(
        inst->VRegA_12x(inst_data), -shadow_frame.GetVReg(inst->VRegB_12x(inst_data)));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void NOT_INT() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVReg(
        inst->VRegA_12x(inst_data), ~shadow_frame.GetVReg(inst->VRegB_12x(inst_data)));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void NEG_LONG() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegLong(
        inst->VRegA_12x(inst_data), -shadow_frame.GetVRegLong(inst->VRegB_12x(inst_data)));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void NOT_LONG() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegLong(
        inst->VRegA_12x(inst_data), ~shadow_frame.GetVRegLong(inst->VRegB_12x(inst_data)));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void NEG_FLOAT() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegFloat(
        inst->VRegA_12x(inst_data), -shadow_frame.GetVRegFloat(inst->VRegB_12x(inst_data)));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void NEG_DOUBLE() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegDouble(
        inst->VRegA_12x(inst_data), -shadow_frame.GetVRegDouble(inst->VRegB_12x(inst_data)));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void INT_TO_LONG() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegLong(inst->VRegA_12x(inst_data),
                             shadow_frame.GetVReg(inst->VRegB_12x(inst_data)));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void INT_TO_FLOAT() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegFloat(inst->VRegA_12x(inst_data),
                              shadow_frame.GetVReg(inst->VRegB_12x(inst_data)));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void INT_TO_DOUBLE() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegDouble(inst->VRegA_12x(inst_data),
                               shadow_frame.GetVReg(inst->VRegB_12x(inst_data)));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void LONG_TO_INT() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVReg(inst->VRegA_12x(inst_data),
                         shadow_frame.GetVRegLong(inst->VRegB_12x(inst_data)));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void LONG_TO_FLOAT() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegFloat(inst->VRegA_12x(inst_data),
                              shadow_frame.GetVRegLong(inst->VRegB_12x(inst_data)));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void LONG_TO_DOUBLE() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegDouble(inst->VRegA_12x(inst_data),
                               shadow_frame.GetVRegLong(inst->VRegB_12x(inst_data)));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void FLOAT_TO_INT() REQUIRES_SHARED(Locks::mutator_lock_) {
    float val = shadow_frame.GetVRegFloat(inst->VRegB_12x(inst_data));
    int32_t result = art_float_to_integral<int32_t, float>(val);
    shadow_frame.SetVReg(inst->VRegA_12x(inst_data), result);
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void FLOAT_TO_LONG() REQUIRES_SHARED(Locks::mutator_lock_) {
    float val = shadow_frame.GetVRegFloat(inst->VRegB_12x(inst_data));
    int64_t result = art_float_to_integral<int64_t, float>(val);
    shadow_frame.SetVRegLong(inst->VRegA_12x(inst_data), result);
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void FLOAT_TO_DOUBLE() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegDouble(inst->VRegA_12x(inst_data),
                               shadow_frame.GetVRegFloat(inst->VRegB_12x(inst_data)));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void DOUBLE_TO_INT() REQUIRES_SHARED(Locks::mutator_lock_) {
    double val = shadow_frame.GetVRegDouble(inst->VRegB_12x(inst_data));
    int32_t result = art_float_to_integral<int32_t, double>(val);
    shadow_frame.SetVReg(inst->VRegA_12x(inst_data), result);
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void DOUBLE_TO_LONG() REQUIRES_SHARED(Locks::mutator_lock_) {
    double val = shadow_frame.GetVRegDouble(inst->VRegB_12x(inst_data));
    int64_t result = art_float_to_integral<int64_t, double>(val);
    shadow_frame.SetVRegLong(inst->VRegA_12x(inst_data), result);
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void DOUBLE_TO_FLOAT() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegFloat(inst->VRegA_12x(inst_data),
                              shadow_frame.GetVRegDouble(inst->VRegB_12x(inst_data)));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void INT_TO_BYTE() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVReg(inst->VRegA_12x(inst_data), static_cast<int8_t>(
        shadow_frame.GetVReg(inst->VRegB_12x(inst_data))));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void INT_TO_CHAR() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVReg(inst->VRegA_12x(inst_data), static_cast<uint16_t>(
        shadow_frame.GetVReg(inst->VRegB_12x(inst_data))));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void INT_TO_SHORT() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVReg(inst->VRegA_12x(inst_data), static_cast<int16_t>(
        shadow_frame.GetVReg(inst->VRegB_12x(inst_data))));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void ADD_INT() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVReg(inst->VRegA_23x(inst_data),
                         SafeAdd(shadow_frame.GetVReg(inst->VRegB_23x()),
                                 shadow_frame.GetVReg(inst->VRegC_23x())));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void SUB_INT() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVReg(inst->VRegA_23x(inst_data),
                         SafeSub(shadow_frame.GetVReg(inst->VRegB_23x()),
                                 shadow_frame.GetVReg(inst->VRegC_23x())));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void MUL_INT() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVReg(inst->VRegA_23x(inst_data),
                         SafeMul(shadow_frame.GetVReg(inst->VRegB_23x()),
                                 shadow_frame.GetVReg(inst->VRegC_23x())));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void DIV_INT() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoIntDivide(shadow_frame, inst->VRegA_23x(inst_data),
                               shadow_frame.GetVReg(inst->VRegB_23x()),
                               shadow_frame.GetVReg(inst->VRegC_23x()));
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void REM_INT() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoIntRemainder(shadow_frame, inst->VRegA_23x(inst_data),
                                  shadow_frame.GetVReg(inst->VRegB_23x()),
                                  shadow_frame.GetVReg(inst->VRegC_23x()));
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void SHL_INT() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVReg(inst->VRegA_23x(inst_data),
                         shadow_frame.GetVReg(inst->VRegB_23x()) <<
                         (shadow_frame.GetVReg(inst->VRegC_23x()) & 0x1f));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void SHR_INT() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVReg(inst->VRegA_23x(inst_data),
                         shadow_frame.GetVReg(inst->VRegB_23x()) >>
                         (shadow_frame.GetVReg(inst->VRegC_23x()) & 0x1f));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void USHR_INT() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVReg(inst->VRegA_23x(inst_data),
                         static_cast<uint32_t>(shadow_frame.GetVReg(inst->VRegB_23x())) >>
                         (shadow_frame.GetVReg(inst->VRegC_23x()) & 0x1f));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void AND_INT() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVReg(inst->VRegA_23x(inst_data),
                         shadow_frame.GetVReg(inst->VRegB_23x()) &
                         shadow_frame.GetVReg(inst->VRegC_23x()));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void OR_INT() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVReg(inst->VRegA_23x(inst_data),
                         shadow_frame.GetVReg(inst->VRegB_23x()) |
                         shadow_frame.GetVReg(inst->VRegC_23x()));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void XOR_INT() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVReg(inst->VRegA_23x(inst_data),
                         shadow_frame.GetVReg(inst->VRegB_23x()) ^
                         shadow_frame.GetVReg(inst->VRegC_23x()));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void ADD_LONG() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegLong(inst->VRegA_23x(inst_data),
                             SafeAdd(shadow_frame.GetVRegLong(inst->VRegB_23x()),
                                     shadow_frame.GetVRegLong(inst->VRegC_23x())));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void SUB_LONG() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegLong(inst->VRegA_23x(inst_data),
                             SafeSub(shadow_frame.GetVRegLong(inst->VRegB_23x()),
                                     shadow_frame.GetVRegLong(inst->VRegC_23x())));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void MUL_LONG() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegLong(inst->VRegA_23x(inst_data),
                             SafeMul(shadow_frame.GetVRegLong(inst->VRegB_23x()),
                                     shadow_frame.GetVRegLong(inst->VRegC_23x())));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void DIV_LONG() REQUIRES_SHARED(Locks::mutator_lock_) {
    DoLongDivide(shadow_frame, inst->VRegA_23x(inst_data),
                 shadow_frame.GetVRegLong(inst->VRegB_23x()),
                 shadow_frame.GetVRegLong(inst->VRegC_23x()));
    POSSIBLY_HANDLE_PENDING_EXCEPTION(self->IsExceptionPending(), Next_2xx);
  }

  ALWAYS_INLINE void REM_LONG() REQUIRES_SHARED(Locks::mutator_lock_) {
    DoLongRemainder(shadow_frame, inst->VRegA_23x(inst_data),
                    shadow_frame.GetVRegLong(inst->VRegB_23x()),
                    shadow_frame.GetVRegLong(inst->VRegC_23x()));
    POSSIBLY_HANDLE_PENDING_EXCEPTION(self->IsExceptionPending(), Next_2xx);
  }

  ALWAYS_INLINE void AND_LONG() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegLong(inst->VRegA_23x(inst_data),
                             shadow_frame.GetVRegLong(inst->VRegB_23x()) &
                             shadow_frame.GetVRegLong(inst->VRegC_23x()));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void OR_LONG() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegLong(inst->VRegA_23x(inst_data),
                             shadow_frame.GetVRegLong(inst->VRegB_23x()) |
                             shadow_frame.GetVRegLong(inst->VRegC_23x()));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void XOR_LONG() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegLong(inst->VRegA_23x(inst_data),
                             shadow_frame.GetVRegLong(inst->VRegB_23x()) ^
                             shadow_frame.GetVRegLong(inst->VRegC_23x()));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void SHL_LONG() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegLong(inst->VRegA_23x(inst_data),
                             shadow_frame.GetVRegLong(inst->VRegB_23x()) <<
                             (shadow_frame.GetVReg(inst->VRegC_23x()) & 0x3f));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void SHR_LONG() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegLong(inst->VRegA_23x(inst_data),
                             shadow_frame.GetVRegLong(inst->VRegB_23x()) >>
                             (shadow_frame.GetVReg(inst->VRegC_23x()) & 0x3f));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void USHR_LONG() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegLong(inst->VRegA_23x(inst_data),
                             static_cast<uint64_t>(shadow_frame.GetVRegLong(inst->VRegB_23x())) >>
                             (shadow_frame.GetVReg(inst->VRegC_23x()) & 0x3f));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void ADD_FLOAT() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegFloat(inst->VRegA_23x(inst_data),
                              shadow_frame.GetVRegFloat(inst->VRegB_23x()) +
                              shadow_frame.GetVRegFloat(inst->VRegC_23x()));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void SUB_FLOAT() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegFloat(inst->VRegA_23x(inst_data),
                              shadow_frame.GetVRegFloat(inst->VRegB_23x()) -
                              shadow_frame.GetVRegFloat(inst->VRegC_23x()));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void MUL_FLOAT() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegFloat(inst->VRegA_23x(inst_data),
                              shadow_frame.GetVRegFloat(inst->VRegB_23x()) *
                              shadow_frame.GetVRegFloat(inst->VRegC_23x()));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void DIV_FLOAT() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegFloat(inst->VRegA_23x(inst_data),
                              shadow_frame.GetVRegFloat(inst->VRegB_23x()) /
                              shadow_frame.GetVRegFloat(inst->VRegC_23x()));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void REM_FLOAT() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegFloat(inst->VRegA_23x(inst_data),
                              fmodf(shadow_frame.GetVRegFloat(inst->VRegB_23x()),
                                    shadow_frame.GetVRegFloat(inst->VRegC_23x())));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void ADD_DOUBLE() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegDouble(inst->VRegA_23x(inst_data),
                               shadow_frame.GetVRegDouble(inst->VRegB_23x()) +
                               shadow_frame.GetVRegDouble(inst->VRegC_23x()));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void SUB_DOUBLE() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegDouble(inst->VRegA_23x(inst_data),
                               shadow_frame.GetVRegDouble(inst->VRegB_23x()) -
                               shadow_frame.GetVRegDouble(inst->VRegC_23x()));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void MUL_DOUBLE() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegDouble(inst->VRegA_23x(inst_data),
                               shadow_frame.GetVRegDouble(inst->VRegB_23x()) *
                               shadow_frame.GetVRegDouble(inst->VRegC_23x()));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void DIV_DOUBLE() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegDouble(inst->VRegA_23x(inst_data),
                               shadow_frame.GetVRegDouble(inst->VRegB_23x()) /
                               shadow_frame.GetVRegDouble(inst->VRegC_23x()));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void REM_DOUBLE() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVRegDouble(inst->VRegA_23x(inst_data),
                               fmod(shadow_frame.GetVRegDouble(inst->VRegB_23x()),
                                    shadow_frame.GetVRegDouble(inst->VRegC_23x())));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void ADD_INT_2ADDR() REQUIRES_SHARED(Locks::mutator_lock_) {
    uint4_t vregA = inst->VRegA_12x(inst_data);
    shadow_frame.SetVReg(vregA, SafeAdd(shadow_frame.GetVReg(vregA),
                                        shadow_frame.GetVReg(inst->VRegB_12x(inst_data))));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void SUB_INT_2ADDR() REQUIRES_SHARED(Locks::mutator_lock_) {
    uint4_t vregA = inst->VRegA_12x(inst_data);
    shadow_frame.SetVReg(vregA,
                         SafeSub(shadow_frame.GetVReg(vregA),
                                 shadow_frame.GetVReg(inst->VRegB_12x(inst_data))));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void MUL_INT_2ADDR() REQUIRES_SHARED(Locks::mutator_lock_) {
    uint4_t vregA = inst->VRegA_12x(inst_data);
    shadow_frame.SetVReg(vregA,
                         SafeMul(shadow_frame.GetVReg(vregA),
                                 shadow_frame.GetVReg(inst->VRegB_12x(inst_data))));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void DIV_INT_2ADDR() REQUIRES_SHARED(Locks::mutator_lock_) {
    uint4_t vregA = inst->VRegA_12x(inst_data);
    bool success = DoIntDivide(shadow_frame, vregA, shadow_frame.GetVReg(vregA),
                               shadow_frame.GetVReg(inst->VRegB_12x(inst_data)));
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_1xx);
  }

  ALWAYS_INLINE void REM_INT_2ADDR() REQUIRES_SHARED(Locks::mutator_lock_) {
    uint4_t vregA = inst->VRegA_12x(inst_data);
    bool success = DoIntRemainder(shadow_frame, vregA, shadow_frame.GetVReg(vregA),
                                  shadow_frame.GetVReg(inst->VRegB_12x(inst_data)));
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_1xx);
  }

  ALWAYS_INLINE void SHL_INT_2ADDR() REQUIRES_SHARED(Locks::mutator_lock_) {
    uint4_t vregA = inst->VRegA_12x(inst_data);
    shadow_frame.SetVReg(vregA,
                         shadow_frame.GetVReg(vregA) <<
                         (shadow_frame.GetVReg(inst->VRegB_12x(inst_data)) & 0x1f));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void SHR_INT_2ADDR() REQUIRES_SHARED(Locks::mutator_lock_) {
    uint4_t vregA = inst->VRegA_12x(inst_data);
    shadow_frame.SetVReg(vregA,
                         shadow_frame.GetVReg(vregA) >>
                         (shadow_frame.GetVReg(inst->VRegB_12x(inst_data)) & 0x1f));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void USHR_INT_2ADDR() REQUIRES_SHARED(Locks::mutator_lock_) {
    uint4_t vregA = inst->VRegA_12x(inst_data);
    shadow_frame.SetVReg(vregA,
                         static_cast<uint32_t>(shadow_frame.GetVReg(vregA)) >>
                         (shadow_frame.GetVReg(inst->VRegB_12x(inst_data)) & 0x1f));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void AND_INT_2ADDR() REQUIRES_SHARED(Locks::mutator_lock_) {
    uint4_t vregA = inst->VRegA_12x(inst_data);
    shadow_frame.SetVReg(vregA,
                         shadow_frame.GetVReg(vregA) &
                         shadow_frame.GetVReg(inst->VRegB_12x(inst_data)));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void OR_INT_2ADDR() REQUIRES_SHARED(Locks::mutator_lock_) {
    uint4_t vregA = inst->VRegA_12x(inst_data);
    shadow_frame.SetVReg(vregA,
                         shadow_frame.GetVReg(vregA) |
                         shadow_frame.GetVReg(inst->VRegB_12x(inst_data)));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void XOR_INT_2ADDR() REQUIRES_SHARED(Locks::mutator_lock_) {
    uint4_t vregA = inst->VRegA_12x(inst_data);
    shadow_frame.SetVReg(vregA,
                         shadow_frame.GetVReg(vregA) ^
                         shadow_frame.GetVReg(inst->VRegB_12x(inst_data)));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void ADD_LONG_2ADDR() REQUIRES_SHARED(Locks::mutator_lock_) {
    uint4_t vregA = inst->VRegA_12x(inst_data);
    shadow_frame.SetVRegLong(vregA,
                             SafeAdd(shadow_frame.GetVRegLong(vregA),
                                     shadow_frame.GetVRegLong(inst->VRegB_12x(inst_data))));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void SUB_LONG_2ADDR() REQUIRES_SHARED(Locks::mutator_lock_) {
    uint4_t vregA = inst->VRegA_12x(inst_data);
    shadow_frame.SetVRegLong(vregA,
                             SafeSub(shadow_frame.GetVRegLong(vregA),
                                     shadow_frame.GetVRegLong(inst->VRegB_12x(inst_data))));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void MUL_LONG_2ADDR() REQUIRES_SHARED(Locks::mutator_lock_) {
    uint4_t vregA = inst->VRegA_12x(inst_data);
    shadow_frame.SetVRegLong(vregA,
                             SafeMul(shadow_frame.GetVRegLong(vregA),
                                     shadow_frame.GetVRegLong(inst->VRegB_12x(inst_data))));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void DIV_LONG_2ADDR() REQUIRES_SHARED(Locks::mutator_lock_) {
    uint4_t vregA = inst->VRegA_12x(inst_data);
    DoLongDivide(shadow_frame, vregA, shadow_frame.GetVRegLong(vregA),
                shadow_frame.GetVRegLong(inst->VRegB_12x(inst_data)));
    POSSIBLY_HANDLE_PENDING_EXCEPTION(self->IsExceptionPending(), Next_1xx);
  }

  ALWAYS_INLINE void REM_LONG_2ADDR() REQUIRES_SHARED(Locks::mutator_lock_) {
    uint4_t vregA = inst->VRegA_12x(inst_data);
    DoLongRemainder(shadow_frame, vregA, shadow_frame.GetVRegLong(vregA),
                    shadow_frame.GetVRegLong(inst->VRegB_12x(inst_data)));
    POSSIBLY_HANDLE_PENDING_EXCEPTION(self->IsExceptionPending(), Next_1xx);
  }

  ALWAYS_INLINE void AND_LONG_2ADDR() REQUIRES_SHARED(Locks::mutator_lock_) {
    uint4_t vregA = inst->VRegA_12x(inst_data);
    shadow_frame.SetVRegLong(vregA,
                             shadow_frame.GetVRegLong(vregA) &
                             shadow_frame.GetVRegLong(inst->VRegB_12x(inst_data)));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void OR_LONG_2ADDR() REQUIRES_SHARED(Locks::mutator_lock_) {
    uint4_t vregA = inst->VRegA_12x(inst_data);
    shadow_frame.SetVRegLong(vregA,
                             shadow_frame.GetVRegLong(vregA) |
                             shadow_frame.GetVRegLong(inst->VRegB_12x(inst_data)));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void XOR_LONG_2ADDR() REQUIRES_SHARED(Locks::mutator_lock_) {
    uint4_t vregA = inst->VRegA_12x(inst_data);
    shadow_frame.SetVRegLong(vregA,
                             shadow_frame.GetVRegLong(vregA) ^
                             shadow_frame.GetVRegLong(inst->VRegB_12x(inst_data)));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void SHL_LONG_2ADDR() REQUIRES_SHARED(Locks::mutator_lock_) {
    uint4_t vregA = inst->VRegA_12x(inst_data);
    shadow_frame.SetVRegLong(vregA,
                             shadow_frame.GetVRegLong(vregA) <<
                             (shadow_frame.GetVReg(inst->VRegB_12x(inst_data)) & 0x3f));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void SHR_LONG_2ADDR() REQUIRES_SHARED(Locks::mutator_lock_) {
    uint4_t vregA = inst->VRegA_12x(inst_data);
    shadow_frame.SetVRegLong(vregA,
                             shadow_frame.GetVRegLong(vregA) >>
                             (shadow_frame.GetVReg(inst->VRegB_12x(inst_data)) & 0x3f));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void USHR_LONG_2ADDR() REQUIRES_SHARED(Locks::mutator_lock_) {
    uint4_t vregA = inst->VRegA_12x(inst_data);
    shadow_frame.SetVRegLong(vregA,
                             static_cast<uint64_t>(shadow_frame.GetVRegLong(vregA)) >>
                             (shadow_frame.GetVReg(inst->VRegB_12x(inst_data)) & 0x3f));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void ADD_FLOAT_2ADDR() REQUIRES_SHARED(Locks::mutator_lock_) {
    uint4_t vregA = inst->VRegA_12x(inst_data);
    shadow_frame.SetVRegFloat(vregA,
                              shadow_frame.GetVRegFloat(vregA) +
                              shadow_frame.GetVRegFloat(inst->VRegB_12x(inst_data)));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void SUB_FLOAT_2ADDR() REQUIRES_SHARED(Locks::mutator_lock_) {
    uint4_t vregA = inst->VRegA_12x(inst_data);
    shadow_frame.SetVRegFloat(vregA,
                              shadow_frame.GetVRegFloat(vregA) -
                              shadow_frame.GetVRegFloat(inst->VRegB_12x(inst_data)));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void MUL_FLOAT_2ADDR() REQUIRES_SHARED(Locks::mutator_lock_) {
    uint4_t vregA = inst->VRegA_12x(inst_data);
    shadow_frame.SetVRegFloat(vregA,
                              shadow_frame.GetVRegFloat(vregA) *
                              shadow_frame.GetVRegFloat(inst->VRegB_12x(inst_data)));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void DIV_FLOAT_2ADDR() REQUIRES_SHARED(Locks::mutator_lock_) {
    uint4_t vregA = inst->VRegA_12x(inst_data);
    shadow_frame.SetVRegFloat(vregA,
                              shadow_frame.GetVRegFloat(vregA) /
                              shadow_frame.GetVRegFloat(inst->VRegB_12x(inst_data)));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void REM_FLOAT_2ADDR() REQUIRES_SHARED(Locks::mutator_lock_) {
    uint4_t vregA = inst->VRegA_12x(inst_data);
    shadow_frame.SetVRegFloat(vregA,
                              fmodf(shadow_frame.GetVRegFloat(vregA),
                                    shadow_frame.GetVRegFloat(inst->VRegB_12x(inst_data))));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void ADD_DOUBLE_2ADDR() REQUIRES_SHARED(Locks::mutator_lock_) {
    uint4_t vregA = inst->VRegA_12x(inst_data);
    shadow_frame.SetVRegDouble(vregA,
                               shadow_frame.GetVRegDouble(vregA) +
                               shadow_frame.GetVRegDouble(inst->VRegB_12x(inst_data)));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void SUB_DOUBLE_2ADDR() REQUIRES_SHARED(Locks::mutator_lock_) {
    uint4_t vregA = inst->VRegA_12x(inst_data);
    shadow_frame.SetVRegDouble(vregA,
                               shadow_frame.GetVRegDouble(vregA) -
                               shadow_frame.GetVRegDouble(inst->VRegB_12x(inst_data)));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void MUL_DOUBLE_2ADDR() REQUIRES_SHARED(Locks::mutator_lock_) {
    uint4_t vregA = inst->VRegA_12x(inst_data);
    shadow_frame.SetVRegDouble(vregA,
                               shadow_frame.GetVRegDouble(vregA) *
                               shadow_frame.GetVRegDouble(inst->VRegB_12x(inst_data)));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void DIV_DOUBLE_2ADDR() REQUIRES_SHARED(Locks::mutator_lock_) {
    uint4_t vregA = inst->VRegA_12x(inst_data);
    shadow_frame.SetVRegDouble(vregA,
                               shadow_frame.GetVRegDouble(vregA) /
                               shadow_frame.GetVRegDouble(inst->VRegB_12x(inst_data)));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void REM_DOUBLE_2ADDR() REQUIRES_SHARED(Locks::mutator_lock_) {
    uint4_t vregA = inst->VRegA_12x(inst_data);
    shadow_frame.SetVRegDouble(vregA,
                               fmod(shadow_frame.GetVRegDouble(vregA),
                                    shadow_frame.GetVRegDouble(inst->VRegB_12x(inst_data))));
    inst = inst->Next_1xx();
  }

  ALWAYS_INLINE void ADD_INT_LIT16() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVReg(inst->VRegA_22s(inst_data),
                         SafeAdd(shadow_frame.GetVReg(inst->VRegB_22s(inst_data)),
                                 inst->VRegC_22s()));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void RSUB_INT() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVReg(inst->VRegA_22s(inst_data),
                         SafeSub(inst->VRegC_22s(),
                                 shadow_frame.GetVReg(inst->VRegB_22s(inst_data))));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void MUL_INT_LIT16() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVReg(inst->VRegA_22s(inst_data),
                         SafeMul(shadow_frame.GetVReg(inst->VRegB_22s(inst_data)),
                                 inst->VRegC_22s()));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void DIV_INT_LIT16() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoIntDivide(shadow_frame, inst->VRegA_22s(inst_data),
                               shadow_frame.GetVReg(inst->VRegB_22s(inst_data)),
                               inst->VRegC_22s());
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void REM_INT_LIT16() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoIntRemainder(shadow_frame, inst->VRegA_22s(inst_data),
                                  shadow_frame.GetVReg(inst->VRegB_22s(inst_data)),
                                  inst->VRegC_22s());
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void AND_INT_LIT16() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVReg(inst->VRegA_22s(inst_data),
                         shadow_frame.GetVReg(inst->VRegB_22s(inst_data)) &
                         inst->VRegC_22s());
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void OR_INT_LIT16() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVReg(inst->VRegA_22s(inst_data),
                         shadow_frame.GetVReg(inst->VRegB_22s(inst_data)) |
                         inst->VRegC_22s());
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void XOR_INT_LIT16() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVReg(inst->VRegA_22s(inst_data),
                         shadow_frame.GetVReg(inst->VRegB_22s(inst_data)) ^
                         inst->VRegC_22s());
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void ADD_INT_LIT8() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVReg(inst->VRegA_22b(inst_data),
                         SafeAdd(shadow_frame.GetVReg(inst->VRegB_22b()), inst->VRegC_22b()));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void RSUB_INT_LIT8() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVReg(inst->VRegA_22b(inst_data),
                         SafeSub(inst->VRegC_22b(), shadow_frame.GetVReg(inst->VRegB_22b())));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void MUL_INT_LIT8() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVReg(inst->VRegA_22b(inst_data),
                         SafeMul(shadow_frame.GetVReg(inst->VRegB_22b()), inst->VRegC_22b()));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void DIV_INT_LIT8() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoIntDivide(shadow_frame, inst->VRegA_22b(inst_data),
                               shadow_frame.GetVReg(inst->VRegB_22b()), inst->VRegC_22b());
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void REM_INT_LIT8() REQUIRES_SHARED(Locks::mutator_lock_) {
    bool success = DoIntRemainder(shadow_frame, inst->VRegA_22b(inst_data),
                                  shadow_frame.GetVReg(inst->VRegB_22b()), inst->VRegC_22b());
    POSSIBLY_HANDLE_PENDING_EXCEPTION(!success, Next_2xx);
  }

  ALWAYS_INLINE void AND_INT_LIT8() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVReg(inst->VRegA_22b(inst_data),
                         shadow_frame.GetVReg(inst->VRegB_22b()) &
                         inst->VRegC_22b());
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void OR_INT_LIT8() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVReg(inst->VRegA_22b(inst_data),
                         shadow_frame.GetVReg(inst->VRegB_22b()) |
                         inst->VRegC_22b());
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void XOR_INT_LIT8() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVReg(inst->VRegA_22b(inst_data),
                         shadow_frame.GetVReg(inst->VRegB_22b()) ^
                         inst->VRegC_22b());
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void SHL_INT_LIT8() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVReg(inst->VRegA_22b(inst_data),
                         shadow_frame.GetVReg(inst->VRegB_22b()) <<
                         (inst->VRegC_22b() & 0x1f));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void SHR_INT_LIT8() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVReg(inst->VRegA_22b(inst_data),
                         shadow_frame.GetVReg(inst->VRegB_22b()) >>
                         (inst->VRegC_22b() & 0x1f));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void USHR_INT_LIT8() REQUIRES_SHARED(Locks::mutator_lock_) {
    shadow_frame.SetVReg(inst->VRegA_22b(inst_data),
                         static_cast<uint32_t>(shadow_frame.GetVReg(inst->VRegB_22b())) >>
                         (inst->VRegC_22b() & 0x1f));
    inst = inst->Next_2xx();
  }

  ALWAYS_INLINE void UNUSED_3E() REQUIRES_SHARED(Locks::mutator_lock_) {
    UnexpectedOpcode(inst, shadow_frame);
  }

  ALWAYS_INLINE void UNUSED_3F() REQUIRES_SHARED(Locks::mutator_lock_) {
    UnexpectedOpcode(inst, shadow_frame);
  }

  ALWAYS_INLINE void UNUSED_40() REQUIRES_SHARED(Locks::mutator_lock_) {
    UnexpectedOpcode(inst, shadow_frame);
  }

  ALWAYS_INLINE void UNUSED_41() REQUIRES_SHARED(Locks::mutator_lock_) {
    UnexpectedOpcode(inst, shadow_frame);
  }

  ALWAYS_INLINE void UNUSED_42() REQUIRES_SHARED(Locks::mutator_lock_) {
    UnexpectedOpcode(inst, shadow_frame);
  }

  ALWAYS_INLINE void UNUSED_43() REQUIRES_SHARED(Locks::mutator_lock_) {
    UnexpectedOpcode(inst, shadow_frame);
  }

  ALWAYS_INLINE void UNUSED_79() REQUIRES_SHARED(Locks::mutator_lock_) {
    UnexpectedOpcode(inst, shadow_frame);
  }

  ALWAYS_INLINE void UNUSED_7A() REQUIRES_SHARED(Locks::mutator_lock_) {
    UnexpectedOpcode(inst, shadow_frame);
  }

  ALWAYS_INLINE void UNUSED_F3() REQUIRES_SHARED(Locks::mutator_lock_) {
    UnexpectedOpcode(inst, shadow_frame);
  }

  ALWAYS_INLINE void UNUSED_F4() REQUIRES_SHARED(Locks::mutator_lock_) {
    UnexpectedOpcode(inst, shadow_frame);
  }

  ALWAYS_INLINE void UNUSED_F5() REQUIRES_SHARED(Locks::mutator_lock_) {
    UnexpectedOpcode(inst, shadow_frame);
  }

  ALWAYS_INLINE void UNUSED_F6() REQUIRES_SHARED(Locks::mutator_lock_) {
    UnexpectedOpcode(inst, shadow_frame);
  }

  ALWAYS_INLINE void UNUSED_F7() REQUIRES_SHARED(Locks::mutator_lock_) {
    UnexpectedOpcode(inst, shadow_frame);
  }

  ALWAYS_INLINE void UNUSED_F8() REQUIRES_SHARED(Locks::mutator_lock_) {
    UnexpectedOpcode(inst, shadow_frame);
  }

  ALWAYS_INLINE void UNUSED_F9() REQUIRES_SHARED(Locks::mutator_lock_) {
    UnexpectedOpcode(inst, shadow_frame);
  }

  ALWAYS_INLINE InstructionHandler(SwitchImplContext* ctx,
                                   const instrumentation::Instrumentation* instrumentation,
                                   Thread* self,
                                   ShadowFrame& shadow_frame,
                                   uint16_t dex_pc,
                                   const Instruction*& inst,
                                   uint16_t inst_data,
                                   bool& exit_interpreter_loop)
    : ctx(ctx),
      instrumentation(instrumentation),
      self(self),
      shadow_frame(shadow_frame),
      dex_pc(dex_pc),
      inst(inst),
      inst_data(inst_data),
      exit_interpreter_loop(exit_interpreter_loop) {
  }

 private:
  static constexpr bool do_assignability_check = do_access_check;

  const CodeItemDataAccessor& Accessor() { return ctx->accessor; }
  const uint16_t* Insns() { return ctx->accessor.Insns(); }
  JValue* ResultRegister() { return &ctx->result_register; }

  SwitchImplContext* const ctx;
  const instrumentation::Instrumentation* const instrumentation;
  Thread* const self;
  ShadowFrame& shadow_frame;
  uint32_t const dex_pc;
  const Instruction*& inst;
  uint16_t const inst_data;
  bool& exit_interpreter_loop;
};

#undef BRANCH_INSTRUMENTATION
#undef POSSIBLY_HANDLE_PENDING_EXCEPTION
#undef POSSIBLY_HANDLE_PENDING_EXCEPTION_ON_INVOKE
#undef POSSIBLY_HANDLE_PENDING_EXCEPTION_ON_INVOKE_POLYMORPHIC
#undef HANDLE_PENDING_EXCEPTION

// TODO On ASAN builds this function gets a huge stack frame. Since normally we run in the mterp
// this shouldn't cause any problems for stack overflow detection. Remove this once b/117341496 is
// fixed.
template<bool do_access_check, bool transaction_active>
ATTRIBUTE_NO_SANITIZE_ADDRESS void ExecuteSwitchImplCpp(SwitchImplContext* ctx) {
  Thread* self = ctx->self;
  const CodeItemDataAccessor& accessor = ctx->accessor;
  ShadowFrame& shadow_frame = ctx->shadow_frame;
  if (UNLIKELY(!shadow_frame.HasReferenceArray())) {
    LOG(FATAL) << "Invalid shadow frame for interpreter use";
    ctx->result = JValue();
    return;
  }
  self->VerifyStack();

  uint32_t dex_pc = shadow_frame.GetDexPC();
  const auto* const instrumentation = Runtime::Current()->GetInstrumentation();
  const uint16_t* const insns = accessor.Insns();
  const Instruction* inst = Instruction::At(insns + dex_pc);
  uint16_t inst_data;

  DCHECK(!shadow_frame.GetForceRetryInstruction())
      << "Entered interpreter from invoke without retry instruction being handled!";

  bool const interpret_one_instruction = ctx->interpret_one_instruction;
  while (true) {
    dex_pc = inst->GetDexPc(insns);
    shadow_frame.SetDexPC(dex_pc);
    TraceExecution(shadow_frame, inst, dex_pc);
    inst_data = inst->Fetch16(0);
    {
      bool exit_loop = false;
      InstructionHandler<do_access_check, transaction_active> handler(
          ctx, instrumentation, self, shadow_frame, dex_pc, inst, inst_data, exit_loop);
      if (!handler.Preamble()) {
        if (UNLIKELY(exit_loop)) {
          return;
        }
        if (UNLIKELY(interpret_one_instruction)) {
          break;
        }
        continue;
      }
    }
    switch (inst->Opcode(inst_data)) {
#define OPCODE_CASE(OPCODE, OPCODE_NAME, pname, f, i, a, e, v)                                    \
      case OPCODE: {                                                                              \
        bool exit_loop = false;                                                                   \
        InstructionHandler<do_access_check, transaction_active> handler(                          \
            ctx, instrumentation, self, shadow_frame, dex_pc, inst, inst_data, exit_loop);        \
        handler.OPCODE_NAME();                                                                    \
        /* TODO: Advance 'inst' here, instead of explicitly in each handler */                    \
        if (UNLIKELY(exit_loop)) {                                                                \
          return;                                                                                 \
        }                                                                                         \
        break;                                                                                    \
      }
DEX_INSTRUCTION_LIST(OPCODE_CASE)
#undef OPCODE_CASE
    }
    if (UNLIKELY(interpret_one_instruction)) {
      break;
    }
  }
  // Record where we stopped.
  shadow_frame.SetDexPC(inst->GetDexPc(insns));
  ctx->result = ctx->result_register;
  return;
}  // NOLINT(readability/fn_size)

}  // namespace interpreter
}  // namespace art

#endif  // ART_RUNTIME_INTERPRETER_INTERPRETER_SWITCH_IMPL_INL_H_
