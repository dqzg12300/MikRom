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

#include "interpreter.h"

#include <limits>
#include <string_view>

#include "common_dex_operations.h"
#include "common_throws.h"
#include "dex/dex_file_types.h"
#include "interpreter_common.h"
#include "interpreter_mterp_impl.h"
#include "interpreter_switch_impl.h"
#include "jit/jit.h"
#include "jit/jit_code_cache.h"
#include "jvalue-inl.h"
#include "mirror/string-inl.h"
#include "mterp/mterp.h"
#include "nativehelper/scoped_local_ref.h"
#include "scoped_thread_state_change-inl.h"
#include "shadow_frame-inl.h"
#include "stack.h"
#include "thread-inl.h"
#include "unstarted_runtime.h"

namespace art {
namespace interpreter {

ALWAYS_INLINE static ObjPtr<mirror::Object> ObjArg(uint32_t arg)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  return reinterpret_cast<mirror::Object*>(arg);
}

static void InterpreterJni(Thread* self,
                           ArtMethod* method,
                           std::string_view shorty,
                           ObjPtr<mirror::Object> receiver,
                           uint32_t* args,
                           JValue* result)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  // TODO: The following enters JNI code using a typedef-ed function rather than the JNI compiler,
  //       it should be removed and JNI compiled stubs used instead.
  ScopedObjectAccessUnchecked soa(self);
  if (method->IsStatic()) {
    if (shorty == "L") {
      using fntype = jobject(JNIEnv*, jclass);
      fntype* const fn = reinterpret_cast<fntype*>(method->GetEntryPointFromJni());
      ScopedLocalRef<jclass> klass(soa.Env(),
                                   soa.AddLocalReference<jclass>(method->GetDeclaringClass()));
      jobject jresult;
      {
        ScopedThreadStateChange tsc(self, kNative);
        jresult = fn(soa.Env(), klass.get());
      }
      result->SetL(soa.Decode<mirror::Object>(jresult));
    } else if (shorty == "V") {
      using fntype = void(JNIEnv*, jclass);
      fntype* const fn = reinterpret_cast<fntype*>(method->GetEntryPointFromJni());
      ScopedLocalRef<jclass> klass(soa.Env(),
                                   soa.AddLocalReference<jclass>(method->GetDeclaringClass()));
      ScopedThreadStateChange tsc(self, kNative);
      fn(soa.Env(), klass.get());
    } else if (shorty == "Z") {
      using fntype = jboolean(JNIEnv*, jclass);
      fntype* const fn = reinterpret_cast<fntype*>(method->GetEntryPointFromJni());
      ScopedLocalRef<jclass> klass(soa.Env(),
                                   soa.AddLocalReference<jclass>(method->GetDeclaringClass()));
      ScopedThreadStateChange tsc(self, kNative);
      result->SetZ(fn(soa.Env(), klass.get()));
    } else if (shorty == "BI") {
      using fntype = jbyte(JNIEnv*, jclass, jint);
      fntype* const fn = reinterpret_cast<fntype*>(method->GetEntryPointFromJni());
      ScopedLocalRef<jclass> klass(soa.Env(),
                                   soa.AddLocalReference<jclass>(method->GetDeclaringClass()));
      ScopedThreadStateChange tsc(self, kNative);
      result->SetB(fn(soa.Env(), klass.get(), args[0]));
    } else if (shorty == "II") {
      using fntype = jint(JNIEnv*, jclass, jint);
      fntype* const fn = reinterpret_cast<fntype*>(method->GetEntryPointFromJni());
      ScopedLocalRef<jclass> klass(soa.Env(),
                                   soa.AddLocalReference<jclass>(method->GetDeclaringClass()));
      ScopedThreadStateChange tsc(self, kNative);
      result->SetI(fn(soa.Env(), klass.get(), args[0]));
    } else if (shorty == "LL") {
      using fntype = jobject(JNIEnv*, jclass, jobject);
      fntype* const fn = reinterpret_cast<fntype*>(method->GetEntryPointFromJni());
      ScopedLocalRef<jclass> klass(soa.Env(),
                                   soa.AddLocalReference<jclass>(method->GetDeclaringClass()));
      ScopedLocalRef<jobject> arg0(soa.Env(),
                                   soa.AddLocalReference<jobject>(ObjArg(args[0])));
      jobject jresult;
      {
        ScopedThreadStateChange tsc(self, kNative);
        jresult = fn(soa.Env(), klass.get(), arg0.get());
      }
      result->SetL(soa.Decode<mirror::Object>(jresult));
    } else if (shorty == "IIZ") {
      using fntype = jint(JNIEnv*, jclass, jint, jboolean);
      fntype* const fn = reinterpret_cast<fntype*>(method->GetEntryPointFromJni());
      ScopedLocalRef<jclass> klass(soa.Env(),
                                   soa.AddLocalReference<jclass>(method->GetDeclaringClass()));
      ScopedThreadStateChange tsc(self, kNative);
      result->SetI(fn(soa.Env(), klass.get(), args[0], args[1]));
    } else if (shorty == "ILI") {
      using fntype = jint(JNIEnv*, jclass, jobject, jint);
      fntype* const fn = reinterpret_cast<fntype*>(const_cast<void*>(
          method->GetEntryPointFromJni()));
      ScopedLocalRef<jclass> klass(soa.Env(),
                                   soa.AddLocalReference<jclass>(method->GetDeclaringClass()));
      ScopedLocalRef<jobject> arg0(soa.Env(),
                                   soa.AddLocalReference<jobject>(ObjArg(args[0])));
      ScopedThreadStateChange tsc(self, kNative);
      result->SetI(fn(soa.Env(), klass.get(), arg0.get(), args[1]));
    } else if (shorty == "SIZ") {
      using fntype = jshort(JNIEnv*, jclass, jint, jboolean);
      fntype* const fn =
          reinterpret_cast<fntype*>(const_cast<void*>(method->GetEntryPointFromJni()));
      ScopedLocalRef<jclass> klass(soa.Env(),
                                   soa.AddLocalReference<jclass>(method->GetDeclaringClass()));
      ScopedThreadStateChange tsc(self, kNative);
      result->SetS(fn(soa.Env(), klass.get(), args[0], args[1]));
    } else if (shorty == "VIZ") {
      using fntype = void(JNIEnv*, jclass, jint, jboolean);
      fntype* const fn = reinterpret_cast<fntype*>(method->GetEntryPointFromJni());
      ScopedLocalRef<jclass> klass(soa.Env(),
                                   soa.AddLocalReference<jclass>(method->GetDeclaringClass()));
      ScopedThreadStateChange tsc(self, kNative);
      fn(soa.Env(), klass.get(), args[0], args[1]);
    } else if (shorty == "ZLL") {
      using fntype = jboolean(JNIEnv*, jclass, jobject, jobject);
      fntype* const fn = reinterpret_cast<fntype*>(method->GetEntryPointFromJni());
      ScopedLocalRef<jclass> klass(soa.Env(),
                                   soa.AddLocalReference<jclass>(method->GetDeclaringClass()));
      ScopedLocalRef<jobject> arg0(soa.Env(),
                                   soa.AddLocalReference<jobject>(ObjArg(args[0])));
      ScopedLocalRef<jobject> arg1(soa.Env(),
                                   soa.AddLocalReference<jobject>(ObjArg(args[1])));
      ScopedThreadStateChange tsc(self, kNative);
      result->SetZ(fn(soa.Env(), klass.get(), arg0.get(), arg1.get()));
    } else if (shorty == "ZILL") {
      using fntype = jboolean(JNIEnv*, jclass, jint, jobject, jobject);
      fntype* const fn = reinterpret_cast<fntype*>(method->GetEntryPointFromJni());
      ScopedLocalRef<jclass> klass(soa.Env(),
                                   soa.AddLocalReference<jclass>(method->GetDeclaringClass()));
      ScopedLocalRef<jobject> arg1(soa.Env(),
                                   soa.AddLocalReference<jobject>(ObjArg(args[1])));
      ScopedLocalRef<jobject> arg2(soa.Env(),
                                   soa.AddLocalReference<jobject>(ObjArg(args[2])));
      ScopedThreadStateChange tsc(self, kNative);
      result->SetZ(fn(soa.Env(), klass.get(), args[0], arg1.get(), arg2.get()));
    } else if (shorty == "VILII") {
      using fntype = void(JNIEnv*, jclass, jint, jobject, jint, jint);
      fntype* const fn = reinterpret_cast<fntype*>(method->GetEntryPointFromJni());
      ScopedLocalRef<jclass> klass(soa.Env(),
                                   soa.AddLocalReference<jclass>(method->GetDeclaringClass()));
      ScopedLocalRef<jobject> arg1(soa.Env(),
                                   soa.AddLocalReference<jobject>(ObjArg(args[1])));
      ScopedThreadStateChange tsc(self, kNative);
      fn(soa.Env(), klass.get(), args[0], arg1.get(), args[2], args[3]);
    } else if (shorty == "VLILII") {
      using fntype = void(JNIEnv*, jclass, jobject, jint, jobject, jint, jint);
      fntype* const fn = reinterpret_cast<fntype*>(method->GetEntryPointFromJni());
      ScopedLocalRef<jclass> klass(soa.Env(),
                                   soa.AddLocalReference<jclass>(method->GetDeclaringClass()));
      ScopedLocalRef<jobject> arg0(soa.Env(),
                                   soa.AddLocalReference<jobject>(ObjArg(args[0])));
      ScopedLocalRef<jobject> arg2(soa.Env(),
                                   soa.AddLocalReference<jobject>(ObjArg(args[2])));
      ScopedThreadStateChange tsc(self, kNative);
      fn(soa.Env(), klass.get(), arg0.get(), args[1], arg2.get(), args[3], args[4]);
    } else {
      LOG(FATAL) << "Do something with static native method: " << method->PrettyMethod()
          << " shorty: " << shorty;
    }
  } else {
    if (shorty == "L") {
      using fntype = jobject(JNIEnv*, jobject);
      fntype* const fn = reinterpret_cast<fntype*>(method->GetEntryPointFromJni());
      ScopedLocalRef<jobject> rcvr(soa.Env(),
                                   soa.AddLocalReference<jobject>(receiver));
      jobject jresult;
      {
        ScopedThreadStateChange tsc(self, kNative);
        jresult = fn(soa.Env(), rcvr.get());
      }
      result->SetL(soa.Decode<mirror::Object>(jresult));
    } else if (shorty == "V") {
      using fntype = void(JNIEnv*, jobject);
      fntype* const fn = reinterpret_cast<fntype*>(method->GetEntryPointFromJni());
      ScopedLocalRef<jobject> rcvr(soa.Env(),
                                   soa.AddLocalReference<jobject>(receiver));
      ScopedThreadStateChange tsc(self, kNative);
      fn(soa.Env(), rcvr.get());
    } else if (shorty == "LL") {
      using fntype = jobject(JNIEnv*, jobject, jobject);
      fntype* const fn = reinterpret_cast<fntype*>(method->GetEntryPointFromJni());
      ScopedLocalRef<jobject> rcvr(soa.Env(),
                                   soa.AddLocalReference<jobject>(receiver));
      ScopedLocalRef<jobject> arg0(soa.Env(),
                                   soa.AddLocalReference<jobject>(ObjArg(args[0])));
      jobject jresult;
      {
        ScopedThreadStateChange tsc(self, kNative);
        jresult = fn(soa.Env(), rcvr.get(), arg0.get());
      }
      result->SetL(soa.Decode<mirror::Object>(jresult));
      ScopedThreadStateChange tsc(self, kNative);
    } else if (shorty == "III") {
      using fntype = jint(JNIEnv*, jobject, jint, jint);
      fntype* const fn = reinterpret_cast<fntype*>(method->GetEntryPointFromJni());
      ScopedLocalRef<jobject> rcvr(soa.Env(),
                                   soa.AddLocalReference<jobject>(receiver));
      ScopedThreadStateChange tsc(self, kNative);
      result->SetI(fn(soa.Env(), rcvr.get(), args[0], args[1]));
    } else {
      LOG(FATAL) << "Do something with native method: " << method->PrettyMethod()
          << " shorty: " << shorty;
    }
  }
}

enum InterpreterImplKind {
  kSwitchImplKind,        // Switch-based interpreter implementation.
  kMterpImplKind          // Assembly interpreter
};

#if ART_USE_CXX_INTERPRETER
static constexpr InterpreterImplKind kInterpreterImplKind = kSwitchImplKind;
#else
static constexpr InterpreterImplKind kInterpreterImplKind = kMterpImplKind;
#endif

static inline JValue Execute(
    Thread* self,
    const CodeItemDataAccessor& accessor,
    ShadowFrame& shadow_frame,
    JValue result_register,
    bool stay_in_interpreter = false,
    bool from_deoptimize = false) REQUIRES_SHARED(Locks::mutator_lock_) {
  DCHECK(!shadow_frame.GetMethod()->IsAbstract());
  DCHECK(!shadow_frame.GetMethod()->IsNative());

  // Check that we are using the right interpreter.
  if (kIsDebugBuild && self->UseMterp() != CanUseMterp()) {
    // The flag might be currently being updated on all threads. Retry with lock.
    MutexLock tll_mu(self, *Locks::thread_list_lock_);
    DCHECK_EQ(self->UseMterp(), CanUseMterp());
  }

  if (LIKELY(!from_deoptimize)) {  // Entering the method, but not via deoptimization.
    if (kIsDebugBuild) {
      CHECK_EQ(shadow_frame.GetDexPC(), 0u);
      self->AssertNoPendingException();
    }
    instrumentation::Instrumentation* instrumentation = Runtime::Current()->GetInstrumentation();
    ArtMethod *method = shadow_frame.GetMethod();

    if (UNLIKELY(instrumentation->HasMethodEntryListeners())) {
      instrumentation->MethodEnterEvent(self,
                                        shadow_frame.GetThisObject(accessor.InsSize()),
                                        method,
                                        0);
      if (UNLIKELY(shadow_frame.GetForcePopFrame())) {
        // The caller will retry this invoke. Just return immediately without any value.
        DCHECK(Runtime::Current()->AreNonStandardExitsEnabled());
        DCHECK(PrevFrameWillRetry(self, shadow_frame));
        return JValue();
      }
      if (UNLIKELY(self->IsExceptionPending())) {
        instrumentation->MethodUnwindEvent(self,
                                           shadow_frame.GetThisObject(accessor.InsSize()),
                                           method,
                                           0);
        return JValue();
      }
    }

    if (!stay_in_interpreter && !self->IsForceInterpreter()) {
      jit::Jit* jit = Runtime::Current()->GetJit();
      if (jit != nullptr) {
        jit->MethodEntered(self, shadow_frame.GetMethod());
        if (jit->CanInvokeCompiledCode(method)) {
          JValue result;

          // Pop the shadow frame before calling into compiled code.
          self->PopShadowFrame();
          // Calculate the offset of the first input reg. The input registers are in the high regs.
          // It's ok to access the code item here since JIT code will have been touched by the
          // interpreter and compiler already.
          uint16_t arg_offset = accessor.RegistersSize() - accessor.InsSize();
          ArtInterpreterToCompiledCodeBridge(self, nullptr, &shadow_frame, arg_offset, &result);
          // Push the shadow frame back as the caller will expect it.
          self->PushShadowFrame(&shadow_frame);

          return result;
        }
      }
    }
  }

  ArtMethod* method = shadow_frame.GetMethod();

  DCheckStaticState(self, method);

  // Lock counting is a special version of accessibility checks, and for simplicity and
  // reduction of template parameters, we gate it behind access-checks mode.
  DCHECK(!method->SkipAccessChecks() || !method->MustCountLocks());

  bool transaction_active = Runtime::Current()->IsActiveTransaction();
  if (LIKELY(method->SkipAccessChecks())) {
    // Enter the "without access check" interpreter.
    if (kInterpreterImplKind == kMterpImplKind) {
      if (transaction_active) {
        // No Mterp variant - just use the switch interpreter.
        return ExecuteSwitchImpl<false, true>(self, accessor, shadow_frame, result_register,
                                              false);
      } else if (UNLIKELY(!Runtime::Current()->IsStarted())) {
        return ExecuteSwitchImpl<false, false>(self, accessor, shadow_frame, result_register,
                                               false);
      } else {
        while (true) {
          // Mterp does not support all instrumentation/debugging.
          if (!self->UseMterp()) {
            return ExecuteSwitchImpl<false, false>(self, accessor, shadow_frame, result_register,
                                                   false);
          }
          bool returned = ExecuteMterpImpl(self,
                                           accessor.Insns(),
                                           &shadow_frame,
                                           &result_register);
          if (returned) {
            return result_register;
          } else {
            // Mterp didn't like that instruction.  Single-step it with the reference interpreter.
            result_register = ExecuteSwitchImpl<false, false>(self, accessor, shadow_frame,
                                                              result_register, true);
            if (shadow_frame.GetDexPC() == dex::kDexNoIndex) {
              // Single-stepped a return or an exception not handled locally.  Return to caller.
              return result_register;
            }
          }
        }
      }
    } else {
      DCHECK_EQ(kInterpreterImplKind, kSwitchImplKind);
      if (transaction_active) {
        return ExecuteSwitchImpl<false, true>(self, accessor, shadow_frame, result_register,
                                              false);
      } else {
        return ExecuteSwitchImpl<false, false>(self, accessor, shadow_frame, result_register,
                                               false);
      }
    }
  } else {
    // Enter the "with access check" interpreter.

    // The boot classpath should really not have to run access checks.
    DCHECK(method->GetDeclaringClass()->GetClassLoader() != nullptr
           || Runtime::Current()->IsVerificationSoftFail()
           || Runtime::Current()->IsAotCompiler())
        << method->PrettyMethod();

    if (kInterpreterImplKind == kMterpImplKind) {
      // No access check variants for Mterp.  Just use the switch version.
      if (transaction_active) {
        return ExecuteSwitchImpl<true, true>(self, accessor, shadow_frame, result_register,
                                             false);
      } else {
        return ExecuteSwitchImpl<true, false>(self, accessor, shadow_frame, result_register,
                                              false);
      }
    } else {
      DCHECK_EQ(kInterpreterImplKind, kSwitchImplKind);
      if (transaction_active) {
        return ExecuteSwitchImpl<true, true>(self, accessor, shadow_frame, result_register,
                                             false);
      } else {
        return ExecuteSwitchImpl<true, false>(self, accessor, shadow_frame, result_register,
                                              false);
      }
    }
  }
}

void EnterInterpreterFromInvoke(Thread* self,
                                ArtMethod* method,
                                ObjPtr<mirror::Object> receiver,
                                uint32_t* args,
                                JValue* result,
                                bool stay_in_interpreter) {
  DCHECK_EQ(self, Thread::Current());
  bool implicit_check = !Runtime::Current()->ExplicitStackOverflowChecks();
  if (UNLIKELY(__builtin_frame_address(0) < self->GetStackEndForInterpreter(implicit_check))) {
    ThrowStackOverflowError(self);
    return;
  }

  // This can happen if we are in forced interpreter mode and an obsolete method is called using
  // reflection.
  if (UNLIKELY(method->IsObsolete())) {
    ThrowInternalError("Attempting to invoke obsolete version of '%s'.",
                       method->PrettyMethod().c_str());
    return;
  }

  const char* old_cause = self->StartAssertNoThreadSuspension("EnterInterpreterFromInvoke");
  CodeItemDataAccessor accessor(method->DexInstructionData());
  uint16_t num_regs;
  uint16_t num_ins;
  if (accessor.HasCodeItem()) {
    num_regs =  accessor.RegistersSize();
    num_ins = accessor.InsSize();
  } else if (!method->IsInvokable()) {
    self->EndAssertNoThreadSuspension(old_cause);
    method->ThrowInvocationTimeError();
    return;
  } else {
    DCHECK(method->IsNative());
    num_regs = num_ins = ArtMethod::NumArgRegisters(method->GetShorty());
    if (!method->IsStatic()) {
      num_regs++;
      num_ins++;
    }
  }
  // Set up shadow frame with matching number of reference slots to vregs.
  ShadowFrame* last_shadow_frame = self->GetManagedStack()->GetTopShadowFrame();
  ShadowFrameAllocaUniquePtr shadow_frame_unique_ptr =
      CREATE_SHADOW_FRAME(num_regs, last_shadow_frame, method, /* dex pc */ 0);
  ShadowFrame* shadow_frame = shadow_frame_unique_ptr.get();
  self->PushShadowFrame(shadow_frame);

  size_t cur_reg = num_regs - num_ins;
  if (!method->IsStatic()) {
    CHECK(receiver != nullptr);
    shadow_frame->SetVRegReference(cur_reg, receiver);
    ++cur_reg;
  }
  uint32_t shorty_len = 0;
  const char* shorty = method->GetShorty(&shorty_len);
  for (size_t shorty_pos = 0, arg_pos = 0; cur_reg < num_regs; ++shorty_pos, ++arg_pos, cur_reg++) {
    DCHECK_LT(shorty_pos + 1, shorty_len);
    switch (shorty[shorty_pos + 1]) {
      case 'L': {
        ObjPtr<mirror::Object> o =
            reinterpret_cast<StackReference<mirror::Object>*>(&args[arg_pos])->AsMirrorPtr();
        shadow_frame->SetVRegReference(cur_reg, o);
        break;
      }
      case 'J': case 'D': {
        uint64_t wide_value = (static_cast<uint64_t>(args[arg_pos + 1]) << 32) | args[arg_pos];
        shadow_frame->SetVRegLong(cur_reg, wide_value);
        cur_reg++;
        arg_pos++;
        break;
      }
      default:
        shadow_frame->SetVReg(cur_reg, args[arg_pos]);
        break;
    }
  }
  self->EndAssertNoThreadSuspension(old_cause);
  // Do this after populating the shadow frame in case EnsureInitialized causes a GC.
  if (method->IsStatic() && UNLIKELY(!method->GetDeclaringClass()->IsInitialized())) {
    ClassLinker* class_linker = Runtime::Current()->GetClassLinker();
    StackHandleScope<1> hs(self);
    Handle<mirror::Class> h_class(hs.NewHandle(method->GetDeclaringClass()));
    if (UNLIKELY(!class_linker->EnsureInitialized(self, h_class, true, true))) {
      CHECK(self->IsExceptionPending());
      self->PopShadowFrame();
      return;
    }
  }
  if (LIKELY(!method->IsNative())) {
    JValue r = Execute(self, accessor, *shadow_frame, JValue(), stay_in_interpreter);
    if (result != nullptr) {
      *result = r;
    }
  } else {
    // We don't expect to be asked to interpret native code (which is entered via a JNI compiler
    // generated stub) except during testing and image writing.
    // Update args to be the args in the shadow frame since the input ones could hold stale
    // references pointers due to moving GC.
    args = shadow_frame->GetVRegArgs(method->IsStatic() ? 0 : 1);
    if (!Runtime::Current()->IsStarted()) {
      UnstartedRuntime::Jni(self, method, receiver.Ptr(), args, result);
    } else {
      InterpreterJni(self, method, shorty, receiver, args, result);
    }
  }
  self->PopShadowFrame();
}

static int16_t GetReceiverRegisterForStringInit(const Instruction* instr) {
  DCHECK(instr->Opcode() == Instruction::INVOKE_DIRECT_RANGE ||
         instr->Opcode() == Instruction::INVOKE_DIRECT);
  return (instr->Opcode() == Instruction::INVOKE_DIRECT_RANGE) ?
      instr->VRegC_3rc() : instr->VRegC_35c();
}

void EnterInterpreterFromDeoptimize(Thread* self,
                                    ShadowFrame* shadow_frame,
                                    JValue* ret_val,
                                    bool from_code,
                                    DeoptimizationMethodType deopt_method_type)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  JValue value;
  // Set value to last known result in case the shadow frame chain is empty.
  value.SetJ(ret_val->GetJ());
  // How many frames we have executed.
  size_t frame_cnt = 0;
  while (shadow_frame != nullptr) {
    // We do not want to recover lock state for lock counting when deoptimizing. Currently,
    // the compiler should not have compiled a method that failed structured-locking checks.
    DCHECK(!shadow_frame->GetMethod()->MustCountLocks());

    self->SetTopOfShadowStack(shadow_frame);
    CodeItemDataAccessor accessor(shadow_frame->GetMethod()->DexInstructionData());
    const uint32_t dex_pc = shadow_frame->GetDexPC();
    uint32_t new_dex_pc = dex_pc;
    if (UNLIKELY(self->IsExceptionPending())) {
      // If we deoptimize from the QuickExceptionHandler, we already reported the exception to
      // the instrumentation. To prevent from reporting it a second time, we simply pass a
      // null Instrumentation*.
      const instrumentation::Instrumentation* const instrumentation =
          frame_cnt == 0 ? nullptr : Runtime::Current()->GetInstrumentation();
      new_dex_pc = MoveToExceptionHandler(
          self, *shadow_frame, instrumentation) ? shadow_frame->GetDexPC() : dex::kDexNoIndex;
    } else if (!from_code) {
      // Deoptimization is not called from code directly.
      const Instruction* instr = &accessor.InstructionAt(dex_pc);
      if (deopt_method_type == DeoptimizationMethodType::kKeepDexPc ||
          shadow_frame->GetForceRetryInstruction()) {
        DCHECK(frame_cnt == 0 || (frame_cnt == 1 && shadow_frame->GetForceRetryInstruction()))
            << "frame_cnt: " << frame_cnt
            << " force-retry: " << shadow_frame->GetForceRetryInstruction();
        // Need to re-execute the dex instruction.
        // (1) An invocation might be split into class initialization and invoke.
        //     In this case, the invoke should not be skipped.
        // (2) A suspend check should also execute the dex instruction at the
        //     corresponding dex pc.
        // If the ForceRetryInstruction bit is set this must be the second frame (the first being
        // the one that is being popped).
        DCHECK_EQ(new_dex_pc, dex_pc);
        shadow_frame->SetForceRetryInstruction(false);
      } else if (instr->Opcode() == Instruction::MONITOR_ENTER ||
                 instr->Opcode() == Instruction::MONITOR_EXIT) {
        DCHECK(deopt_method_type == DeoptimizationMethodType::kDefault);
        DCHECK_EQ(frame_cnt, 0u);
        // Non-idempotent dex instruction should not be re-executed.
        // On the other hand, if a MONITOR_ENTER is at the dex_pc of a suspend
        // check, that MONITOR_ENTER should be executed. That case is handled
        // above.
        new_dex_pc = dex_pc + instr->SizeInCodeUnits();
      } else if (instr->IsInvoke()) {
        DCHECK(deopt_method_type == DeoptimizationMethodType::kDefault);
        if (IsStringInit(instr, shadow_frame->GetMethod())) {
          uint16_t this_obj_vreg = GetReceiverRegisterForStringInit(instr);
          // Move the StringFactory.newStringFromChars() result into the register representing
          // "this object" when invoking the string constructor in the original dex instruction.
          // Also move the result into all aliases.
          DCHECK(value.GetL()->IsString());
          SetStringInitValueToAllAliases(shadow_frame, this_obj_vreg, value);
          // Calling string constructor in the original dex code doesn't generate a result value.
          value.SetJ(0);
        }
        new_dex_pc = dex_pc + instr->SizeInCodeUnits();
      } else if (instr->Opcode() == Instruction::NEW_INSTANCE) {
        // A NEW_INSTANCE is simply re-executed, including
        // "new-instance String" which is compiled into a call into
        // StringFactory.newEmptyString().
        DCHECK_EQ(new_dex_pc, dex_pc);
      } else {
        DCHECK(deopt_method_type == DeoptimizationMethodType::kDefault);
        DCHECK_EQ(frame_cnt, 0u);
        // By default, we re-execute the dex instruction since if they are not
        // an invoke, so that we don't have to decode the dex instruction to move
        // result into the right vreg. All slow paths have been audited to be
        // idempotent except monitor-enter/exit and invocation stubs.
        // TODO: move result and advance dex pc. That also requires that we
        // can tell the return type of a runtime method, possibly by decoding
        // the dex instruction at the caller.
        DCHECK_EQ(new_dex_pc, dex_pc);
      }
    } else {
      // Nothing to do, the dex_pc is the one at which the code requested
      // the deoptimization.
      DCHECK_EQ(frame_cnt, 0u);
      DCHECK_EQ(new_dex_pc, dex_pc);
    }
    if (new_dex_pc != dex::kDexNoIndex) {
      shadow_frame->SetDexPC(new_dex_pc);
      value = Execute(self,
                      accessor,
                      *shadow_frame,
                      value,
                      /* stay_in_interpreter= */ true,
                      /* from_deoptimize= */ true);
    }
    ShadowFrame* old_frame = shadow_frame;
    shadow_frame = shadow_frame->GetLink();
    ShadowFrame::DeleteDeoptimizedFrame(old_frame);
    // Following deoptimizations of shadow frames must be at invocation point
    // and should advance dex pc past the invoke instruction.
    from_code = false;
    deopt_method_type = DeoptimizationMethodType::kDefault;
    frame_cnt++;
  }
  ret_val->SetJ(value.GetJ());
}

JValue EnterInterpreterFromEntryPoint(Thread* self, const CodeItemDataAccessor& accessor,
                                      ShadowFrame* shadow_frame) {
  DCHECK_EQ(self, Thread::Current());
  bool implicit_check = !Runtime::Current()->ExplicitStackOverflowChecks();
  if (UNLIKELY(__builtin_frame_address(0) < self->GetStackEndForInterpreter(implicit_check))) {
    ThrowStackOverflowError(self);
    return JValue();
  }

  jit::Jit* jit = Runtime::Current()->GetJit();
  if (jit != nullptr) {
    jit->NotifyCompiledCodeToInterpreterTransition(self, shadow_frame->GetMethod());
  }
  return Execute(self, accessor, *shadow_frame, JValue());
}

void ArtInterpreterToInterpreterBridge(Thread* self,
                                       const CodeItemDataAccessor& accessor,
                                       ShadowFrame* shadow_frame,
                                       JValue* result) {
  bool implicit_check = !Runtime::Current()->ExplicitStackOverflowChecks();
  if (UNLIKELY(__builtin_frame_address(0) < self->GetStackEndForInterpreter(implicit_check))) {
    ThrowStackOverflowError(self);
    return;
  }

  self->PushShadowFrame(shadow_frame);
  ArtMethod* method = shadow_frame->GetMethod();
  // Ensure static methods are initialized.
  const bool is_static = method->IsStatic();
  if (is_static) {
    ObjPtr<mirror::Class> declaring_class = method->GetDeclaringClass();
    if (UNLIKELY(!declaring_class->IsInitialized())) {
      StackHandleScope<1> hs(self);
      HandleWrapperObjPtr<mirror::Class> h_declaring_class(hs.NewHandleWrapper(&declaring_class));
      if (UNLIKELY(!Runtime::Current()->GetClassLinker()->EnsureInitialized(
          self, h_declaring_class, true, true))) {
        DCHECK(self->IsExceptionPending());
        self->PopShadowFrame();
        return;
      }
      CHECK(h_declaring_class->IsInitializing());
    }
  }

  if (LIKELY(!shadow_frame->GetMethod()->IsNative())) {
    result->SetJ(Execute(self, accessor, *shadow_frame, JValue()).GetJ());
  } else {
    // We don't expect to be asked to interpret native code (which is entered via a JNI compiler
    // generated stub) except during testing and image writing.
    CHECK(!Runtime::Current()->IsStarted());
    ObjPtr<mirror::Object> receiver = is_static ? nullptr : shadow_frame->GetVRegReference(0);
    uint32_t* args = shadow_frame->GetVRegArgs(is_static ? 0 : 1);
    UnstartedRuntime::Jni(self, shadow_frame->GetMethod(), receiver.Ptr(), args, result);
  }

  self->PopShadowFrame();
}

void CheckInterpreterAsmConstants() {
  CheckMterpAsmConstants();
}

void InitInterpreterTls(Thread* self) {
  InitMterpTls(self);
}

bool PrevFrameWillRetry(Thread* self, const ShadowFrame& frame) {
  ShadowFrame* prev_frame = frame.GetLink();
  if (prev_frame == nullptr) {
    NthCallerVisitor vis(self, 1, false);
    vis.WalkStack();
    prev_frame = vis.GetCurrentShadowFrame();
    if (prev_frame == nullptr) {
      prev_frame = self->FindDebuggerShadowFrame(vis.GetFrameId());
    }
  }
  return prev_frame != nullptr && prev_frame->GetForceRetryInstruction();
}

}  // namespace interpreter
}  // namespace art
