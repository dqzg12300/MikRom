/*
 * Copyright (C) 2011 The Android Open Source Project
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

#include "reflection-inl.h"

#include "art_field-inl.h"
#include "art_method-inl.h"
#include "base/enums.h"
#include "class_linker.h"
#include "common_throws.h"
#include "dex/dex_file-inl.h"
#include "indirect_reference_table-inl.h"
#include "jni/java_vm_ext.h"
#include "jni/jni_internal.h"
#include "jvalue-inl.h"
#include "mirror/class-inl.h"
#include "mirror/executable.h"
#include "mirror/object_array-inl.h"
#include "nativehelper/scoped_local_ref.h"
#include "nth_caller_visitor.h"
#include "scoped_thread_state_change-inl.h"
#include "stack_reference.h"
#include "thread-inl.h"
#include "well_known_classes.h"

namespace art {
namespace {

using android::base::StringPrintf;

class ArgArray {
 public:
  ArgArray(const char* shorty, uint32_t shorty_len)
      : shorty_(shorty), shorty_len_(shorty_len), num_bytes_(0) {
    size_t num_slots = shorty_len + 1;  // +1 in case of receiver.
    if (LIKELY((num_slots * 2) < kSmallArgArraySize)) {
      // We can trivially use the small arg array.
      arg_array_ = small_arg_array_;
    } else {
      // Analyze shorty to see if we need the large arg array.
      for (size_t i = 1; i < shorty_len; ++i) {
        char c = shorty[i];
        if (c == 'J' || c == 'D') {
          num_slots++;
        }
      }
      if (num_slots <= kSmallArgArraySize) {
        arg_array_ = small_arg_array_;
      } else {
        large_arg_array_.reset(new uint32_t[num_slots]);
        arg_array_ = large_arg_array_.get();
      }
    }
  }

  uint32_t* GetArray() {
    return arg_array_;
  }

  uint32_t GetNumBytes() {
    return num_bytes_;
  }

  void Append(uint32_t value) {
    arg_array_[num_bytes_ / 4] = value;
    num_bytes_ += 4;
  }

  void Append(ObjPtr<mirror::Object> obj) REQUIRES_SHARED(Locks::mutator_lock_) {
    Append(StackReference<mirror::Object>::FromMirrorPtr(obj.Ptr()).AsVRegValue());
  }

  void AppendWide(uint64_t value) {
    arg_array_[num_bytes_ / 4] = value;
    arg_array_[(num_bytes_ / 4) + 1] = value >> 32;
    num_bytes_ += 8;
  }

  void AppendFloat(float value) {
    jvalue jv;
    jv.f = value;
    Append(jv.i);
  }

  void AppendDouble(double value) {
    jvalue jv;
    jv.d = value;
    AppendWide(jv.j);
  }

  void BuildArgArrayFromVarArgs(const ScopedObjectAccessAlreadyRunnable& soa,
                                ObjPtr<mirror::Object> receiver,
                                va_list ap)
      REQUIRES_SHARED(Locks::mutator_lock_) {
    // Set receiver if non-null (method is not static)
    if (receiver != nullptr) {
      Append(receiver);
    }
    for (size_t i = 1; i < shorty_len_; ++i) {
      switch (shorty_[i]) {
        case 'Z':
        case 'B':
        case 'C':
        case 'S':
        case 'I':
          Append(va_arg(ap, jint));
          break;
        case 'F':
          AppendFloat(va_arg(ap, jdouble));
          break;
        case 'L':
          Append(soa.Decode<mirror::Object>(va_arg(ap, jobject)));
          break;
        case 'D':
          AppendDouble(va_arg(ap, jdouble));
          break;
        case 'J':
          AppendWide(va_arg(ap, jlong));
          break;
#ifndef NDEBUG
        default:
          LOG(FATAL) << "Unexpected shorty character: " << shorty_[i];
#endif
      }
    }
  }

  void BuildArgArrayFromJValues(const ScopedObjectAccessAlreadyRunnable& soa,
                                ObjPtr<mirror::Object> receiver, const jvalue* args)
      REQUIRES_SHARED(Locks::mutator_lock_) {
    // Set receiver if non-null (method is not static)
    if (receiver != nullptr) {
      Append(receiver);
    }
    for (size_t i = 1, args_offset = 0; i < shorty_len_; ++i, ++args_offset) {
      switch (shorty_[i]) {
        case 'Z':
          Append(args[args_offset].z);
          break;
        case 'B':
          Append(args[args_offset].b);
          break;
        case 'C':
          Append(args[args_offset].c);
          break;
        case 'S':
          Append(args[args_offset].s);
          break;
        case 'I':
          FALLTHROUGH_INTENDED;
        case 'F':
          Append(args[args_offset].i);
          break;
        case 'L':
          Append(soa.Decode<mirror::Object>(args[args_offset].l));
          break;
        case 'D':
          FALLTHROUGH_INTENDED;
        case 'J':
          AppendWide(args[args_offset].j);
          break;
#ifndef NDEBUG
        default:
          LOG(FATAL) << "Unexpected shorty character: " << shorty_[i];
#endif
      }
    }
  }

  void BuildArgArrayFromFrame(ShadowFrame* shadow_frame, uint32_t arg_offset)
      REQUIRES_SHARED(Locks::mutator_lock_) {
    // Set receiver if non-null (method is not static)
    size_t cur_arg = arg_offset;
    if (!shadow_frame->GetMethod()->IsStatic()) {
      Append(shadow_frame->GetVReg(cur_arg));
      cur_arg++;
    }
    for (size_t i = 1; i < shorty_len_; ++i) {
      switch (shorty_[i]) {
        case 'Z':
        case 'B':
        case 'C':
        case 'S':
        case 'I':
        case 'F':
        case 'L':
          Append(shadow_frame->GetVReg(cur_arg));
          cur_arg++;
          break;
        case 'D':
        case 'J':
          AppendWide(shadow_frame->GetVRegLong(cur_arg));
          cur_arg++;
          cur_arg++;
          break;
#ifndef NDEBUG
        default:
          LOG(FATAL) << "Unexpected shorty character: " << shorty_[i];
#endif
      }
    }
  }

  static void ThrowIllegalPrimitiveArgumentException(const char* expected,
                                                     const char* found_descriptor)
      REQUIRES_SHARED(Locks::mutator_lock_) {
    ThrowIllegalArgumentException(
        StringPrintf("Invalid primitive conversion from %s to %s", expected,
                     PrettyDescriptor(found_descriptor).c_str()).c_str());
  }

  bool BuildArgArrayFromObjectArray(ObjPtr<mirror::Object> receiver,
                                    ObjPtr<mirror::ObjectArray<mirror::Object>> raw_args,
                                    ArtMethod* m,
                                    Thread* self)
      REQUIRES_SHARED(Locks::mutator_lock_) {
    const dex::TypeList* classes = m->GetParameterTypeList();
    // Set receiver if non-null (method is not static)
    if (receiver != nullptr) {
      Append(receiver);
    }
    StackHandleScope<2> hs(self);
    MutableHandle<mirror::Object> arg(hs.NewHandle<mirror::Object>(nullptr));
    Handle<mirror::ObjectArray<mirror::Object>> args(
        hs.NewHandle<mirror::ObjectArray<mirror::Object>>(raw_args));
    for (size_t i = 1, args_offset = 0; i < shorty_len_; ++i, ++args_offset) {
      arg.Assign(args->Get(args_offset));
      if (((shorty_[i] == 'L') && (arg != nullptr)) ||
          ((arg == nullptr && shorty_[i] != 'L'))) {
        // TODO: The method's parameter's type must have been previously resolved, yet
        // we've seen cases where it's not b/34440020.
        ObjPtr<mirror::Class> dst_class(
            m->ResolveClassFromTypeIndex(classes->GetTypeItem(args_offset).type_idx_));
        if (dst_class == nullptr) {
          CHECK(self->IsExceptionPending());
          return false;
        }
        if (UNLIKELY(arg == nullptr || !arg->InstanceOf(dst_class))) {
          ThrowIllegalArgumentException(
              StringPrintf("method %s argument %zd has type %s, got %s",
                  m->PrettyMethod(false).c_str(),
                  args_offset + 1,  // Humans don't count from 0.
                  mirror::Class::PrettyDescriptor(dst_class).c_str(),
                  mirror::Object::PrettyTypeOf(arg.Get()).c_str()).c_str());
          return false;
        }
      }

#define DO_FIRST_ARG(match_descriptor, get_fn, append) { \
          if (LIKELY(arg != nullptr && \
              arg->GetClass()->DescriptorEquals(match_descriptor))) { \
            ArtField* primitive_field = arg->GetClass()->GetInstanceField(0); \
            append(primitive_field-> get_fn(arg.Get()));

#define DO_ARG(match_descriptor, get_fn, append) \
          } else if (LIKELY(arg != nullptr && \
                            arg->GetClass<>()->DescriptorEquals(match_descriptor))) { \
            ArtField* primitive_field = arg->GetClass()->GetInstanceField(0); \
            append(primitive_field-> get_fn(arg.Get()));

#define DO_FAIL(expected) \
          } else { \
            if (arg->GetClass<>()->IsPrimitive()) { \
              std::string temp; \
              ThrowIllegalPrimitiveArgumentException(expected, \
                                                     arg->GetClass<>()->GetDescriptor(&temp)); \
            } else { \
              ThrowIllegalArgumentException(\
                  StringPrintf("method %s argument %zd has type %s, got %s", \
                      ArtMethod::PrettyMethod(m, false).c_str(), \
                      args_offset + 1, \
                      expected, \
                      mirror::Object::PrettyTypeOf(arg.Get()).c_str()).c_str()); \
            } \
            return false; \
          } }

      switch (shorty_[i]) {
        case 'L':
          Append(arg.Get());
          break;
        case 'Z':
          DO_FIRST_ARG("Ljava/lang/Boolean;", GetBoolean, Append)
          DO_FAIL("boolean")
          break;
        case 'B':
          DO_FIRST_ARG("Ljava/lang/Byte;", GetByte, Append)
          DO_FAIL("byte")
          break;
        case 'C':
          DO_FIRST_ARG("Ljava/lang/Character;", GetChar, Append)
          DO_FAIL("char")
          break;
        case 'S':
          DO_FIRST_ARG("Ljava/lang/Short;", GetShort, Append)
          DO_ARG("Ljava/lang/Byte;", GetByte, Append)
          DO_FAIL("short")
          break;
        case 'I':
          DO_FIRST_ARG("Ljava/lang/Integer;", GetInt, Append)
          DO_ARG("Ljava/lang/Character;", GetChar, Append)
          DO_ARG("Ljava/lang/Short;", GetShort, Append)
          DO_ARG("Ljava/lang/Byte;", GetByte, Append)
          DO_FAIL("int")
          break;
        case 'J':
          DO_FIRST_ARG("Ljava/lang/Long;", GetLong, AppendWide)
          DO_ARG("Ljava/lang/Integer;", GetInt, AppendWide)
          DO_ARG("Ljava/lang/Character;", GetChar, AppendWide)
          DO_ARG("Ljava/lang/Short;", GetShort, AppendWide)
          DO_ARG("Ljava/lang/Byte;", GetByte, AppendWide)
          DO_FAIL("long")
          break;
        case 'F':
          DO_FIRST_ARG("Ljava/lang/Float;", GetFloat, AppendFloat)
          DO_ARG("Ljava/lang/Long;", GetLong, AppendFloat)
          DO_ARG("Ljava/lang/Integer;", GetInt, AppendFloat)
          DO_ARG("Ljava/lang/Character;", GetChar, AppendFloat)
          DO_ARG("Ljava/lang/Short;", GetShort, AppendFloat)
          DO_ARG("Ljava/lang/Byte;", GetByte, AppendFloat)
          DO_FAIL("float")
          break;
        case 'D':
          DO_FIRST_ARG("Ljava/lang/Double;", GetDouble, AppendDouble)
          DO_ARG("Ljava/lang/Float;", GetFloat, AppendDouble)
          DO_ARG("Ljava/lang/Long;", GetLong, AppendDouble)
          DO_ARG("Ljava/lang/Integer;", GetInt, AppendDouble)
          DO_ARG("Ljava/lang/Character;", GetChar, AppendDouble)
          DO_ARG("Ljava/lang/Short;", GetShort, AppendDouble)
          DO_ARG("Ljava/lang/Byte;", GetByte, AppendDouble)
          DO_FAIL("double")
          break;
#ifndef NDEBUG
        default:
          LOG(FATAL) << "Unexpected shorty character: " << shorty_[i];
          UNREACHABLE();
#endif
      }
#undef DO_FIRST_ARG
#undef DO_ARG
#undef DO_FAIL
    }
    return true;
  }

 private:
  enum { kSmallArgArraySize = 16 };
  const char* const shorty_;
  const uint32_t shorty_len_;
  uint32_t num_bytes_;
  uint32_t* arg_array_;
  uint32_t small_arg_array_[kSmallArgArraySize];
  std::unique_ptr<uint32_t[]> large_arg_array_;
};

void CheckMethodArguments(JavaVMExt* vm, ArtMethod* m, uint32_t* args)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  const dex::TypeList* params = m->GetParameterTypeList();
  if (params == nullptr) {
    return;  // No arguments so nothing to check.
  }
  uint32_t offset = 0;
  uint32_t num_params = params->Size();
  size_t error_count = 0;
  if (!m->IsStatic()) {
    offset = 1;
  }
  // TODO: If args contain object references, it may cause problems.
  Thread* const self = Thread::Current();
  for (uint32_t i = 0; i < num_params; i++) {
    dex::TypeIndex type_idx = params->GetTypeItem(i).type_idx_;
    ObjPtr<mirror::Class> param_type(m->ResolveClassFromTypeIndex(type_idx));
    if (param_type == nullptr) {
      CHECK(self->IsExceptionPending());
      LOG(ERROR) << "Internal error: unresolvable type for argument type in JNI invoke: "
          << m->GetTypeDescriptorFromTypeIdx(type_idx) << "\n"
          << self->GetException()->Dump();
      self->ClearException();
      ++error_count;
    } else if (!param_type->IsPrimitive()) {
      // TODO: There is a compaction bug here since GetClassFromTypeIdx can cause thread suspension,
      // this is a hard to fix problem since the args can contain Object*, we need to save and
      // restore them by using a visitor similar to the ones used in the trampoline entrypoints.
      ObjPtr<mirror::Object> argument =
          (reinterpret_cast<StackReference<mirror::Object>*>(&args[i + offset]))->AsMirrorPtr();
      if (argument != nullptr && !argument->InstanceOf(param_type)) {
        LOG(ERROR) << "JNI ERROR (app bug): attempt to pass an instance of "
                   << argument->PrettyTypeOf() << " as argument " << (i + 1)
                   << " to " << m->PrettyMethod();
        ++error_count;
      }
    } else if (param_type->IsPrimitiveLong() || param_type->IsPrimitiveDouble()) {
      offset++;
    } else {
      int32_t arg = static_cast<int32_t>(args[i + offset]);
      if (param_type->IsPrimitiveBoolean()) {
        if (arg != JNI_TRUE && arg != JNI_FALSE) {
          LOG(ERROR) << "JNI ERROR (app bug): expected jboolean (0/1) but got value of "
              << arg << " as argument " << (i + 1) << " to " << m->PrettyMethod();
          ++error_count;
        }
      } else if (param_type->IsPrimitiveByte()) {
        if (arg < -128 || arg > 127) {
          LOG(ERROR) << "JNI ERROR (app bug): expected jbyte but got value of "
              << arg << " as argument " << (i + 1) << " to " << m->PrettyMethod();
          ++error_count;
        }
      } else if (param_type->IsPrimitiveChar()) {
        if (args[i + offset] > 0xFFFF) {
          LOG(ERROR) << "JNI ERROR (app bug): expected jchar but got value of "
              << arg << " as argument " << (i + 1) << " to " << m->PrettyMethod();
          ++error_count;
        }
      } else if (param_type->IsPrimitiveShort()) {
        if (arg < -32768 || arg > 0x7FFF) {
          LOG(ERROR) << "JNI ERROR (app bug): expected jshort but got value of "
              << arg << " as argument " << (i + 1) << " to " << m->PrettyMethod();
          ++error_count;
        }
      }
    }
  }
  if (UNLIKELY(error_count > 0)) {
    // TODO: pass the JNI function name (such as "CallVoidMethodV") through so we can call JniAbort
    // with an argument.
    vm->JniAbortF(nullptr, "bad arguments passed to %s (see above for details)",
                  m->PrettyMethod().c_str());
  }
}

ArtMethod* FindVirtualMethod(ObjPtr<mirror::Object> receiver, ArtMethod* method)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  return receiver->GetClass()->FindVirtualMethodForVirtualOrInterface(method, kRuntimePointerSize);
}


void InvokeWithArgArray(const ScopedObjectAccessAlreadyRunnable& soa,
                               ArtMethod* method, ArgArray* arg_array, JValue* result,
                               const char* shorty)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  uint32_t* args = arg_array->GetArray();
  if (UNLIKELY(soa.Env()->IsCheckJniEnabled())) {
    CheckMethodArguments(soa.Vm(), method->GetInterfaceMethodIfProxy(kRuntimePointerSize), args);
  }
  method->Invoke(soa.Self(), args, arg_array->GetNumBytes(), result, shorty);
}

ALWAYS_INLINE
bool CheckArgsForInvokeMethod(ArtMethod* np_method,
                              ObjPtr<mirror::ObjectArray<mirror::Object>> objects)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  const dex::TypeList* classes = np_method->GetParameterTypeList();
  uint32_t classes_size = (classes == nullptr) ? 0 : classes->Size();
  uint32_t arg_count = (objects == nullptr) ? 0 : objects->GetLength();
  if (UNLIKELY(arg_count != classes_size)) {
    ThrowIllegalArgumentException(StringPrintf("Wrong number of arguments; expected %d, got %d",
                                               classes_size, arg_count).c_str());
    return false;
  }
  return true;
}

ALWAYS_INLINE
bool InvokeMethodImpl(const ScopedObjectAccessAlreadyRunnable& soa,
                      ArtMethod* m,
                      ArtMethod* np_method,
                      ObjPtr<mirror::Object> receiver,
                      ObjPtr<mirror::ObjectArray<mirror::Object>> objects,
                      const char** shorty,
                      JValue* result) REQUIRES_SHARED(Locks::mutator_lock_) {
  // Invoke the method.
  uint32_t shorty_len = 0;
  *shorty = np_method->GetShorty(&shorty_len);
  ArgArray arg_array(*shorty, shorty_len);
  if (!arg_array.BuildArgArrayFromObjectArray(receiver, objects, np_method, soa.Self())) {
    CHECK(soa.Self()->IsExceptionPending());
    return false;
  }

  InvokeWithArgArray(soa, m, &arg_array, result, *shorty);

  // Wrap any exception with "Ljava/lang/reflect/InvocationTargetException;" and return early.
  if (soa.Self()->IsExceptionPending()) {
    // If we get another exception when we are trying to wrap, then just use that instead.
    ScopedLocalRef<jthrowable> th(soa.Env(), soa.Env()->ExceptionOccurred());
    soa.Self()->ClearException();
    jclass exception_class = soa.Env()->FindClass("java/lang/reflect/InvocationTargetException");
    if (exception_class == nullptr) {
      soa.Self()->AssertPendingException();
      return false;
    }
    jmethodID mid = soa.Env()->GetMethodID(exception_class, "<init>", "(Ljava/lang/Throwable;)V");
    CHECK(mid != nullptr);
    jobject exception_instance = soa.Env()->NewObject(exception_class, mid, th.get());
    if (exception_instance == nullptr) {
      soa.Self()->AssertPendingException();
      return false;
    }
    soa.Env()->Throw(reinterpret_cast<jthrowable>(exception_instance));
    return false;
  }

  return true;
}

}  // anonymous namespace

JValue InvokeWithVarArgs(const ScopedObjectAccessAlreadyRunnable& soa, jobject obj, jmethodID mid,
                         va_list args)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  // We want to make sure that the stack is not within a small distance from the
  // protected region in case we are calling into a leaf function whose stack
  // check has been elided.
  if (UNLIKELY(__builtin_frame_address(0) < soa.Self()->GetStackEnd())) {
    ThrowStackOverflowError(soa.Self());
    return JValue();
  }

  ArtMethod* method = jni::DecodeArtMethod(mid);
  bool is_string_init = method->GetDeclaringClass()->IsStringClass() && method->IsConstructor();
  if (is_string_init) {
    // Replace calls to String.<init> with equivalent StringFactory call.
    method = WellKnownClasses::StringInitToStringFactory(method);
  }
  ObjPtr<mirror::Object> receiver = method->IsStatic() ? nullptr : soa.Decode<mirror::Object>(obj);
  uint32_t shorty_len = 0;
  const char* shorty =
      method->GetInterfaceMethodIfProxy(kRuntimePointerSize)->GetShorty(&shorty_len);
  JValue result;
  ArgArray arg_array(shorty, shorty_len);
  arg_array.BuildArgArrayFromVarArgs(soa, receiver, args);
  InvokeWithArgArray(soa, method, &arg_array, &result, shorty);
  if (is_string_init) {
    // For string init, remap original receiver to StringFactory result.
    UpdateReference(soa.Self(), obj, result.GetL());
  }
  return result;
}

JValue InvokeWithJValues(const ScopedObjectAccessAlreadyRunnable& soa, jobject obj, jmethodID mid,
                         const jvalue* args) {
  // We want to make sure that the stack is not within a small distance from the
  // protected region in case we are calling into a leaf function whose stack
  // check has been elided.
  if (UNLIKELY(__builtin_frame_address(0) < soa.Self()->GetStackEnd())) {
    ThrowStackOverflowError(soa.Self());
    return JValue();
  }

  ArtMethod* method = jni::DecodeArtMethod(mid);
  bool is_string_init = method->GetDeclaringClass()->IsStringClass() && method->IsConstructor();
  if (is_string_init) {
    // Replace calls to String.<init> with equivalent StringFactory call.
    method = WellKnownClasses::StringInitToStringFactory(method);
  }
  ObjPtr<mirror::Object> receiver = method->IsStatic() ? nullptr : soa.Decode<mirror::Object>(obj);
  uint32_t shorty_len = 0;
  const char* shorty =
      method->GetInterfaceMethodIfProxy(kRuntimePointerSize)->GetShorty(&shorty_len);
  JValue result;
  ArgArray arg_array(shorty, shorty_len);
  arg_array.BuildArgArrayFromJValues(soa, receiver, args);
  InvokeWithArgArray(soa, method, &arg_array, &result, shorty);
  if (is_string_init) {
    // For string init, remap original receiver to StringFactory result.
    UpdateReference(soa.Self(), obj, result.GetL());
  }
  return result;
}

JValue InvokeVirtualOrInterfaceWithJValues(const ScopedObjectAccessAlreadyRunnable& soa,
                                           jobject obj, jmethodID mid, const jvalue* args) {
  // We want to make sure that the stack is not within a small distance from the
  // protected region in case we are calling into a leaf function whose stack
  // check has been elided.
  if (UNLIKELY(__builtin_frame_address(0) < soa.Self()->GetStackEnd())) {
    ThrowStackOverflowError(soa.Self());
    return JValue();
  }

  ObjPtr<mirror::Object> receiver = soa.Decode<mirror::Object>(obj);
  ArtMethod* method = FindVirtualMethod(receiver, jni::DecodeArtMethod(mid));
  bool is_string_init = method->GetDeclaringClass()->IsStringClass() && method->IsConstructor();
  if (is_string_init) {
    // Replace calls to String.<init> with equivalent StringFactory call.
    method = WellKnownClasses::StringInitToStringFactory(method);
    receiver = nullptr;
  }
  uint32_t shorty_len = 0;
  const char* shorty =
      method->GetInterfaceMethodIfProxy(kRuntimePointerSize)->GetShorty(&shorty_len);
  JValue result;
  ArgArray arg_array(shorty, shorty_len);
  arg_array.BuildArgArrayFromJValues(soa, receiver, args);
  InvokeWithArgArray(soa, method, &arg_array, &result, shorty);
  if (is_string_init) {
    // For string init, remap original receiver to StringFactory result.
    UpdateReference(soa.Self(), obj, result.GetL());
  }
  return result;
}

JValue InvokeVirtualOrInterfaceWithVarArgs(const ScopedObjectAccessAlreadyRunnable& soa,
                                           jobject obj, jmethodID mid, va_list args) {
  // We want to make sure that the stack is not within a small distance from the
  // protected region in case we are calling into a leaf function whose stack
  // check has been elided.
  if (UNLIKELY(__builtin_frame_address(0) < soa.Self()->GetStackEnd())) {
    ThrowStackOverflowError(soa.Self());
    return JValue();
  }

  ObjPtr<mirror::Object> receiver = soa.Decode<mirror::Object>(obj);
  ArtMethod* method = FindVirtualMethod(receiver, jni::DecodeArtMethod(mid));
  bool is_string_init = method->GetDeclaringClass()->IsStringClass() && method->IsConstructor();
  if (is_string_init) {
    // Replace calls to String.<init> with equivalent StringFactory call.
    method = WellKnownClasses::StringInitToStringFactory(method);
    receiver = nullptr;
  }
  uint32_t shorty_len = 0;
  const char* shorty =
      method->GetInterfaceMethodIfProxy(kRuntimePointerSize)->GetShorty(&shorty_len);
  JValue result;
  ArgArray arg_array(shorty, shorty_len);
  arg_array.BuildArgArrayFromVarArgs(soa, receiver, args);
  InvokeWithArgArray(soa, method, &arg_array, &result, shorty);
  if (is_string_init) {
    // For string init, remap original receiver to StringFactory result.
    UpdateReference(soa.Self(), obj, result.GetL());
  }
  return result;
}

jobject InvokeMethod(const ScopedObjectAccessAlreadyRunnable& soa, jobject javaMethod,
                     jobject javaReceiver, jobject javaArgs, size_t num_frames) {
  // We want to make sure that the stack is not within a small distance from the
  // protected region in case we are calling into a leaf function whose stack
  // check has been elided.
  if (UNLIKELY(__builtin_frame_address(0) <
               soa.Self()->GetStackEndForInterpreter(true))) {
    ThrowStackOverflowError(soa.Self());
    return nullptr;
  }

  ObjPtr<mirror::Executable> executable = soa.Decode<mirror::Executable>(javaMethod);
  const bool accessible = executable->IsAccessible();
  ArtMethod* m = executable->GetArtMethod();

  ObjPtr<mirror::Class> declaring_class = m->GetDeclaringClass();
  if (UNLIKELY(!declaring_class->IsInitialized())) {
    StackHandleScope<1> hs(soa.Self());
    HandleWrapperObjPtr<mirror::Class> h_class(hs.NewHandleWrapper(&declaring_class));
    if (!Runtime::Current()->GetClassLinker()->EnsureInitialized(soa.Self(), h_class, true, true)) {
      return nullptr;
    }
  }

  ObjPtr<mirror::Object> receiver;
  if (!m->IsStatic()) {
    // Replace calls to String.<init> with equivalent StringFactory call.
    if (declaring_class->IsStringClass() && m->IsConstructor()) {
      m = WellKnownClasses::StringInitToStringFactory(m);
      CHECK(javaReceiver == nullptr);
    } else {
      // Check that the receiver is non-null and an instance of the field's declaring class.
      receiver = soa.Decode<mirror::Object>(javaReceiver);
      if (!VerifyObjectIsClass(receiver, declaring_class)) {
        return nullptr;
      }

      // Find the actual implementation of the virtual method.
      m = receiver->GetClass()->FindVirtualMethodForVirtualOrInterface(m, kRuntimePointerSize);
    }
  }

  // Get our arrays of arguments and their types, and check they're the same size.
  ObjPtr<mirror::ObjectArray<mirror::Object>> objects =
      soa.Decode<mirror::ObjectArray<mirror::Object>>(javaArgs);
  auto* np_method = m->GetInterfaceMethodIfProxy(kRuntimePointerSize);
  if (!CheckArgsForInvokeMethod(np_method, objects)) {
    return nullptr;
  }

  // If method is not set to be accessible, verify it can be accessed by the caller.
  ObjPtr<mirror::Class> calling_class;
  if (!accessible && !VerifyAccess(soa.Self(),
                                   receiver,
                                   declaring_class,
                                   m->GetAccessFlags(),
                                   &calling_class,
                                   num_frames)) {
    ThrowIllegalAccessException(
        StringPrintf("Class %s cannot access %s method %s of class %s",
            calling_class == nullptr ? "null" : calling_class->PrettyClass().c_str(),
            PrettyJavaAccessFlags(m->GetAccessFlags()).c_str(),
            m->PrettyMethod().c_str(),
            m->GetDeclaringClass() == nullptr ? "null" :
                m->GetDeclaringClass()->PrettyClass().c_str()).c_str());
    return nullptr;
  }

  // Invoke the method.
  JValue result;
  const char* shorty;
  if (!InvokeMethodImpl(soa, m, np_method, receiver, objects, &shorty, &result)) {
    return nullptr;
  }
  return soa.AddLocalReference<jobject>(BoxPrimitive(Primitive::GetType(shorty[0]), result));
}

void InvokeConstructor(const ScopedObjectAccessAlreadyRunnable& soa,
                       ArtMethod* constructor,
                       ObjPtr<mirror::Object> receiver,
                       jobject javaArgs) {
  // We want to make sure that the stack is not within a small distance from the
  // protected region in case we are calling into a leaf function whose stack
  // check has been elided.
  if (UNLIKELY(__builtin_frame_address(0) < soa.Self()->GetStackEndForInterpreter(true))) {
    ThrowStackOverflowError(soa.Self());
    return;
  }

  if (kIsDebugBuild) {
    CHECK(constructor->IsConstructor());

    ObjPtr<mirror::Class> declaring_class = constructor->GetDeclaringClass();
    CHECK(declaring_class->IsInitialized());

    // Calls to String.<init> should have been repplaced with with equivalent StringFactory calls.
    CHECK(!declaring_class->IsStringClass());

    // Check that the receiver is non-null and an instance of the field's declaring class.
    CHECK(receiver != nullptr);
    CHECK(VerifyObjectIsClass(receiver, declaring_class));
    CHECK_EQ(constructor,
             receiver->GetClass()->FindVirtualMethodForVirtualOrInterface(constructor,
                                                                          kRuntimePointerSize));
  }

  // Get our arrays of arguments and their types, and check they're the same size.
  ObjPtr<mirror::ObjectArray<mirror::Object>> objects =
      soa.Decode<mirror::ObjectArray<mirror::Object>>(javaArgs);
  ArtMethod* np_method = constructor->GetInterfaceMethodIfProxy(kRuntimePointerSize);
  if (!CheckArgsForInvokeMethod(np_method, objects)) {
    return;
  }

  // Invoke the constructor.
  JValue result;
  const char* shorty;
  InvokeMethodImpl(soa, constructor, np_method, receiver, objects, &shorty, &result);
}

ObjPtr<mirror::Object> BoxPrimitive(Primitive::Type src_class, const JValue& value) {
  if (src_class == Primitive::kPrimNot) {
    return value.GetL();
  }
  if (src_class == Primitive::kPrimVoid) {
    // There's no such thing as a void field, and void methods invoked via reflection return null.
    return nullptr;
  }

  jmethodID m = nullptr;
  const char* shorty;
  switch (src_class) {
  case Primitive::kPrimBoolean:
    m = WellKnownClasses::java_lang_Boolean_valueOf;
    shorty = "LZ";
    break;
  case Primitive::kPrimByte:
    m = WellKnownClasses::java_lang_Byte_valueOf;
    shorty = "LB";
    break;
  case Primitive::kPrimChar:
    m = WellKnownClasses::java_lang_Character_valueOf;
    shorty = "LC";
    break;
  case Primitive::kPrimDouble:
    m = WellKnownClasses::java_lang_Double_valueOf;
    shorty = "LD";
    break;
  case Primitive::kPrimFloat:
    m = WellKnownClasses::java_lang_Float_valueOf;
    shorty = "LF";
    break;
  case Primitive::kPrimInt:
    m = WellKnownClasses::java_lang_Integer_valueOf;
    shorty = "LI";
    break;
  case Primitive::kPrimLong:
    m = WellKnownClasses::java_lang_Long_valueOf;
    shorty = "LJ";
    break;
  case Primitive::kPrimShort:
    m = WellKnownClasses::java_lang_Short_valueOf;
    shorty = "LS";
    break;
  default:
    LOG(FATAL) << static_cast<int>(src_class);
    shorty = nullptr;
  }

  ScopedObjectAccessUnchecked soa(Thread::Current());
  DCHECK_EQ(soa.Self()->GetState(), kRunnable);

  ArgArray arg_array(shorty, 2);
  JValue result;
  if (src_class == Primitive::kPrimDouble || src_class == Primitive::kPrimLong) {
    arg_array.AppendWide(value.GetJ());
  } else {
    arg_array.Append(value.GetI());
  }

  jni::DecodeArtMethod(m)->Invoke(soa.Self(),
                                  arg_array.GetArray(),
                                  arg_array.GetNumBytes(),
                                  &result,
                                  shorty);
  return result.GetL();
}

static std::string UnboxingFailureKind(ArtField* f)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  if (f != nullptr) {
    return "field " + f->PrettyField(false);
  }
  return "result";
}

static bool UnboxPrimitive(ObjPtr<mirror::Object> o,
                           ObjPtr<mirror::Class> dst_class,
                           ArtField* f,
                           JValue* unboxed_value)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  bool unbox_for_result = (f == nullptr);
  if (!dst_class->IsPrimitive()) {
    if (UNLIKELY(o != nullptr && !o->InstanceOf(dst_class))) {
      if (!unbox_for_result) {
        ThrowIllegalArgumentException(
            StringPrintf("%s has type %s, got %s",
                         UnboxingFailureKind(f).c_str(),
                         dst_class->PrettyDescriptor().c_str(),
                         o->PrettyTypeOf().c_str()).c_str());
      } else {
        ThrowClassCastException(
            StringPrintf("Couldn't convert result of type %s to %s",
                         o->PrettyTypeOf().c_str(),
                         dst_class->PrettyDescriptor().c_str()).c_str());
      }
      return false;
    }
    unboxed_value->SetL(o);
    return true;
  }
  if (UNLIKELY(dst_class->GetPrimitiveType() == Primitive::kPrimVoid)) {
    ThrowIllegalArgumentException(StringPrintf("Can't unbox %s to void",
                                               UnboxingFailureKind(f).c_str()).c_str());
    return false;
  }
  if (UNLIKELY(o == nullptr)) {
    if (!unbox_for_result) {
      ThrowIllegalArgumentException(
          StringPrintf("%s has type %s, got null",
                       UnboxingFailureKind(f).c_str(),
                       dst_class->PrettyDescriptor().c_str()).c_str());
    } else {
      ThrowNullPointerException(
          StringPrintf("Expected to unbox a '%s' primitive type but was returned null",
                       dst_class->PrettyDescriptor().c_str()).c_str());
    }
    return false;
  }

  JValue boxed_value;
  ObjPtr<mirror::Class> klass = o->GetClass();
  Primitive::Type primitive_type;
  ArtField* primitive_field = &klass->GetIFieldsPtr()->At(0);
  if (klass->DescriptorEquals("Ljava/lang/Boolean;")) {
    primitive_type = Primitive::kPrimBoolean;
    boxed_value.SetZ(primitive_field->GetBoolean(o));
  } else if (klass->DescriptorEquals("Ljava/lang/Byte;")) {
    primitive_type = Primitive::kPrimByte;
    boxed_value.SetB(primitive_field->GetByte(o));
  } else if (klass->DescriptorEquals("Ljava/lang/Character;")) {
    primitive_type = Primitive::kPrimChar;
    boxed_value.SetC(primitive_field->GetChar(o));
  } else if (klass->DescriptorEquals("Ljava/lang/Float;")) {
    primitive_type = Primitive::kPrimFloat;
    boxed_value.SetF(primitive_field->GetFloat(o));
  } else if (klass->DescriptorEquals("Ljava/lang/Double;")) {
    primitive_type = Primitive::kPrimDouble;
    boxed_value.SetD(primitive_field->GetDouble(o));
  } else if (klass->DescriptorEquals("Ljava/lang/Integer;")) {
    primitive_type = Primitive::kPrimInt;
    boxed_value.SetI(primitive_field->GetInt(o));
  } else if (klass->DescriptorEquals("Ljava/lang/Long;")) {
    primitive_type = Primitive::kPrimLong;
    boxed_value.SetJ(primitive_field->GetLong(o));
  } else if (klass->DescriptorEquals("Ljava/lang/Short;")) {
    primitive_type = Primitive::kPrimShort;
    boxed_value.SetS(primitive_field->GetShort(o));
  } else {
    std::string temp;
    ThrowIllegalArgumentException(
        StringPrintf("%s has type %s, got %s", UnboxingFailureKind(f).c_str(),
            dst_class->PrettyDescriptor().c_str(),
            PrettyDescriptor(o->GetClass()->GetDescriptor(&temp)).c_str()).c_str());
    return false;
  }

  return ConvertPrimitiveValue(unbox_for_result,
                               primitive_type,
                               dst_class->GetPrimitiveType(),
                               boxed_value, unboxed_value);
}

bool UnboxPrimitiveForField(ObjPtr<mirror::Object> o,
                            ObjPtr<mirror::Class> dst_class,
                            ArtField* f,
                            JValue* unboxed_value) {
  DCHECK(f != nullptr);
  return UnboxPrimitive(o, dst_class, f, unboxed_value);
}

bool UnboxPrimitiveForResult(ObjPtr<mirror::Object> o,
                             ObjPtr<mirror::Class> dst_class,
                             JValue* unboxed_value) {
  return UnboxPrimitive(o, dst_class, nullptr, unboxed_value);
}

ObjPtr<mirror::Class> GetCallingClass(Thread* self, size_t num_frames) {
  NthCallerVisitor visitor(self, num_frames);
  visitor.WalkStack();
  return visitor.caller != nullptr ? visitor.caller->GetDeclaringClass() : nullptr;
}

bool VerifyAccess(Thread* self,
                  ObjPtr<mirror::Object> obj,
                  ObjPtr<mirror::Class> declaring_class,
                  uint32_t access_flags,
                  ObjPtr<mirror::Class>* calling_class,
                  size_t num_frames) {
  if ((access_flags & kAccPublic) != 0) {
    return true;
  }
  ObjPtr<mirror::Class> klass = GetCallingClass(self, num_frames);
  if (UNLIKELY(klass == nullptr)) {
    // The caller is an attached native thread.
    return false;
  }
  *calling_class = klass;
  return VerifyAccess(obj, declaring_class, access_flags, klass);
}

bool VerifyAccess(ObjPtr<mirror::Object> obj,
                  ObjPtr<mirror::Class> declaring_class,
                  uint32_t access_flags,
                  ObjPtr<mirror::Class> calling_class) {
  if (calling_class == declaring_class) {
    return true;
  }
  ScopedAssertNoThreadSuspension sants("verify-access");
  if ((access_flags & kAccPrivate) != 0) {
    return false;
  }
  if ((access_flags & kAccProtected) != 0) {
    if (obj != nullptr && !obj->InstanceOf(calling_class) &&
        !declaring_class->IsInSamePackage(calling_class)) {
      return false;
    } else if (declaring_class->IsAssignableFrom(calling_class)) {
      return true;
    }
  }
  return declaring_class->IsInSamePackage(calling_class);
}

void InvalidReceiverError(ObjPtr<mirror::Object> o, ObjPtr<mirror::Class> c) {
  std::string expected_class_name(mirror::Class::PrettyDescriptor(c));
  std::string actual_class_name(mirror::Object::PrettyTypeOf(o));
  ThrowIllegalArgumentException(StringPrintf("Expected receiver of type %s, but got %s",
                                             expected_class_name.c_str(),
                                             actual_class_name.c_str()).c_str());
}

// This only works if there's one reference which points to the object in obj.
// Will need to be fixed if there's cases where it's not.
void UpdateReference(Thread* self, jobject obj, ObjPtr<mirror::Object> result) {
  IndirectRef ref = reinterpret_cast<IndirectRef>(obj);
  IndirectRefKind kind = IndirectReferenceTable::GetIndirectRefKind(ref);
  if (kind == kLocal) {
    self->GetJniEnv()->UpdateLocal(obj, result);
  } else if (kind == kHandleScopeOrInvalid) {
    LOG(FATAL) << "Unsupported UpdateReference for kind kHandleScopeOrInvalid";
  } else if (kind == kGlobal) {
    self->GetJniEnv()->GetVm()->UpdateGlobal(self, ref, result);
  } else {
    DCHECK_EQ(kind, kWeakGlobal);
    self->GetJniEnv()->GetVm()->UpdateWeakGlobal(self, ref, result);
  }
}

}  // namespace art
