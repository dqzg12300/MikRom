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

#include "class_linker.h"

#include <unistd.h>

#include <algorithm>
#include <deque>
#include <iostream>
#include <map>
#include <memory>
#include <queue>
#include <string>
#include <string_view>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>

#include "android-base/stringprintf.h"

#include "art_field-inl.h"
#include "art_method-inl.h"
#include "base/arena_allocator.h"
#include "base/casts.h"
#include "base/leb128.h"
#include "base/logging.h"
#include "base/os.h"
#include "base/quasi_atomic.h"
#include "base/scoped_arena_containers.h"
#include "base/scoped_flock.h"
#include "base/stl_util.h"
#include "base/string_view_cpp20.h"
#include "base/systrace.h"
#include "base/time_utils.h"
#include "base/unix_file/fd_file.h"
#include "base/utils.h"
#include "base/value_object.h"
#include "cha.h"
#include "class_linker-inl.h"
#include "class_loader_utils.h"
#include "class_root.h"
#include "class_table-inl.h"
#include "compiler_callbacks.h"
#include "debug_print.h"
#include "debugger.h"
#include "dex/class_accessor-inl.h"
#include "dex/descriptors_names.h"
#include "dex/dex_file-inl.h"
#include "dex/dex_file_exception_helpers.h"
#include "dex/dex_file_loader.h"
#include "dex/signature-inl.h"
#include "dex/utf.h"
#include "entrypoints/entrypoint_utils.h"
#include "entrypoints/runtime_asm_entrypoints.h"
#include "experimental_flags.h"
#include "gc/accounting/card_table-inl.h"
#include "gc/accounting/heap_bitmap-inl.h"
#include "gc/accounting/space_bitmap-inl.h"
#include "gc/heap-visit-objects-inl.h"
#include "gc/heap.h"
#include "gc/scoped_gc_critical_section.h"
#include "gc/space/image_space.h"
#include "gc/space/space-inl.h"
#include "gc_root-inl.h"
#include "handle_scope-inl.h"
#include "hidden_api.h"
#include "image-inl.h"
#include "imt_conflict_table.h"
#include "imtable-inl.h"
#include "intern_table-inl.h"
#include "interpreter/interpreter.h"
#include "jit/debugger_interface.h"
#include "jit/jit.h"
#include "jit/jit_code_cache.h"
#include "jni/java_vm_ext.h"
#include "jni/jni_internal.h"
#include "linear_alloc.h"
#include "mirror/array-alloc-inl.h"
#include "mirror/array-inl.h"
#include "mirror/call_site.h"
#include "mirror/class-alloc-inl.h"
#include "mirror/class-inl.h"
#include "mirror/class.h"
#include "mirror/class_ext.h"
#include "mirror/class_loader.h"
#include "mirror/dex_cache-inl.h"
#include "mirror/dex_cache.h"
#include "mirror/emulated_stack_frame.h"
#include "mirror/field.h"
#include "mirror/iftable-inl.h"
#include "mirror/method.h"
#include "mirror/method_handle_impl.h"
#include "mirror/method_handles_lookup.h"
#include "mirror/method_type.h"
#include "mirror/object-inl.h"
#include "mirror/object-refvisitor-inl.h"
#include "mirror/object_array-alloc-inl.h"
#include "mirror/object_array-inl.h"
#include "mirror/object_reference.h"
#include "mirror/object_reference-inl.h"
#include "mirror/proxy.h"
#include "mirror/reference-inl.h"
#include "mirror/stack_trace_element.h"
#include "mirror/string-inl.h"
#include "mirror/throwable.h"
#include "mirror/var_handle.h"
#include "native/dalvik_system_DexFile.h"
#include "nativehelper/scoped_local_ref.h"
#include "oat.h"
#include "oat_file-inl.h"
#include "oat_file.h"
#include "oat_file_assistant.h"
#include "oat_file_manager.h"
#include "object_lock.h"
#include "profile/profile_compilation_info.h"
#include "runtime.h"
#include "runtime_callbacks.h"
#include "scoped_thread_state_change-inl.h"
#include "thread-inl.h"
#include "thread_list.h"
#include "trace.h"
#include "utils/dex_cache_arrays_layout-inl.h"
#include "verifier/class_verifier.h"
#include "well_known_classes.h"

namespace art {

using android::base::StringPrintf;

static constexpr bool kSanityCheckObjects = kIsDebugBuild;
static constexpr bool kVerifyArtMethodDeclaringClasses = kIsDebugBuild;

static void ThrowNoClassDefFoundError(const char* fmt, ...)
    __attribute__((__format__(__printf__, 1, 2)))
    REQUIRES_SHARED(Locks::mutator_lock_);
static void ThrowNoClassDefFoundError(const char* fmt, ...) {
  va_list args;
  va_start(args, fmt);
  Thread* self = Thread::Current();
  self->ThrowNewExceptionV("Ljava/lang/NoClassDefFoundError;", fmt, args);
  va_end(args);
}

static bool HasInitWithString(Thread* self, ClassLinker* class_linker, const char* descriptor)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  ArtMethod* method = self->GetCurrentMethod(nullptr);
  StackHandleScope<1> hs(self);
  Handle<mirror::ClassLoader> class_loader(hs.NewHandle(method != nullptr ?
      method->GetDeclaringClass()->GetClassLoader() : nullptr));
  ObjPtr<mirror::Class> exception_class = class_linker->FindClass(self, descriptor, class_loader);

  if (exception_class == nullptr) {
    // No exc class ~ no <init>-with-string.
    CHECK(self->IsExceptionPending());
    self->ClearException();
    return false;
  }

  ArtMethod* exception_init_method = exception_class->FindConstructor(
      "(Ljava/lang/String;)V", class_linker->GetImagePointerSize());
  return exception_init_method != nullptr;
}

static ObjPtr<mirror::Object> GetVerifyError(ObjPtr<mirror::Class> c)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  ObjPtr<mirror::ClassExt> ext(c->GetExtData());
  if (ext == nullptr) {
    return nullptr;
  } else {
    return ext->GetVerifyError();
  }
}

// Helper for ThrowEarlierClassFailure. Throws the stored error.
static void HandleEarlierVerifyError(Thread* self,
                                     ClassLinker* class_linker,
                                     ObjPtr<mirror::Class> c)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  ObjPtr<mirror::Object> obj = GetVerifyError(c);
  DCHECK(obj != nullptr);
  self->AssertNoPendingException();
  if (obj->IsClass()) {
    // Previous error has been stored as class. Create a new exception of that type.

    // It's possible the exception doesn't have a <init>(String).
    std::string temp;
    const char* descriptor = obj->AsClass()->GetDescriptor(&temp);

    if (HasInitWithString(self, class_linker, descriptor)) {
      self->ThrowNewException(descriptor, c->PrettyDescriptor().c_str());
    } else {
      self->ThrowNewException(descriptor, nullptr);
    }
  } else {
    // Previous error has been stored as an instance. Just rethrow.
    ObjPtr<mirror::Class> throwable_class = GetClassRoot<mirror::Throwable>(class_linker);
    ObjPtr<mirror::Class> error_class = obj->GetClass();
    CHECK(throwable_class->IsAssignableFrom(error_class));
    self->SetException(obj->AsThrowable());
  }
  self->AssertPendingException();
}

// Ensures that methods have the kAccSkipAccessChecks bit set. We use the
// kAccVerificationAttempted bit on the class access flags to determine whether this has been done
// before.
template <bool kNeedsVerified = false>
static void EnsureSkipAccessChecksMethods(Handle<mirror::Class> klass, PointerSize pointer_size)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  if (kNeedsVerified) {
    // To not fail access-flags access checks, push a minimal state.
    mirror::Class::SetStatus(klass, ClassStatus::kVerified, Thread::Current());
  }
  if (!klass->WasVerificationAttempted()) {
    klass->SetSkipAccessChecksFlagOnAllMethods(pointer_size);
    klass->SetVerificationAttempted();
  }
}

void ClassLinker::ThrowEarlierClassFailure(ObjPtr<mirror::Class> c,
                                           bool wrap_in_no_class_def,
                                           bool log) {
  // The class failed to initialize on a previous attempt, so we want to throw
  // a NoClassDefFoundError (v2 2.17.5).  The exception to this rule is if we
  // failed in verification, in which case v2 5.4.1 says we need to re-throw
  // the previous error.
  Runtime* const runtime = Runtime::Current();
  if (!runtime->IsAotCompiler()) {  // Give info if this occurs at runtime.
    std::string extra;
    ObjPtr<mirror::Object> verify_error = GetVerifyError(c);
    if (verify_error != nullptr) {
      if (verify_error->IsClass()) {
        extra = mirror::Class::PrettyDescriptor(verify_error->AsClass());
      } else {
        extra = verify_error->AsThrowable()->Dump();
      }
    }
    if (log) {
      LOG(INFO) << "Rejecting re-init on previously-failed class " << c->PrettyClass()
                << ": " << extra;
    }
  }

  CHECK(c->IsErroneous()) << c->PrettyClass() << " " << c->GetStatus();
  Thread* self = Thread::Current();
  if (runtime->IsAotCompiler()) {
    // At compile time, accurate errors and NCDFE are disabled to speed compilation.
    ObjPtr<mirror::Throwable> pre_allocated = runtime->GetPreAllocatedNoClassDefFoundError();
    self->SetException(pre_allocated);
  } else {
    ObjPtr<mirror::Object> verify_error = GetVerifyError(c);
    if (verify_error != nullptr) {
      // Rethrow stored error.
      HandleEarlierVerifyError(self, this, c);
    }
    // TODO This might be wrong if we hit an OOME while allocating the ClassExt. In that case we
    // might have meant to go down the earlier if statement with the original error but it got
    // swallowed by the OOM so we end up here.
    if (verify_error == nullptr || wrap_in_no_class_def) {
      // If there isn't a recorded earlier error, or this is a repeat throw from initialization,
      // the top-level exception must be a NoClassDefFoundError. The potentially already pending
      // exception will be a cause.
      self->ThrowNewWrappedException("Ljava/lang/NoClassDefFoundError;",
                                     c->PrettyDescriptor().c_str());
    }
  }
}

static void VlogClassInitializationFailure(Handle<mirror::Class> klass)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  if (VLOG_IS_ON(class_linker)) {
    std::string temp;
    LOG(INFO) << "Failed to initialize class " << klass->GetDescriptor(&temp) << " from "
              << klass->GetLocation() << "\n" << Thread::Current()->GetException()->Dump();
  }
}

static void WrapExceptionInInitializer(Handle<mirror::Class> klass)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  Thread* self = Thread::Current();
  JNIEnv* env = self->GetJniEnv();

  ScopedLocalRef<jthrowable> cause(env, env->ExceptionOccurred());
  CHECK(cause.get() != nullptr);

  // Boot classpath classes should not fail initialization. This is a sanity debug check. This
  // cannot in general be guaranteed, but in all likelihood leads to breakage down the line.
  if (klass->GetClassLoader() == nullptr && !Runtime::Current()->IsAotCompiler()) {
    std::string tmp;
    // We want to LOG(FATAL) on debug builds since this really shouldn't be happening but we need to
    // make sure to only do it if we don't have AsyncExceptions being thrown around since those
    // could have caused the error.
    bool known_impossible = kIsDebugBuild && !Runtime::Current()->AreAsyncExceptionsThrown();
    LOG(known_impossible ? FATAL : WARNING) << klass->GetDescriptor(&tmp)
                                            << " failed initialization: "
                                            << self->GetException()->Dump();
  }

  env->ExceptionClear();
  bool is_error = env->IsInstanceOf(cause.get(), WellKnownClasses::java_lang_Error);
  env->Throw(cause.get());

  // We only wrap non-Error exceptions; an Error can just be used as-is.
  if (!is_error) {
    self->ThrowNewWrappedException("Ljava/lang/ExceptionInInitializerError;", nullptr);
  }
  VlogClassInitializationFailure(klass);
}

// Gap between two fields in object layout.
struct FieldGap {
  uint32_t start_offset;  // The offset from the start of the object.
  uint32_t size;  // The gap size of 1, 2, or 4 bytes.
};
struct FieldGapsComparator {
  FieldGapsComparator() {
  }
  bool operator() (const FieldGap& lhs, const FieldGap& rhs)
      NO_THREAD_SAFETY_ANALYSIS {
    // Sort by gap size, largest first. Secondary sort by starting offset.
    // Note that the priority queue returns the largest element, so operator()
    // should return true if lhs is less than rhs.
    return lhs.size < rhs.size || (lhs.size == rhs.size && lhs.start_offset > rhs.start_offset);
  }
};
using FieldGaps = std::priority_queue<FieldGap, std::vector<FieldGap>, FieldGapsComparator>;

// Adds largest aligned gaps to queue of gaps.
static void AddFieldGap(uint32_t gap_start, uint32_t gap_end, FieldGaps* gaps) {
  DCHECK(gaps != nullptr);

  uint32_t current_offset = gap_start;
  while (current_offset != gap_end) {
    size_t remaining = gap_end - current_offset;
    if (remaining >= sizeof(uint32_t) && IsAligned<4>(current_offset)) {
      gaps->push(FieldGap {current_offset, sizeof(uint32_t)});
      current_offset += sizeof(uint32_t);
    } else if (remaining >= sizeof(uint16_t) && IsAligned<2>(current_offset)) {
      gaps->push(FieldGap {current_offset, sizeof(uint16_t)});
      current_offset += sizeof(uint16_t);
    } else {
      gaps->push(FieldGap {current_offset, sizeof(uint8_t)});
      current_offset += sizeof(uint8_t);
    }
    DCHECK_LE(current_offset, gap_end) << "Overran gap";
  }
}
// Shuffle fields forward, making use of gaps whenever possible.
template<int n>
static void ShuffleForward(size_t* current_field_idx,
                           MemberOffset* field_offset,
                           std::deque<ArtField*>* grouped_and_sorted_fields,
                           FieldGaps* gaps)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  DCHECK(current_field_idx != nullptr);
  DCHECK(grouped_and_sorted_fields != nullptr);
  DCHECK(gaps != nullptr);
  DCHECK(field_offset != nullptr);

  DCHECK(IsPowerOfTwo(n));
  while (!grouped_and_sorted_fields->empty()) {
    ArtField* field = grouped_and_sorted_fields->front();
    Primitive::Type type = field->GetTypeAsPrimitiveType();
    if (Primitive::ComponentSize(type) < n) {
      break;
    }
    if (!IsAligned<n>(field_offset->Uint32Value())) {
      MemberOffset old_offset = *field_offset;
      *field_offset = MemberOffset(RoundUp(field_offset->Uint32Value(), n));
      AddFieldGap(old_offset.Uint32Value(), field_offset->Uint32Value(), gaps);
    }
    CHECK(type != Primitive::kPrimNot) << field->PrettyField();  // should be primitive types
    grouped_and_sorted_fields->pop_front();
    if (!gaps->empty() && gaps->top().size >= n) {
      FieldGap gap = gaps->top();
      gaps->pop();
      DCHECK_ALIGNED(gap.start_offset, n);
      field->SetOffset(MemberOffset(gap.start_offset));
      if (gap.size > n) {
        AddFieldGap(gap.start_offset + n, gap.start_offset + gap.size, gaps);
      }
    } else {
      DCHECK_ALIGNED(field_offset->Uint32Value(), n);
      field->SetOffset(*field_offset);
      *field_offset = MemberOffset(field_offset->Uint32Value() + n);
    }
    ++(*current_field_idx);
  }
}

ClassLinker::ClassLinker(InternTable* intern_table, bool fast_class_not_found_exceptions)
    : boot_class_table_(new ClassTable()),
      failed_dex_cache_class_lookups_(0),
      class_roots_(nullptr),
      find_array_class_cache_next_victim_(0),
      init_done_(false),
      log_new_roots_(false),
      intern_table_(intern_table),
      fast_class_not_found_exceptions_(fast_class_not_found_exceptions),
      quick_resolution_trampoline_(nullptr),
      quick_imt_conflict_trampoline_(nullptr),
      quick_generic_jni_trampoline_(nullptr),
      quick_to_interpreter_bridge_trampoline_(nullptr),
      image_pointer_size_(kRuntimePointerSize),
      cha_(Runtime::Current()->IsAotCompiler() ? nullptr : new ClassHierarchyAnalysis()) {
  // For CHA disabled during Aot, see b/34193647.

  CHECK(intern_table_ != nullptr);
  static_assert(kFindArrayCacheSize == arraysize(find_array_class_cache_),
                "Array cache size wrong.");
  std::fill_n(find_array_class_cache_, kFindArrayCacheSize, GcRoot<mirror::Class>(nullptr));
}

void ClassLinker::CheckSystemClass(Thread* self, Handle<mirror::Class> c1, const char* descriptor) {
  ObjPtr<mirror::Class> c2 = FindSystemClass(self, descriptor);
  if (c2 == nullptr) {
    LOG(FATAL) << "Could not find class " << descriptor;
    UNREACHABLE();
  }
  if (c1.Get() != c2) {
    std::ostringstream os1, os2;
    c1->DumpClass(os1, mirror::Class::kDumpClassFullDetail);
    c2->DumpClass(os2, mirror::Class::kDumpClassFullDetail);
    LOG(FATAL) << "InitWithoutImage: Class mismatch for " << descriptor
               << ". This is most likely the result of a broken build. Make sure that "
               << "libcore and art projects match.\n\n"
               << os1.str() << "\n\n" << os2.str();
    UNREACHABLE();
  }
}

bool ClassLinker::InitWithoutImage(std::vector<std::unique_ptr<const DexFile>> boot_class_path,
                                   std::string* error_msg) {
  VLOG(startup) << "ClassLinker::Init";

  Thread* const self = Thread::Current();
  Runtime* const runtime = Runtime::Current();
  gc::Heap* const heap = runtime->GetHeap();

  CHECK(!heap->HasBootImageSpace()) << "Runtime has image. We should use it.";
  CHECK(!init_done_);

  // Use the pointer size from the runtime since we are probably creating the image.
  image_pointer_size_ = InstructionSetPointerSize(runtime->GetInstructionSet());

  // java_lang_Class comes first, it's needed for AllocClass
  // The GC can't handle an object with a null class since we can't get the size of this object.
  heap->IncrementDisableMovingGC(self);
  StackHandleScope<64> hs(self);  // 64 is picked arbitrarily.
  auto class_class_size = mirror::Class::ClassClassSize(image_pointer_size_);
  // Allocate the object as non-movable so that there are no cases where Object::IsClass returns
  // the incorrect result when comparing to-space vs from-space.
  Handle<mirror::Class> java_lang_Class(hs.NewHandle(ObjPtr<mirror::Class>::DownCast(
      heap->AllocNonMovableObject<true>(self, nullptr, class_class_size, VoidFunctor()))));
  CHECK(java_lang_Class != nullptr);
  java_lang_Class->SetClassFlags(mirror::kClassFlagClass);
  java_lang_Class->SetClass(java_lang_Class.Get());
  if (kUseBakerReadBarrier) {
    java_lang_Class->AssertReadBarrierState();
  }
  java_lang_Class->SetClassSize(class_class_size);
  java_lang_Class->SetPrimitiveType(Primitive::kPrimNot);
  heap->DecrementDisableMovingGC(self);
  // AllocClass(ObjPtr<mirror::Class>) can now be used

  // Class[] is used for reflection support.
  auto class_array_class_size = mirror::ObjectArray<mirror::Class>::ClassSize(image_pointer_size_);
  Handle<mirror::Class> class_array_class(hs.NewHandle(
      AllocClass(self, java_lang_Class.Get(), class_array_class_size)));
  class_array_class->SetComponentType(java_lang_Class.Get());

  // java_lang_Object comes next so that object_array_class can be created.
  Handle<mirror::Class> java_lang_Object(hs.NewHandle(
      AllocClass(self, java_lang_Class.Get(), mirror::Object::ClassSize(image_pointer_size_))));
  CHECK(java_lang_Object != nullptr);
  // backfill Object as the super class of Class.
  java_lang_Class->SetSuperClass(java_lang_Object.Get());
  mirror::Class::SetStatus(java_lang_Object, ClassStatus::kLoaded, self);

  java_lang_Object->SetObjectSize(sizeof(mirror::Object));
  // Allocate in non-movable so that it's possible to check if a JNI weak global ref has been
  // cleared without triggering the read barrier and unintentionally mark the sentinel alive.
  runtime->SetSentinel(heap->AllocNonMovableObject<true>(self,
                                                         java_lang_Object.Get(),
                                                         java_lang_Object->GetObjectSize(),
                                                         VoidFunctor()));

  // Initialize the SubtypeCheck bitstring for java.lang.Object and java.lang.Class.
  if (kBitstringSubtypeCheckEnabled) {
    // It might seem the lock here is unnecessary, however all the SubtypeCheck
    // functions are annotated to require locks all the way down.
    //
    // We take the lock here to avoid using NO_THREAD_SAFETY_ANALYSIS.
    MutexLock subtype_check_lock(Thread::Current(), *Locks::subtype_check_lock_);
    SubtypeCheck<ObjPtr<mirror::Class>>::EnsureInitialized(java_lang_Object.Get());
    SubtypeCheck<ObjPtr<mirror::Class>>::EnsureInitialized(java_lang_Class.Get());
  }

  // Object[] next to hold class roots.
  Handle<mirror::Class> object_array_class(hs.NewHandle(
      AllocClass(self, java_lang_Class.Get(),
                 mirror::ObjectArray<mirror::Object>::ClassSize(image_pointer_size_))));
  object_array_class->SetComponentType(java_lang_Object.Get());

  // Setup java.lang.String.
  //
  // We make this class non-movable for the unlikely case where it were to be
  // moved by a sticky-bit (minor) collection when using the Generational
  // Concurrent Copying (CC) collector, potentially creating a stale reference
  // in the `klass_` field of one of its instances allocated in the Large-Object
  // Space (LOS) -- see the comment about the dirty card scanning logic in
  // art::gc::collector::ConcurrentCopying::MarkingPhase.
  Handle<mirror::Class> java_lang_String(hs.NewHandle(
      AllocClass</* kMovable= */ false>(
          self, java_lang_Class.Get(), mirror::String::ClassSize(image_pointer_size_))));
  java_lang_String->SetStringClass();
  mirror::Class::SetStatus(java_lang_String, ClassStatus::kResolved, self);

  // Setup java.lang.ref.Reference.
  Handle<mirror::Class> java_lang_ref_Reference(hs.NewHandle(
      AllocClass(self, java_lang_Class.Get(), mirror::Reference::ClassSize(image_pointer_size_))));
  java_lang_ref_Reference->SetObjectSize(mirror::Reference::InstanceSize());
  mirror::Class::SetStatus(java_lang_ref_Reference, ClassStatus::kResolved, self);

  // Create storage for root classes, save away our work so far (requires descriptors).
  class_roots_ = GcRoot<mirror::ObjectArray<mirror::Class>>(
      mirror::ObjectArray<mirror::Class>::Alloc(self,
                                                object_array_class.Get(),
                                                static_cast<int32_t>(ClassRoot::kMax)));
  CHECK(!class_roots_.IsNull());
  SetClassRoot(ClassRoot::kJavaLangClass, java_lang_Class.Get());
  SetClassRoot(ClassRoot::kJavaLangObject, java_lang_Object.Get());
  SetClassRoot(ClassRoot::kClassArrayClass, class_array_class.Get());
  SetClassRoot(ClassRoot::kObjectArrayClass, object_array_class.Get());
  SetClassRoot(ClassRoot::kJavaLangString, java_lang_String.Get());
  SetClassRoot(ClassRoot::kJavaLangRefReference, java_lang_ref_Reference.Get());

  // Fill in the empty iftable. Needs to be done after the kObjectArrayClass root is set.
  java_lang_Object->SetIfTable(AllocIfTable(self, 0));

  // Create array interface entries to populate once we can load system classes.
  object_array_class->SetIfTable(AllocIfTable(self, 2));
  DCHECK_EQ(GetArrayIfTable(), object_array_class->GetIfTable());

  // Setup the primitive type classes.
  SetClassRoot(ClassRoot::kPrimitiveBoolean, CreatePrimitiveClass(self, Primitive::kPrimBoolean));
  SetClassRoot(ClassRoot::kPrimitiveByte, CreatePrimitiveClass(self, Primitive::kPrimByte));
  SetClassRoot(ClassRoot::kPrimitiveChar, CreatePrimitiveClass(self, Primitive::kPrimChar));
  SetClassRoot(ClassRoot::kPrimitiveShort, CreatePrimitiveClass(self, Primitive::kPrimShort));
  SetClassRoot(ClassRoot::kPrimitiveInt, CreatePrimitiveClass(self, Primitive::kPrimInt));
  SetClassRoot(ClassRoot::kPrimitiveLong, CreatePrimitiveClass(self, Primitive::kPrimLong));
  SetClassRoot(ClassRoot::kPrimitiveFloat, CreatePrimitiveClass(self, Primitive::kPrimFloat));
  SetClassRoot(ClassRoot::kPrimitiveDouble, CreatePrimitiveClass(self, Primitive::kPrimDouble));
  SetClassRoot(ClassRoot::kPrimitiveVoid, CreatePrimitiveClass(self, Primitive::kPrimVoid));

  // Create int array type for native pointer arrays (for example vtables) on 32-bit archs.
  Handle<mirror::Class> int_array_class(hs.NewHandle(
      AllocPrimitiveArrayClass(self, java_lang_Class.Get())));
  int_array_class->SetComponentType(GetClassRoot(ClassRoot::kPrimitiveInt, this));
  SetClassRoot(ClassRoot::kIntArrayClass, int_array_class.Get());

  // Create long array type for native pointer arrays (for example vtables) on 64-bit archs.
  Handle<mirror::Class> long_array_class(hs.NewHandle(
      AllocPrimitiveArrayClass(self, java_lang_Class.Get())));
  long_array_class->SetComponentType(GetClassRoot(ClassRoot::kPrimitiveLong, this));
  SetClassRoot(ClassRoot::kLongArrayClass, long_array_class.Get());

  // now that these are registered, we can use AllocClass() and AllocObjectArray

  // Set up DexCache. This cannot be done later since AppendToBootClassPath calls AllocDexCache.
  Handle<mirror::Class> java_lang_DexCache(hs.NewHandle(
      AllocClass(self, java_lang_Class.Get(), mirror::DexCache::ClassSize(image_pointer_size_))));
  SetClassRoot(ClassRoot::kJavaLangDexCache, java_lang_DexCache.Get());
  java_lang_DexCache->SetDexCacheClass();
  java_lang_DexCache->SetObjectSize(mirror::DexCache::InstanceSize());
  mirror::Class::SetStatus(java_lang_DexCache, ClassStatus::kResolved, self);


  // Setup dalvik.system.ClassExt
  Handle<mirror::Class> dalvik_system_ClassExt(hs.NewHandle(
      AllocClass(self, java_lang_Class.Get(), mirror::ClassExt::ClassSize(image_pointer_size_))));
  SetClassRoot(ClassRoot::kDalvikSystemClassExt, dalvik_system_ClassExt.Get());
  mirror::Class::SetStatus(dalvik_system_ClassExt, ClassStatus::kResolved, self);

  // Set up array classes for string, field, method
  Handle<mirror::Class> object_array_string(hs.NewHandle(
      AllocClass(self, java_lang_Class.Get(),
                 mirror::ObjectArray<mirror::String>::ClassSize(image_pointer_size_))));
  object_array_string->SetComponentType(java_lang_String.Get());
  SetClassRoot(ClassRoot::kJavaLangStringArrayClass, object_array_string.Get());

  LinearAlloc* linear_alloc = runtime->GetLinearAlloc();
  // Create runtime resolution and imt conflict methods.
  runtime->SetResolutionMethod(runtime->CreateResolutionMethod());
  runtime->SetImtConflictMethod(runtime->CreateImtConflictMethod(linear_alloc));
  runtime->SetImtUnimplementedMethod(runtime->CreateImtConflictMethod(linear_alloc));

  // Setup boot_class_path_ and register class_path now that we can use AllocObjectArray to create
  // DexCache instances. Needs to be after String, Field, Method arrays since AllocDexCache uses
  // these roots.
  if (boot_class_path.empty()) {
    *error_msg = "Boot classpath is empty.";
    return false;
  }
  for (auto& dex_file : boot_class_path) {
    if (dex_file.get() == nullptr) {
      *error_msg = "Null dex file.";
      return false;
    }
    AppendToBootClassPath(self, *dex_file);
    boot_dex_files_.push_back(std::move(dex_file));
  }

  // now we can use FindSystemClass

  // Set up GenericJNI entrypoint. That is mainly a hack for common_compiler_test.h so that
  // we do not need friend classes or a publicly exposed setter.
  quick_generic_jni_trampoline_ = GetQuickGenericJniStub();
  if (!runtime->IsAotCompiler()) {
    // We need to set up the generic trampolines since we don't have an image.
    quick_resolution_trampoline_ = GetQuickResolutionStub();
    quick_imt_conflict_trampoline_ = GetQuickImtConflictStub();
    quick_to_interpreter_bridge_trampoline_ = GetQuickToInterpreterBridge();
  }

  // Object, String, ClassExt and DexCache need to be rerun through FindSystemClass to finish init
  mirror::Class::SetStatus(java_lang_Object, ClassStatus::kNotReady, self);
  CheckSystemClass(self, java_lang_Object, "Ljava/lang/Object;");
  CHECK_EQ(java_lang_Object->GetObjectSize(), mirror::Object::InstanceSize());
  mirror::Class::SetStatus(java_lang_String, ClassStatus::kNotReady, self);
  CheckSystemClass(self, java_lang_String, "Ljava/lang/String;");
  mirror::Class::SetStatus(java_lang_DexCache, ClassStatus::kNotReady, self);
  CheckSystemClass(self, java_lang_DexCache, "Ljava/lang/DexCache;");
  CHECK_EQ(java_lang_DexCache->GetObjectSize(), mirror::DexCache::InstanceSize());
  mirror::Class::SetStatus(dalvik_system_ClassExt, ClassStatus::kNotReady, self);
  CheckSystemClass(self, dalvik_system_ClassExt, "Ldalvik/system/ClassExt;");
  CHECK_EQ(dalvik_system_ClassExt->GetObjectSize(), mirror::ClassExt::InstanceSize());

  // Setup the primitive array type classes - can't be done until Object has a vtable.
  AllocAndSetPrimitiveArrayClassRoot(self,
                                     java_lang_Class.Get(),
                                     ClassRoot::kBooleanArrayClass,
                                     ClassRoot::kPrimitiveBoolean,
                                     "[Z");

  AllocAndSetPrimitiveArrayClassRoot(
      self, java_lang_Class.Get(), ClassRoot::kByteArrayClass, ClassRoot::kPrimitiveByte, "[B");

  AllocAndSetPrimitiveArrayClassRoot(
      self, java_lang_Class.Get(), ClassRoot::kCharArrayClass, ClassRoot::kPrimitiveChar, "[C");

  AllocAndSetPrimitiveArrayClassRoot(
      self, java_lang_Class.Get(), ClassRoot::kShortArrayClass, ClassRoot::kPrimitiveShort, "[S");

  CheckSystemClass(self, int_array_class, "[I");
  CheckSystemClass(self, long_array_class, "[J");

  AllocAndSetPrimitiveArrayClassRoot(
      self, java_lang_Class.Get(), ClassRoot::kFloatArrayClass, ClassRoot::kPrimitiveFloat, "[F");

  AllocAndSetPrimitiveArrayClassRoot(
      self, java_lang_Class.Get(), ClassRoot::kDoubleArrayClass, ClassRoot::kPrimitiveDouble, "[D");

  // Run Class through FindSystemClass. This initializes the dex_cache_ fields and register it
  // in class_table_.
  CheckSystemClass(self, java_lang_Class, "Ljava/lang/Class;");

  CheckSystemClass(self, class_array_class, "[Ljava/lang/Class;");
  CheckSystemClass(self, object_array_class, "[Ljava/lang/Object;");

  // Setup the single, global copy of "iftable".
  auto java_lang_Cloneable = hs.NewHandle(FindSystemClass(self, "Ljava/lang/Cloneable;"));
  CHECK(java_lang_Cloneable != nullptr);
  auto java_io_Serializable = hs.NewHandle(FindSystemClass(self, "Ljava/io/Serializable;"));
  CHECK(java_io_Serializable != nullptr);
  // We assume that Cloneable/Serializable don't have superinterfaces -- normally we'd have to
  // crawl up and explicitly list all of the supers as well.
  object_array_class->GetIfTable()->SetInterface(0, java_lang_Cloneable.Get());
  object_array_class->GetIfTable()->SetInterface(1, java_io_Serializable.Get());

  // Sanity check Class[] and Object[]'s interfaces. GetDirectInterface may cause thread
  // suspension.
  CHECK_EQ(java_lang_Cloneable.Get(),
           mirror::Class::GetDirectInterface(self, class_array_class.Get(), 0));
  CHECK_EQ(java_io_Serializable.Get(),
           mirror::Class::GetDirectInterface(self, class_array_class.Get(), 1));
  CHECK_EQ(java_lang_Cloneable.Get(),
           mirror::Class::GetDirectInterface(self, object_array_class.Get(), 0));
  CHECK_EQ(java_io_Serializable.Get(),
           mirror::Class::GetDirectInterface(self, object_array_class.Get(), 1));

  CHECK_EQ(object_array_string.Get(),
           FindSystemClass(self, GetClassRootDescriptor(ClassRoot::kJavaLangStringArrayClass)));

  // End of special init trickery, all subsequent classes may be loaded via FindSystemClass.

  // Create java.lang.reflect.Proxy root.
  SetClassRoot(ClassRoot::kJavaLangReflectProxy,
               FindSystemClass(self, "Ljava/lang/reflect/Proxy;"));

  // Create java.lang.reflect.Field.class root.
  ObjPtr<mirror::Class> class_root = FindSystemClass(self, "Ljava/lang/reflect/Field;");
  CHECK(class_root != nullptr);
  SetClassRoot(ClassRoot::kJavaLangReflectField, class_root);

  // Create java.lang.reflect.Field array root.
  class_root = FindSystemClass(self, "[Ljava/lang/reflect/Field;");
  CHECK(class_root != nullptr);
  SetClassRoot(ClassRoot::kJavaLangReflectFieldArrayClass, class_root);

  // Create java.lang.reflect.Constructor.class root and array root.
  class_root = FindSystemClass(self, "Ljava/lang/reflect/Constructor;");
  CHECK(class_root != nullptr);
  SetClassRoot(ClassRoot::kJavaLangReflectConstructor, class_root);
  class_root = FindSystemClass(self, "[Ljava/lang/reflect/Constructor;");
  CHECK(class_root != nullptr);
  SetClassRoot(ClassRoot::kJavaLangReflectConstructorArrayClass, class_root);

  // Create java.lang.reflect.Method.class root and array root.
  class_root = FindSystemClass(self, "Ljava/lang/reflect/Method;");
  CHECK(class_root != nullptr);
  SetClassRoot(ClassRoot::kJavaLangReflectMethod, class_root);
  class_root = FindSystemClass(self, "[Ljava/lang/reflect/Method;");
  CHECK(class_root != nullptr);
  SetClassRoot(ClassRoot::kJavaLangReflectMethodArrayClass, class_root);

  // Create java.lang.invoke.CallSite.class root
  class_root = FindSystemClass(self, "Ljava/lang/invoke/CallSite;");
  CHECK(class_root != nullptr);
  SetClassRoot(ClassRoot::kJavaLangInvokeCallSite, class_root);

  // Create java.lang.invoke.MethodType.class root
  class_root = FindSystemClass(self, "Ljava/lang/invoke/MethodType;");
  CHECK(class_root != nullptr);
  SetClassRoot(ClassRoot::kJavaLangInvokeMethodType, class_root);

  // Create java.lang.invoke.MethodHandleImpl.class root
  class_root = FindSystemClass(self, "Ljava/lang/invoke/MethodHandleImpl;");
  CHECK(class_root != nullptr);
  SetClassRoot(ClassRoot::kJavaLangInvokeMethodHandleImpl, class_root);
  SetClassRoot(ClassRoot::kJavaLangInvokeMethodHandle, class_root->GetSuperClass());

  // Create java.lang.invoke.MethodHandles.Lookup.class root
  class_root = FindSystemClass(self, "Ljava/lang/invoke/MethodHandles$Lookup;");
  CHECK(class_root != nullptr);
  SetClassRoot(ClassRoot::kJavaLangInvokeMethodHandlesLookup, class_root);

  // Create java.lang.invoke.VarHandle.class root
  class_root = FindSystemClass(self, "Ljava/lang/invoke/VarHandle;");
  CHECK(class_root != nullptr);
  SetClassRoot(ClassRoot::kJavaLangInvokeVarHandle, class_root);

  // Create java.lang.invoke.FieldVarHandle.class root
  class_root = FindSystemClass(self, "Ljava/lang/invoke/FieldVarHandle;");
  CHECK(class_root != nullptr);
  SetClassRoot(ClassRoot::kJavaLangInvokeFieldVarHandle, class_root);

  // Create java.lang.invoke.ArrayElementVarHandle.class root
  class_root = FindSystemClass(self, "Ljava/lang/invoke/ArrayElementVarHandle;");
  CHECK(class_root != nullptr);
  SetClassRoot(ClassRoot::kJavaLangInvokeArrayElementVarHandle, class_root);

  // Create java.lang.invoke.ByteArrayViewVarHandle.class root
  class_root = FindSystemClass(self, "Ljava/lang/invoke/ByteArrayViewVarHandle;");
  CHECK(class_root != nullptr);
  SetClassRoot(ClassRoot::kJavaLangInvokeByteArrayViewVarHandle, class_root);

  // Create java.lang.invoke.ByteBufferViewVarHandle.class root
  class_root = FindSystemClass(self, "Ljava/lang/invoke/ByteBufferViewVarHandle;");
  CHECK(class_root != nullptr);
  SetClassRoot(ClassRoot::kJavaLangInvokeByteBufferViewVarHandle, class_root);

  class_root = FindSystemClass(self, "Ldalvik/system/EmulatedStackFrame;");
  CHECK(class_root != nullptr);
  SetClassRoot(ClassRoot::kDalvikSystemEmulatedStackFrame, class_root);

  // java.lang.ref classes need to be specially flagged, but otherwise are normal classes
  // finish initializing Reference class
  mirror::Class::SetStatus(java_lang_ref_Reference, ClassStatus::kNotReady, self);
  CheckSystemClass(self, java_lang_ref_Reference, "Ljava/lang/ref/Reference;");
  CHECK_EQ(java_lang_ref_Reference->GetObjectSize(), mirror::Reference::InstanceSize());
  CHECK_EQ(java_lang_ref_Reference->GetClassSize(),
           mirror::Reference::ClassSize(image_pointer_size_));
  class_root = FindSystemClass(self, "Ljava/lang/ref/FinalizerReference;");
  CHECK_EQ(class_root->GetClassFlags(), mirror::kClassFlagNormal);
  class_root->SetClassFlags(class_root->GetClassFlags() | mirror::kClassFlagFinalizerReference);
  class_root = FindSystemClass(self, "Ljava/lang/ref/PhantomReference;");
  CHECK_EQ(class_root->GetClassFlags(), mirror::kClassFlagNormal);
  class_root->SetClassFlags(class_root->GetClassFlags() | mirror::kClassFlagPhantomReference);
  class_root = FindSystemClass(self, "Ljava/lang/ref/SoftReference;");
  CHECK_EQ(class_root->GetClassFlags(), mirror::kClassFlagNormal);
  class_root->SetClassFlags(class_root->GetClassFlags() | mirror::kClassFlagSoftReference);
  class_root = FindSystemClass(self, "Ljava/lang/ref/WeakReference;");
  CHECK_EQ(class_root->GetClassFlags(), mirror::kClassFlagNormal);
  class_root->SetClassFlags(class_root->GetClassFlags() | mirror::kClassFlagWeakReference);

  // Setup the ClassLoader, verifying the object_size_.
  class_root = FindSystemClass(self, "Ljava/lang/ClassLoader;");
  class_root->SetClassLoaderClass();
  CHECK_EQ(class_root->GetObjectSize(), mirror::ClassLoader::InstanceSize());
  SetClassRoot(ClassRoot::kJavaLangClassLoader, class_root);

  // Set up java.lang.Throwable, java.lang.ClassNotFoundException, and
  // java.lang.StackTraceElement as a convenience.
  SetClassRoot(ClassRoot::kJavaLangThrowable, FindSystemClass(self, "Ljava/lang/Throwable;"));
  SetClassRoot(ClassRoot::kJavaLangClassNotFoundException,
               FindSystemClass(self, "Ljava/lang/ClassNotFoundException;"));
  SetClassRoot(ClassRoot::kJavaLangStackTraceElement,
               FindSystemClass(self, "Ljava/lang/StackTraceElement;"));
  SetClassRoot(ClassRoot::kJavaLangStackTraceElementArrayClass,
               FindSystemClass(self, "[Ljava/lang/StackTraceElement;"));
  SetClassRoot(ClassRoot::kJavaLangClassLoaderArrayClass,
               FindSystemClass(self, "[Ljava/lang/ClassLoader;"));

  // Create conflict tables that depend on the class linker.
  runtime->FixupConflictTables();

  FinishInit(self);

  VLOG(startup) << "ClassLinker::InitFromCompiler exiting";

  return true;
}

static void CreateStringInitBindings(Thread* self, ClassLinker* class_linker)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  // Find String.<init> -> StringFactory bindings.
  ObjPtr<mirror::Class> string_factory_class =
      class_linker->FindSystemClass(self, "Ljava/lang/StringFactory;");
  CHECK(string_factory_class != nullptr);
  ObjPtr<mirror::Class> string_class = GetClassRoot<mirror::String>(class_linker);
  WellKnownClasses::InitStringInit(string_class, string_factory_class);
  // Update the primordial thread.
  self->InitStringEntryPoints();
}

void ClassLinker::FinishInit(Thread* self) {
  VLOG(startup) << "ClassLinker::FinishInit entering";

  CreateStringInitBindings(self, this);

  // Let the heap know some key offsets into java.lang.ref instances
  // Note: we hard code the field indexes here rather than using FindInstanceField
  // as the types of the field can't be resolved prior to the runtime being
  // fully initialized
  StackHandleScope<3> hs(self);
  Handle<mirror::Class> java_lang_ref_Reference =
      hs.NewHandle(GetClassRoot<mirror::Reference>(this));
  Handle<mirror::Class> java_lang_ref_FinalizerReference =
      hs.NewHandle(FindSystemClass(self, "Ljava/lang/ref/FinalizerReference;"));

  ArtField* pendingNext = java_lang_ref_Reference->GetInstanceField(0);
  CHECK_STREQ(pendingNext->GetName(), "pendingNext");
  CHECK_STREQ(pendingNext->GetTypeDescriptor(), "Ljava/lang/ref/Reference;");

  ArtField* queue = java_lang_ref_Reference->GetInstanceField(1);
  CHECK_STREQ(queue->GetName(), "queue");
  CHECK_STREQ(queue->GetTypeDescriptor(), "Ljava/lang/ref/ReferenceQueue;");

  ArtField* queueNext = java_lang_ref_Reference->GetInstanceField(2);
  CHECK_STREQ(queueNext->GetName(), "queueNext");
  CHECK_STREQ(queueNext->GetTypeDescriptor(), "Ljava/lang/ref/Reference;");

  ArtField* referent = java_lang_ref_Reference->GetInstanceField(3);
  CHECK_STREQ(referent->GetName(), "referent");
  CHECK_STREQ(referent->GetTypeDescriptor(), "Ljava/lang/Object;");

  ArtField* zombie = java_lang_ref_FinalizerReference->GetInstanceField(2);
  CHECK_STREQ(zombie->GetName(), "zombie");
  CHECK_STREQ(zombie->GetTypeDescriptor(), "Ljava/lang/Object;");

  // ensure all class_roots_ are initialized
  for (size_t i = 0; i < static_cast<size_t>(ClassRoot::kMax); i++) {
    ClassRoot class_root = static_cast<ClassRoot>(i);
    ObjPtr<mirror::Class> klass = GetClassRoot(class_root);
    CHECK(klass != nullptr);
    DCHECK(klass->IsArrayClass() || klass->IsPrimitive() || klass->GetDexCache() != nullptr);
    // note SetClassRoot does additional validation.
    // if possible add new checks there to catch errors early
  }

  CHECK(GetArrayIfTable() != nullptr);

  // disable the slow paths in FindClass and CreatePrimitiveClass now
  // that Object, Class, and Object[] are setup
  init_done_ = true;

  // Under sanitization, the small carve-out to handle stack overflow might not be enough to
  // initialize the StackOverflowError class (as it might require running the verifier). Instead,
  // ensure that the class will be initialized.
  if (kMemoryToolIsAvailable && !Runtime::Current()->IsAotCompiler()) {
    verifier::ClassVerifier::Init();  // Need to prepare the verifier.

    ObjPtr<mirror::Class> soe_klass = FindSystemClass(self, "Ljava/lang/StackOverflowError;");
    if (soe_klass == nullptr || !EnsureInitialized(self, hs.NewHandle(soe_klass), true, true)) {
      // Strange, but don't crash.
      LOG(WARNING) << "Could not prepare StackOverflowError.";
      self->ClearException();
    }
  }

  VLOG(startup) << "ClassLinker::FinishInit exiting";
}

void ClassLinker::RunRootClinits(Thread* self) {
  for (size_t i = 0; i < static_cast<size_t>(ClassRoot::kMax); ++i) {
    ObjPtr<mirror::Class> c = GetClassRoot(ClassRoot(i), this);
    if (!c->IsArrayClass() && !c->IsPrimitive()) {
      StackHandleScope<1> hs(self);
      Handle<mirror::Class> h_class(hs.NewHandle(c));
      EnsureInitialized(self, h_class, true, true);
      self->AssertNoPendingException();
    } else {
      DCHECK(c->IsInitialized());
    }
  }
}

struct TrampolineCheckData {
  const void* quick_resolution_trampoline;
  const void* quick_imt_conflict_trampoline;
  const void* quick_generic_jni_trampoline;
  const void* quick_to_interpreter_bridge_trampoline;
  PointerSize pointer_size;
  ArtMethod* m;
  bool error;
};

bool ClassLinker::InitFromBootImage(std::string* error_msg) {
  VLOG(startup) << __FUNCTION__ << " entering";
  CHECK(!init_done_);

  Runtime* const runtime = Runtime::Current();
  Thread* const self = Thread::Current();
  gc::Heap* const heap = runtime->GetHeap();
  std::vector<gc::space::ImageSpace*> spaces = heap->GetBootImageSpaces();
  CHECK(!spaces.empty());
  uint32_t pointer_size_unchecked = spaces[0]->GetImageHeader().GetPointerSizeUnchecked();
  if (!ValidPointerSize(pointer_size_unchecked)) {
    *error_msg = StringPrintf("Invalid image pointer size: %u", pointer_size_unchecked);
    return false;
  }
  const ImageHeader& image_header = spaces[0]->GetImageHeader();
  image_pointer_size_ = image_header.GetPointerSize();
  if (!runtime->IsAotCompiler()) {
    // Only the Aot compiler supports having an image with a different pointer size than the
    // runtime. This happens on the host for compiling 32 bit tests since we use a 64 bit libart
    // compiler. We may also use 32 bit dex2oat on a system with 64 bit apps.
    if (image_pointer_size_ != kRuntimePointerSize) {
      *error_msg = StringPrintf("Runtime must use current image pointer size: %zu vs %zu",
                                static_cast<size_t>(image_pointer_size_),
                                sizeof(void*));
      return false;
    }
  }
  DCHECK(!runtime->HasResolutionMethod());
  runtime->SetResolutionMethod(image_header.GetImageMethod(ImageHeader::kResolutionMethod));
  runtime->SetImtConflictMethod(image_header.GetImageMethod(ImageHeader::kImtConflictMethod));
  runtime->SetImtUnimplementedMethod(
      image_header.GetImageMethod(ImageHeader::kImtUnimplementedMethod));
  runtime->SetCalleeSaveMethod(
      image_header.GetImageMethod(ImageHeader::kSaveAllCalleeSavesMethod),
      CalleeSaveType::kSaveAllCalleeSaves);
  runtime->SetCalleeSaveMethod(
      image_header.GetImageMethod(ImageHeader::kSaveRefsOnlyMethod),
      CalleeSaveType::kSaveRefsOnly);
  runtime->SetCalleeSaveMethod(
      image_header.GetImageMethod(ImageHeader::kSaveRefsAndArgsMethod),
      CalleeSaveType::kSaveRefsAndArgs);
  runtime->SetCalleeSaveMethod(
      image_header.GetImageMethod(ImageHeader::kSaveEverythingMethod),
      CalleeSaveType::kSaveEverything);
  runtime->SetCalleeSaveMethod(
      image_header.GetImageMethod(ImageHeader::kSaveEverythingMethodForClinit),
      CalleeSaveType::kSaveEverythingForClinit);
  runtime->SetCalleeSaveMethod(
      image_header.GetImageMethod(ImageHeader::kSaveEverythingMethodForSuspendCheck),
      CalleeSaveType::kSaveEverythingForSuspendCheck);

  std::vector<const OatFile*> oat_files =
      runtime->GetOatFileManager().RegisterImageOatFiles(spaces);
  DCHECK(!oat_files.empty());
  const OatHeader& default_oat_header = oat_files[0]->GetOatHeader();
  quick_resolution_trampoline_ = default_oat_header.GetQuickResolutionTrampoline();
  quick_imt_conflict_trampoline_ = default_oat_header.GetQuickImtConflictTrampoline();
  quick_generic_jni_trampoline_ = default_oat_header.GetQuickGenericJniTrampoline();
  quick_to_interpreter_bridge_trampoline_ = default_oat_header.GetQuickToInterpreterBridge();
  if (kIsDebugBuild) {
    // Check that the other images use the same trampoline.
    for (size_t i = 1; i < oat_files.size(); ++i) {
      const OatHeader& ith_oat_header = oat_files[i]->GetOatHeader();
      const void* ith_quick_resolution_trampoline =
          ith_oat_header.GetQuickResolutionTrampoline();
      const void* ith_quick_imt_conflict_trampoline =
          ith_oat_header.GetQuickImtConflictTrampoline();
      const void* ith_quick_generic_jni_trampoline =
          ith_oat_header.GetQuickGenericJniTrampoline();
      const void* ith_quick_to_interpreter_bridge_trampoline =
          ith_oat_header.GetQuickToInterpreterBridge();
      if (ith_quick_resolution_trampoline != quick_resolution_trampoline_ ||
          ith_quick_imt_conflict_trampoline != quick_imt_conflict_trampoline_ ||
          ith_quick_generic_jni_trampoline != quick_generic_jni_trampoline_ ||
          ith_quick_to_interpreter_bridge_trampoline != quick_to_interpreter_bridge_trampoline_) {
        // Make sure that all methods in this image do not contain those trampolines as
        // entrypoints. Otherwise the class-linker won't be able to work with a single set.
        TrampolineCheckData data;
        data.error = false;
        data.pointer_size = GetImagePointerSize();
        data.quick_resolution_trampoline = ith_quick_resolution_trampoline;
        data.quick_imt_conflict_trampoline = ith_quick_imt_conflict_trampoline;
        data.quick_generic_jni_trampoline = ith_quick_generic_jni_trampoline;
        data.quick_to_interpreter_bridge_trampoline = ith_quick_to_interpreter_bridge_trampoline;
        ReaderMutexLock mu(self, *Locks::heap_bitmap_lock_);
        auto visitor = [&](mirror::Object* obj) REQUIRES_SHARED(Locks::mutator_lock_) {
          if (obj->IsClass()) {
            ObjPtr<mirror::Class> klass = obj->AsClass();
            for (ArtMethod& m : klass->GetMethods(data.pointer_size)) {
              const void* entrypoint =
                  m.GetEntryPointFromQuickCompiledCodePtrSize(data.pointer_size);
              if (entrypoint == data.quick_resolution_trampoline ||
                  entrypoint == data.quick_imt_conflict_trampoline ||
                  entrypoint == data.quick_generic_jni_trampoline ||
                  entrypoint == data.quick_to_interpreter_bridge_trampoline) {
                data.m = &m;
                data.error = true;
                return;
              }
            }
          }
        };
        spaces[i]->GetLiveBitmap()->Walk(visitor);
        if (data.error) {
          ArtMethod* m = data.m;
          LOG(ERROR) << "Found a broken ArtMethod: " << ArtMethod::PrettyMethod(m);
          *error_msg = "Found an ArtMethod with a bad entrypoint";
          return false;
        }
      }
    }
  }

  class_roots_ = GcRoot<mirror::ObjectArray<mirror::Class>>(
      ObjPtr<mirror::ObjectArray<mirror::Class>>::DownCast(
          spaces[0]->GetImageHeader().GetImageRoot(ImageHeader::kClassRoots)));
  DCHECK_EQ(GetClassRoot<mirror::Class>(this)->GetClassFlags(), mirror::kClassFlagClass);

  ObjPtr<mirror::Class> java_lang_Object = GetClassRoot<mirror::Object>(this);
  java_lang_Object->SetObjectSize(sizeof(mirror::Object));
  // Allocate in non-movable so that it's possible to check if a JNI weak global ref has been
  // cleared without triggering the read barrier and unintentionally mark the sentinel alive.
  runtime->SetSentinel(heap->AllocNonMovableObject<true>(
      self, java_lang_Object, java_lang_Object->GetObjectSize(), VoidFunctor()));

  const std::vector<std::string>& boot_class_path_locations = runtime->GetBootClassPathLocations();
  CHECK_LE(spaces.size(), boot_class_path_locations.size());
  for (size_t i = 0u, size = spaces.size(); i != size; ++i) {
    // Boot class loader, use a null handle.
    std::vector<std::unique_ptr<const DexFile>> dex_files;
    if (!AddImageSpace(spaces[i],
                       ScopedNullHandle<mirror::ClassLoader>(),
                       /*dex_elements=*/ nullptr,
                       /*dex_location=*/ boot_class_path_locations[i].c_str(),
                       /*out*/&dex_files,
                       error_msg)) {
      return false;
    }
    // Assert that if absolute boot classpath locations were provided, they were
    // assigned to the loaded dex files.
    if (kIsDebugBuild && IsAbsoluteLocation(boot_class_path_locations[i])) {
      for (const auto& dex_file : dex_files) {
        DCHECK_EQ(DexFileLoader::GetBaseLocation(dex_file->GetLocation()),
                  boot_class_path_locations[i]);
      }
    }
    // Append opened dex files at the end.
    boot_dex_files_.insert(boot_dex_files_.end(),
                           std::make_move_iterator(dex_files.begin()),
                           std::make_move_iterator(dex_files.end()));
  }
  for (const std::unique_ptr<const DexFile>& dex_file : boot_dex_files_) {
    OatDexFile::MadviseDexFile(*dex_file, MadviseState::kMadviseStateAtLoad);
  }
  FinishInit(self);

  VLOG(startup) << __FUNCTION__ << " exiting";
  return true;
}

void ClassLinker::AddExtraBootDexFiles(
    Thread* self,
    std::vector<std::unique_ptr<const DexFile>>&& additional_dex_files) {
  for (std::unique_ptr<const DexFile>& dex_file : additional_dex_files) {
    AppendToBootClassPath(self, *dex_file);
    boot_dex_files_.push_back(std::move(dex_file));
  }
}

bool ClassLinker::IsBootClassLoader(ScopedObjectAccessAlreadyRunnable& soa,
                                    ObjPtr<mirror::ClassLoader> class_loader) {
  return class_loader == nullptr ||
       soa.Decode<mirror::Class>(WellKnownClasses::java_lang_BootClassLoader) ==
           class_loader->GetClass();
}

static bool GetDexPathListElementName(ObjPtr<mirror::Object> element,
                                      ObjPtr<mirror::String>* out_name)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  ArtField* const dex_file_field =
      jni::DecodeArtField(WellKnownClasses::dalvik_system_DexPathList__Element_dexFile);
  ArtField* const dex_file_name_field =
      jni::DecodeArtField(WellKnownClasses::dalvik_system_DexFile_fileName);
  DCHECK(dex_file_field != nullptr);
  DCHECK(dex_file_name_field != nullptr);
  DCHECK(element != nullptr);
  CHECK_EQ(dex_file_field->GetDeclaringClass(), element->GetClass()) << element->PrettyTypeOf();
  ObjPtr<mirror::Object> dex_file = dex_file_field->GetObject(element);
  if (dex_file == nullptr) {
    // Null dex file means it was probably a jar with no dex files, return a null string.
    *out_name = nullptr;
    return true;
  }
  ObjPtr<mirror::Object> name_object = dex_file_name_field->GetObject(dex_file);
  if (name_object != nullptr) {
    *out_name = name_object->AsString();
    return true;
  }
  return false;
}

static bool GetDexFileNames(ScopedObjectAccessUnchecked& soa,
                            ObjPtr<mirror::ClassLoader> class_loader,
                            /*out*/std::list<ObjPtr<mirror::String>>* dex_files,
                            /*out*/std::string* error_msg)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  StackHandleScope<1> hs(soa.Self());
  Handle<mirror::ClassLoader> handle(hs.NewHandle(class_loader));
  // Get element names. Sets error to true on failure.
  auto add_element_names = [&](ObjPtr<mirror::Object> element, bool* error)
      REQUIRES_SHARED(Locks::mutator_lock_) {
    if (element == nullptr) {
      *error_msg = "Null dex element";
      *error = true;  // Null element is a critical error.
      return false;   // Had an error, stop the visit.
    }
    ObjPtr<mirror::String> name;
    if (!GetDexPathListElementName(element, &name)) {
      *error_msg = "Invalid dex path list element";
      *error = true;   // Invalid element, make it a critical error.
      return false;    // Stop the visit.
    }
    if (name != nullptr) {
      dex_files->push_front(name);
    }
    return true;  // Continue with the next Element.
  };
  bool error = VisitClassLoaderDexElements(soa,
                                           handle,
                                           add_element_names,
                                           /*defaultReturn=*/ false);
  return !error;
}

static bool CompareClassLoaderTypes(ScopedObjectAccessUnchecked& soa,
                                    ObjPtr<mirror::ClassLoader> image_class_loader,
                                    ObjPtr<mirror::ClassLoader> class_loader,
                                    std::string* error_msg)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  if (ClassLinker::IsBootClassLoader(soa, class_loader)) {
    if (!ClassLinker::IsBootClassLoader(soa, image_class_loader)) {
      *error_msg = "Hierarchies don't match";
      return false;
    }
  } else if (ClassLinker::IsBootClassLoader(soa, image_class_loader)) {
    *error_msg = "Hierarchies don't match";
    return false;
  } else if (class_loader->GetClass() != image_class_loader->GetClass()) {
    *error_msg = StringPrintf("Class loader types don't match %s and %s",
                              image_class_loader->PrettyTypeOf().c_str(),
                              class_loader->PrettyTypeOf().c_str());
    return false;
  } else if (soa.Decode<mirror::Class>(WellKnownClasses::dalvik_system_PathClassLoader) !=
      class_loader->GetClass()) {
    *error_msg = StringPrintf("Unknown class loader type %s",
                              class_loader->PrettyTypeOf().c_str());
    // Unsupported class loader.
    return false;
  }
  return true;
}

static bool CompareDexFiles(const std::list<ObjPtr<mirror::String>>& image_dex_files,
                            const std::list<ObjPtr<mirror::String>>& loader_dex_files,
                            std::string* error_msg)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  bool equal = (image_dex_files.size() == loader_dex_files.size()) &&
      std::equal(image_dex_files.begin(),
                 image_dex_files.end(),
                 loader_dex_files.begin(),
                 [](ObjPtr<mirror::String> lhs, ObjPtr<mirror::String> rhs)
                     REQUIRES_SHARED(Locks::mutator_lock_) {
                   return lhs->Equals(rhs);
                 });
  if (!equal) {
    VLOG(image) << "Image dex files " << image_dex_files.size();
    for (ObjPtr<mirror::String> name : image_dex_files) {
      VLOG(image) << name->ToModifiedUtf8();
    }
    VLOG(image) << "Loader dex files " << loader_dex_files.size();
    for (ObjPtr<mirror::String> name : loader_dex_files) {
      VLOG(image) << name->ToModifiedUtf8();
    }
    *error_msg = "Mismatch in dex files";
  }
  return equal;
}

static bool CompareClassLoaders(ScopedObjectAccessUnchecked& soa,
                                ObjPtr<mirror::ClassLoader> image_class_loader,
                                ObjPtr<mirror::ClassLoader> class_loader,
                                bool check_dex_file_names,
                                std::string* error_msg)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  if (!CompareClassLoaderTypes(soa, image_class_loader, class_loader, error_msg)) {
    return false;
  }

  if (ClassLinker::IsBootClassLoader(soa, class_loader)) {
    // No need to check further.
    return true;
  }

  if (check_dex_file_names) {
    std::list<ObjPtr<mirror::String>> image_dex_files;
    if (!GetDexFileNames(soa, image_class_loader, &image_dex_files, error_msg)) {
      return false;
    }

    std::list<ObjPtr<mirror::String>> loader_dex_files;
    if (!GetDexFileNames(soa, class_loader, &loader_dex_files, error_msg)) {
      return false;
    }

    if (!CompareDexFiles(image_dex_files, loader_dex_files, error_msg)) {
      return false;
    }
  }

  ArtField* field =
      jni::DecodeArtField(WellKnownClasses::dalvik_system_BaseDexClassLoader_sharedLibraryLoaders);
  ObjPtr<mirror::Object> shared_libraries_image_loader = field->GetObject(image_class_loader.Ptr());
  ObjPtr<mirror::Object> shared_libraries_loader = field->GetObject(class_loader.Ptr());
  if (shared_libraries_image_loader == nullptr) {
    if (shared_libraries_loader != nullptr) {
      *error_msg = "Mismatch in shared libraries";
      return false;
    }
  } else if (shared_libraries_loader == nullptr) {
    *error_msg = "Mismatch in shared libraries";
    return false;
  } else {
    ObjPtr<mirror::ObjectArray<mirror::ClassLoader>> array1 =
        shared_libraries_image_loader->AsObjectArray<mirror::ClassLoader>();
    ObjPtr<mirror::ObjectArray<mirror::ClassLoader>> array2 =
        shared_libraries_loader->AsObjectArray<mirror::ClassLoader>();
    if (array1->GetLength() != array2->GetLength()) {
      *error_msg = "Mismatch in number of shared libraries";
      return false;
    }

    for (int32_t i = 0; i < array1->GetLength(); ++i) {
      // Do a full comparison of the class loaders, including comparing their dex files.
      if (!CompareClassLoaders(soa,
                               array1->Get(i),
                               array2->Get(i),
                               /*check_dex_file_names=*/ true,
                               error_msg)) {
        return false;
      }
    }
  }

  // Do a full comparison of the class loaders, including comparing their dex files.
  if (!CompareClassLoaders(soa,
                           image_class_loader->GetParent(),
                           class_loader->GetParent(),
                           /*check_dex_file_names=*/ true,
                           error_msg)) {
    return false;
  }
  return true;
}

class CHAOnDeleteUpdateClassVisitor {
 public:
  explicit CHAOnDeleteUpdateClassVisitor(LinearAlloc* alloc)
      : allocator_(alloc), cha_(Runtime::Current()->GetClassLinker()->GetClassHierarchyAnalysis()),
        pointer_size_(Runtime::Current()->GetClassLinker()->GetImagePointerSize()),
        self_(Thread::Current()) {}

  bool operator()(ObjPtr<mirror::Class> klass) REQUIRES_SHARED(Locks::mutator_lock_) {
    // This class is going to be unloaded. Tell CHA about it.
    cha_->ResetSingleImplementationInHierarchy(klass, allocator_, pointer_size_);
    return true;
  }
 private:
  const LinearAlloc* allocator_;
  const ClassHierarchyAnalysis* cha_;
  const PointerSize pointer_size_;
  const Thread* self_;
};

/*
 * A class used to ensure that all strings in an AppImage have been properly
 * interned, and is only ever run in debug mode.
 */
class VerifyStringInterningVisitor {
 public:
  explicit VerifyStringInterningVisitor(const gc::space::ImageSpace& space) :
      space_(space),
      intern_table_(*Runtime::Current()->GetInternTable()) {}

  void TestObject(ObjPtr<mirror::Object> referred_obj) const
      REQUIRES_SHARED(Locks::mutator_lock_) {
    if (referred_obj != nullptr &&
        space_.HasAddress(referred_obj.Ptr()) &&
        referred_obj->IsString()) {
      ObjPtr<mirror::String> referred_str = referred_obj->AsString();

      if (kIsDebugBuild) {
        // Saved to temporary variables to aid in debugging.
        ObjPtr<mirror::String> strong_lookup_result =
            intern_table_.LookupStrong(Thread::Current(), referred_str);
        ObjPtr<mirror::String> weak_lookup_result =
            intern_table_.LookupWeak(Thread::Current(), referred_str);

        DCHECK((strong_lookup_result == referred_str) || (weak_lookup_result == referred_str));
      }
    }
  }

  void VisitRootIfNonNull(
      mirror::CompressedReference<mirror::Object>* root) const
      REQUIRES_SHARED(Locks::mutator_lock_) {
    if (!root->IsNull()) {
      VisitRoot(root);
    }
  }

  void VisitRoot(mirror::CompressedReference<mirror::Object>* root) const
      REQUIRES_SHARED(Locks::mutator_lock_) {
    TestObject(root->AsMirrorPtr());
  }

  // Visit Class Fields
  void operator()(ObjPtr<mirror::Object> obj,
                  MemberOffset offset,
                  bool is_static ATTRIBUTE_UNUSED) const
      REQUIRES_SHARED(Locks::mutator_lock_) {
    // There could be overlap between ranges, we must avoid visiting the same reference twice.
    // Avoid the class field since we already fixed it up in FixupClassVisitor.
    if (offset.Uint32Value() != mirror::Object::ClassOffset().Uint32Value()) {
      // Updating images, don't do a read barrier.
      ObjPtr<mirror::Object> referred_obj =
          obj->GetFieldObject<mirror::Object, kVerifyNone, kWithoutReadBarrier>(offset);

      TestObject(referred_obj);
    }
  }

  void operator()(ObjPtr<mirror::Class> klass ATTRIBUTE_UNUSED,
                  ObjPtr<mirror::Reference> ref) const
      REQUIRES_SHARED(Locks::mutator_lock_) REQUIRES(Locks::heap_bitmap_lock_) {
    operator()(ref, mirror::Reference::ReferentOffset(), false);
  }

  const gc::space::ImageSpace& space_;
  InternTable& intern_table_;
};

/*
 * This function verifies that string references in the AppImage have been
 * properly interned.  To be considered properly interned a reference must
 * point to the same version of the string that the intern table does.
 */
void VerifyStringInterning(gc::space::ImageSpace& space) REQUIRES_SHARED(Locks::mutator_lock_) {
  const gc::accounting::ContinuousSpaceBitmap* bitmap = space.GetMarkBitmap();
  const ImageHeader& image_header = space.GetImageHeader();
  const uint8_t* target_base = space.GetMemMap()->Begin();
  const ImageSection& objects_section = image_header.GetObjectsSection();

  auto objects_begin = reinterpret_cast<uintptr_t>(target_base + objects_section.Offset());
  auto objects_end = reinterpret_cast<uintptr_t>(target_base + objects_section.End());

  VerifyStringInterningVisitor visitor(space);
  bitmap->VisitMarkedRange(objects_begin,
                           objects_end,
                           [&space, &visitor](mirror::Object* obj)
    REQUIRES_SHARED(Locks::mutator_lock_) {
    if (space.HasAddress(obj)) {
      if (obj->IsDexCache()) {
        obj->VisitReferences</* kVisitNativeRoots= */ true,
                             kVerifyNone,
                             kWithoutReadBarrier>(visitor, visitor);
      } else {
        // Don't visit native roots for non-dex-cache as they can't contain
        // native references to strings.  This is verified during compilation
        // by ImageWriter::VerifyNativeGCRootInvariants.
        obj->VisitReferences</* kVisitNativeRoots= */ false,
                             kVerifyNone,
                             kWithoutReadBarrier>(visitor, visitor);
      }
    }
  });
}

// new_class_set is the set of classes that were read from the class table section in the image.
// If there was no class table section, it is null.
// Note: using a class here to avoid having to make ClassLinker internals public.
class AppImageLoadingHelper {
 public:
  static void Update(
      ClassLinker* class_linker,
      gc::space::ImageSpace* space,
      Handle<mirror::ClassLoader> class_loader,
      Handle<mirror::ObjectArray<mirror::DexCache>> dex_caches,
      ClassTable::ClassSet* new_class_set)
      REQUIRES(!Locks::dex_lock_)
      REQUIRES_SHARED(Locks::mutator_lock_);

  static void HandleAppImageStrings(gc::space::ImageSpace* space)
      REQUIRES_SHARED(Locks::mutator_lock_);

  static void UpdateInternStrings(
      gc::space::ImageSpace* space,
      bool use_preresolved_strings,
      const SafeMap<mirror::String*, mirror::String*>& intern_remap)
      REQUIRES_SHARED(Locks::mutator_lock_);
};

void AppImageLoadingHelper::Update(
    ClassLinker* class_linker,
    gc::space::ImageSpace* space,
    Handle<mirror::ClassLoader> class_loader,
    Handle<mirror::ObjectArray<mirror::DexCache>> dex_caches,
    ClassTable::ClassSet* new_class_set)
    REQUIRES(!Locks::dex_lock_)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  ScopedTrace app_image_timing("AppImage:Updating");

  Thread* const self = Thread::Current();
  Runtime* const runtime = Runtime::Current();
  gc::Heap* const heap = runtime->GetHeap();
  const ImageHeader& header = space->GetImageHeader();
  bool load_app_image_startup_cache = runtime->LoadAppImageStartupCache();
  {
    // Register dex caches with the class loader.
    WriterMutexLock mu(self, *Locks::classlinker_classes_lock_);
    const size_t num_dex_caches = dex_caches->GetLength();
    for (size_t i = 0; i < num_dex_caches; i++) {
      ObjPtr<mirror::DexCache> dex_cache = dex_caches->Get(i);
      const DexFile* const dex_file = dex_cache->GetDexFile();
      {
        WriterMutexLock mu2(self, *Locks::dex_lock_);
        CHECK(!class_linker->FindDexCacheDataLocked(*dex_file).IsValid());
        class_linker->RegisterDexFileLocked(*dex_file, dex_cache, class_loader.Get());
      }

      if (!load_app_image_startup_cache) {
        dex_cache->ClearPreResolvedStrings();
      }

      if (kIsDebugBuild) {
        CHECK(new_class_set != nullptr);
        mirror::TypeDexCacheType* const types = dex_cache->GetResolvedTypes();
        const size_t num_types = dex_cache->NumResolvedTypes();
        for (size_t j = 0; j != num_types; ++j) {
          // The image space is not yet added to the heap, avoid read barriers.
          ObjPtr<mirror::Class> klass = types[j].load(std::memory_order_relaxed).object.Read();

          if (space->HasAddress(klass.Ptr())) {
            DCHECK(!klass->IsErroneous()) << klass->GetStatus();
            auto it = new_class_set->find(ClassTable::TableSlot(klass));
            DCHECK(it != new_class_set->end());
            DCHECK_EQ(it->Read(), klass);
            ObjPtr<mirror::Class> super_class = klass->GetSuperClass();

            if (super_class != nullptr && !heap->ObjectIsInBootImageSpace(super_class)) {
              auto it2 = new_class_set->find(ClassTable::TableSlot(super_class));
              DCHECK(it2 != new_class_set->end());
              DCHECK_EQ(it2->Read(), super_class);
            }

            for (ArtMethod& m : klass->GetDirectMethods(kRuntimePointerSize)) {
              const void* code = m.GetEntryPointFromQuickCompiledCode();
              const void* oat_code = m.IsInvokable() ? class_linker->GetQuickOatCodeFor(&m) : code;
              if (!class_linker->IsQuickResolutionStub(code) &&
                  !class_linker->IsQuickGenericJniStub(code) &&
                  !class_linker->IsQuickToInterpreterBridge(code) &&
                  !m.IsNative()) {
                DCHECK_EQ(code, oat_code) << m.PrettyMethod();
              }
            }

            for (ArtMethod& m : klass->GetVirtualMethods(kRuntimePointerSize)) {
              const void* code = m.GetEntryPointFromQuickCompiledCode();
              const void* oat_code = m.IsInvokable() ? class_linker->GetQuickOatCodeFor(&m) : code;
              if (!class_linker->IsQuickResolutionStub(code) &&
                  !class_linker->IsQuickGenericJniStub(code) &&
                  !class_linker->IsQuickToInterpreterBridge(code) &&
                  !m.IsNative()) {
                DCHECK_EQ(code, oat_code) << m.PrettyMethod();
              }
            }
          }
        }
      }
    }
  }

  if (ClassLinker::kAppImageMayContainStrings) {
    HandleAppImageStrings(space);

    if (kIsDebugBuild) {
      VerifyStringInterning(*space);
    }
  }

  if (kVerifyArtMethodDeclaringClasses) {
    ScopedTrace timing("AppImage:VerifyDeclaringClasses");
    ReaderMutexLock rmu(self, *Locks::heap_bitmap_lock_);
    gc::accounting::HeapBitmap* live_bitmap = heap->GetLiveBitmap();
    header.VisitPackedArtMethods([&](ArtMethod& method)
        REQUIRES_SHARED(Locks::mutator_lock_, Locks::heap_bitmap_lock_) {
      ObjPtr<mirror::Class> klass = method.GetDeclaringClassUnchecked();
      if (klass != nullptr) {
        CHECK(live_bitmap->Test(klass.Ptr())) << "Image method has unmarked declaring class";
      }
    }, space->Begin(), kRuntimePointerSize);
  }
}

void AppImageLoadingHelper::UpdateInternStrings(
    gc::space::ImageSpace* space,
    bool use_preresolved_strings,
    const SafeMap<mirror::String*, mirror::String*>& intern_remap) {
  const uint8_t* target_base = space->Begin();
  const ImageSection& sro_section =
      space->GetImageHeader().GetImageStringReferenceOffsetsSection();
  const size_t num_string_offsets = sro_section.Size() / sizeof(AppImageReferenceOffsetInfo);
  InternTable* const intern_table = Runtime::Current()->GetInternTable();

  VLOG(image)
      << "ClassLinker:AppImage:InternStrings:imageStringReferenceOffsetCount = "
      << num_string_offsets;

  const auto* sro_base =
      reinterpret_cast<const AppImageReferenceOffsetInfo*>(target_base + sro_section.Offset());

  for (size_t offset_index = 0; offset_index < num_string_offsets; ++offset_index) {
    uint32_t base_offset = sro_base[offset_index].first;

    if (HasDexCacheStringNativeRefTag(base_offset)) {
      base_offset = ClearDexCacheNativeRefTags(base_offset);
      DCHECK_ALIGNED(base_offset, 2);

      ObjPtr<mirror::DexCache> dex_cache =
          reinterpret_cast<mirror::DexCache*>(space->Begin() + base_offset);
      uint32_t string_index = sro_base[offset_index].second;

      mirror::StringDexCachePair source = dex_cache->GetStrings()[string_index].load();
      ObjPtr<mirror::String> referred_string = source.object.Read();
      DCHECK(referred_string != nullptr);

      auto it = intern_remap.find(referred_string.Ptr());
      if (it != intern_remap.end()) {
        // This doesn't use SetResolvedString to maintain consistency with how
        // we load the string.  The index from the source string must be
        // re-used due to the circular nature of the cache.  Because we are not
        // using a helper function we need to mark the GC card manually.
        WriteBarrier::ForEveryFieldWrite(dex_cache);
        dex_cache->GetStrings()[string_index].store(
            mirror::StringDexCachePair(it->second, source.index));
      } else if (!use_preresolved_strings) {
        dex_cache->GetStrings()[string_index].store(
            mirror::StringDexCachePair(intern_table->InternStrong(referred_string), source.index));
      }
    } else if (HasDexCachePreResolvedStringNativeRefTag(base_offset)) {
      if (use_preresolved_strings) {
        base_offset = ClearDexCacheNativeRefTags(base_offset);
        DCHECK_ALIGNED(base_offset, 2);

        ObjPtr<mirror::DexCache> dex_cache =
            reinterpret_cast<mirror::DexCache*>(space->Begin() + base_offset);
        uint32_t string_index = sro_base[offset_index].second;

        GcRoot<mirror::String>* preresolved_strings =
            dex_cache->GetPreResolvedStrings();
        // Handle calls to ClearPreResolvedStrings that might occur concurrently by the profile
        // saver that runs shortly after startup. In case the strings are cleared, there is nothing
        // to fix up.
        if (preresolved_strings == nullptr) {
          continue;
        }
        ObjPtr<mirror::String> referred_string =
            preresolved_strings[string_index].Read();
        if (referred_string == nullptr) {
          continue;
        }
        auto it = intern_remap.find(referred_string.Ptr());
        if (it != intern_remap.end()) {
          // Because we are not using a helper function we need to mark the GC card manually.
          WriteBarrier::ForEveryFieldWrite(dex_cache);
          dex_cache->GetPreResolvedStrings()[string_index] = GcRoot<mirror::String>(it->second);
        }
      }
    } else {
      uint32_t raw_member_offset = sro_base[offset_index].second;
      DCHECK_ALIGNED(base_offset, 2);
      DCHECK_ALIGNED(raw_member_offset, 2);

      ObjPtr<mirror::Object> obj_ptr =
          reinterpret_cast<mirror::Object*>(space->Begin() + base_offset);
      MemberOffset member_offset(raw_member_offset);
      ObjPtr<mirror::String> referred_string =
          obj_ptr->GetFieldObject<mirror::String,
                                  kVerifyNone,
                                  kWithoutReadBarrier,
                                  /* kIsVolatile= */ false>(member_offset);
      DCHECK(referred_string != nullptr);

      auto it = intern_remap.find(referred_string.Ptr());
      if (it != intern_remap.end()) {
        obj_ptr->SetFieldObject</* kTransactionActive= */ false,
                                /* kCheckTransaction= */ false,
                                kVerifyNone,
                                /* kIsVolatile= */ false>(member_offset, it->second);
      } else if (!use_preresolved_strings) {
        obj_ptr->SetFieldObject</* kTransactionActive= */ false,
                                /* kCheckTransaction= */ false,
                                kVerifyNone,
                                /* kIsVolatile= */ false>(
            member_offset,
            intern_table->InternStrong(referred_string));
      }
    }
  }
}

void AppImageLoadingHelper::HandleAppImageStrings(gc::space::ImageSpace* space) {
  // Iterate over the string reference offsets stored in the image and intern
  // the strings they point to.
  ScopedTrace timing("AppImage:InternString");

  Runtime* const runtime = Runtime::Current();
  InternTable* const intern_table = runtime->GetInternTable();

  const bool load_startup_cache = runtime->LoadAppImageStartupCache();

  // Add the intern table, removing any conflicts. For conflicts, store the new address in a map
  // for faster lookup.
  // TODO: Optimize with a bitmap or bloom filter
  SafeMap<mirror::String*, mirror::String*> intern_remap;
  auto func = [&](InternTable::UnorderedSet& interns)
      REQUIRES_SHARED(Locks::mutator_lock_)
      REQUIRES(Locks::intern_table_lock_) {
    const size_t non_boot_image_strings = intern_table->CountInterns(
        /*visit_boot_images=*/false,
        /*visit_non_boot_images=*/true);
    VLOG(image) << "AppImage:stringsInInternTableSize = " << interns.size();
    VLOG(image) << "AppImage:nonBootImageInternStrings = " << non_boot_image_strings;
    // Visit the smaller of the two sets to compute the intersection.
    if (interns.size() < non_boot_image_strings) {
      for (auto it = interns.begin(); it != interns.end(); ) {
        ObjPtr<mirror::String> string = it->Read();
        ObjPtr<mirror::String> existing = intern_table->LookupWeakLocked(string);
        if (existing == nullptr) {
          existing = intern_table->LookupStrongLocked(string);
        }
        if (existing != nullptr) {
          intern_remap.Put(string.Ptr(), existing.Ptr());
          it = interns.erase(it);
        } else {
          ++it;
        }
      }
    } else {
      intern_table->VisitInterns([&](const GcRoot<mirror::String>& root)
          REQUIRES_SHARED(Locks::mutator_lock_)
          REQUIRES(Locks::intern_table_lock_) {
        auto it = interns.find(root);
        if (it != interns.end()) {
          ObjPtr<mirror::String> existing = root.Read();
          intern_remap.Put(it->Read(), existing.Ptr());
          it = interns.erase(it);
        }
      }, /*visit_boot_images=*/false, /*visit_non_boot_images=*/true);
    }
    // Sanity check to ensure correctness.
    if (kIsDebugBuild) {
      for (GcRoot<mirror::String>& root : interns) {
        ObjPtr<mirror::String> string = root.Read();
        CHECK(intern_table->LookupWeakLocked(string) == nullptr) << string->ToModifiedUtf8();
        CHECK(intern_table->LookupStrongLocked(string) == nullptr) << string->ToModifiedUtf8();
      }
    }
  };

  bool update_intern_strings;
  if (load_startup_cache) {
    VLOG(image) << "AppImage:load_startup_cache";
    // Only add the intern table if we are using the startup cache. Otherwise,
    // UpdateInternStrings adds the strings to the intern table.
    intern_table->AddImageStringsToTable(space, func);
    update_intern_strings = kIsDebugBuild || !intern_remap.empty();
    VLOG(image) << "AppImage:conflictingInternStrings = " << intern_remap.size();
  } else {
    update_intern_strings = true;
  }

  // For debug builds, always run the code below to get coverage.
  if (update_intern_strings) {
    // Slow path case is when there are conflicting intern strings to fix up.
    UpdateInternStrings(space, /*use_preresolved_strings=*/ load_startup_cache, intern_remap);
  }
}

static std::unique_ptr<const DexFile> OpenOatDexFile(const OatFile* oat_file,
                                                     const char* location,
                                                     std::string* error_msg)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  DCHECK(error_msg != nullptr);
  std::unique_ptr<const DexFile> dex_file;
  const OatDexFile* oat_dex_file = oat_file->GetOatDexFile(location, nullptr, error_msg);
  if (oat_dex_file == nullptr) {
    return std::unique_ptr<const DexFile>();
  }
  std::string inner_error_msg;
  dex_file = oat_dex_file->OpenDexFile(&inner_error_msg);
  if (dex_file == nullptr) {
    *error_msg = StringPrintf("Failed to open dex file %s from within oat file %s error '%s'",
                              location,
                              oat_file->GetLocation().c_str(),
                              inner_error_msg.c_str());
    return std::unique_ptr<const DexFile>();
  }

  if (dex_file->GetLocationChecksum() != oat_dex_file->GetDexFileLocationChecksum()) {
    *error_msg = StringPrintf("Checksums do not match for %s: %x vs %x",
                              location,
                              dex_file->GetLocationChecksum(),
                              oat_dex_file->GetDexFileLocationChecksum());
    return std::unique_ptr<const DexFile>();
  }
  return dex_file;
}

bool ClassLinker::OpenImageDexFiles(gc::space::ImageSpace* space,
                                    std::vector<std::unique_ptr<const DexFile>>* out_dex_files,
                                    std::string* error_msg) {
  ScopedAssertNoThreadSuspension nts(__FUNCTION__);
  const ImageHeader& header = space->GetImageHeader();
  ObjPtr<mirror::Object> dex_caches_object = header.GetImageRoot(ImageHeader::kDexCaches);
  DCHECK(dex_caches_object != nullptr);
  ObjPtr<mirror::ObjectArray<mirror::DexCache>> dex_caches =
      dex_caches_object->AsObjectArray<mirror::DexCache>();
  const OatFile* oat_file = space->GetOatFile();
  for (int32_t i = 0, length = dex_caches->GetLength(); i != length; ++i) {
    ObjPtr<mirror::DexCache> dex_cache = dex_caches->Get(i);
    std::string dex_file_location(dex_cache->GetLocation()->ToModifiedUtf8());
    std::unique_ptr<const DexFile> dex_file = OpenOatDexFile(oat_file,
                                                             dex_file_location.c_str(),
                                                             error_msg);
    if (dex_file == nullptr) {
      return false;
    }
    dex_cache->SetDexFile(dex_file.get());
    out_dex_files->push_back(std::move(dex_file));
  }
  return true;
}

// Helper class for ArtMethod checks when adding an image. Keeps all required functionality
// together and caches some intermediate results.
class ImageSanityChecks final {
 public:
  static void CheckObjects(gc::Heap* heap, ClassLinker* class_linker)
      REQUIRES_SHARED(Locks::mutator_lock_) {
    ImageSanityChecks isc(heap, class_linker);
    auto visitor = [&](mirror::Object* obj) REQUIRES_SHARED(Locks::mutator_lock_) {
      DCHECK(obj != nullptr);
      CHECK(obj->GetClass() != nullptr) << "Null class in object " << obj;
      CHECK(obj->GetClass()->GetClass() != nullptr) << "Null class class " << obj;
      if (obj->IsClass()) {
        auto klass = obj->AsClass();
        for (ArtField& field : klass->GetIFields()) {
          CHECK_EQ(field.GetDeclaringClass(), klass);
        }
        for (ArtField& field : klass->GetSFields()) {
          CHECK_EQ(field.GetDeclaringClass(), klass);
        }
        const PointerSize pointer_size = isc.pointer_size_;
        for (ArtMethod& m : klass->GetMethods(pointer_size)) {
          isc.SanityCheckArtMethod(&m, klass);
        }
        ObjPtr<mirror::PointerArray> vtable = klass->GetVTable();
        if (vtable != nullptr) {
          isc.SanityCheckArtMethodPointerArray(vtable, nullptr);
        }
        if (klass->ShouldHaveImt()) {
          ImTable* imt = klass->GetImt(pointer_size);
          for (size_t i = 0; i < ImTable::kSize; ++i) {
            isc.SanityCheckArtMethod(imt->Get(i, pointer_size), nullptr);
          }
        }
        if (klass->ShouldHaveEmbeddedVTable()) {
          for (int32_t i = 0; i < klass->GetEmbeddedVTableLength(); ++i) {
            isc.SanityCheckArtMethod(klass->GetEmbeddedVTableEntry(i, pointer_size), nullptr);
          }
        }
        ObjPtr<mirror::IfTable> iftable = klass->GetIfTable();
        for (int32_t i = 0; i < klass->GetIfTableCount(); ++i) {
          if (iftable->GetMethodArrayCount(i) > 0) {
            isc.SanityCheckArtMethodPointerArray(iftable->GetMethodArray(i), nullptr);
          }
        }
      }
    };
    heap->VisitObjects(visitor);
  }

  static void CheckArtMethodDexCacheArray(gc::Heap* heap,
                                          ClassLinker* class_linker,
                                          mirror::MethodDexCacheType* arr,
                                          size_t size)
      REQUIRES_SHARED(Locks::mutator_lock_) {
    ImageSanityChecks isc(heap, class_linker);
    isc.SanityCheckArtMethodDexCacheArray(arr, size);
  }

 private:
  ImageSanityChecks(gc::Heap* heap, ClassLinker* class_linker)
     :  spaces_(heap->GetBootImageSpaces()),
        pointer_size_(class_linker->GetImagePointerSize()) {
    space_begin_.reserve(spaces_.size());
    method_sections_.reserve(spaces_.size());
    runtime_method_sections_.reserve(spaces_.size());
    for (gc::space::ImageSpace* space : spaces_) {
      space_begin_.push_back(space->Begin());
      auto& header = space->GetImageHeader();
      method_sections_.push_back(&header.GetMethodsSection());
      runtime_method_sections_.push_back(&header.GetRuntimeMethodsSection());
    }
  }

  void SanityCheckArtMethod(ArtMethod* m, ObjPtr<mirror::Class> expected_class)
      REQUIRES_SHARED(Locks::mutator_lock_) {
    if (m->IsRuntimeMethod()) {
      ObjPtr<mirror::Class> declaring_class = m->GetDeclaringClassUnchecked();
      CHECK(declaring_class == nullptr) << declaring_class << " " << m->PrettyMethod();
    } else if (m->IsCopied()) {
      CHECK(m->GetDeclaringClass() != nullptr) << m->PrettyMethod();
    } else if (expected_class != nullptr) {
      CHECK_EQ(m->GetDeclaringClassUnchecked(), expected_class) << m->PrettyMethod();
    }
    if (!spaces_.empty()) {
      bool contains = false;
      for (size_t i = 0; !contains && i != space_begin_.size(); ++i) {
        const size_t offset = reinterpret_cast<uint8_t*>(m) - space_begin_[i];
        contains = method_sections_[i]->Contains(offset) ||
            runtime_method_sections_[i]->Contains(offset);
      }
      CHECK(contains) << m << " not found";
    }
  }

  void SanityCheckArtMethodPointerArray(ObjPtr<mirror::PointerArray> arr,
                                        ObjPtr<mirror::Class> expected_class)
      REQUIRES_SHARED(Locks::mutator_lock_) {
    CHECK(arr != nullptr);
    for (int32_t j = 0; j < arr->GetLength(); ++j) {
      auto* method = arr->GetElementPtrSize<ArtMethod*>(j, pointer_size_);
      // expected_class == null means we are a dex cache.
      if (expected_class != nullptr) {
        CHECK(method != nullptr);
      }
      if (method != nullptr) {
        SanityCheckArtMethod(method, expected_class);
      }
    }
  }

  void SanityCheckArtMethodDexCacheArray(mirror::MethodDexCacheType* arr, size_t size)
      REQUIRES_SHARED(Locks::mutator_lock_) {
    CHECK_EQ(arr != nullptr, size != 0u);
    if (arr != nullptr) {
      bool contains = false;
      for (auto space : spaces_) {
        auto offset = reinterpret_cast<uint8_t*>(arr) - space->Begin();
        if (space->GetImageHeader().GetDexCacheArraysSection().Contains(offset)) {
          contains = true;
          break;
        }
      }
      CHECK(contains);
    }
    for (size_t j = 0; j < size; ++j) {
      auto pair = mirror::DexCache::GetNativePairPtrSize(arr, j, pointer_size_);
      ArtMethod* method = pair.object;
      // expected_class == null means we are a dex cache.
      if (method != nullptr) {
        SanityCheckArtMethod(method, nullptr);
      }
    }
  }

  const std::vector<gc::space::ImageSpace*>& spaces_;
  const PointerSize pointer_size_;

  // Cached sections from the spaces.
  std::vector<const uint8_t*> space_begin_;
  std::vector<const ImageSection*> method_sections_;
  std::vector<const ImageSection*> runtime_method_sections_;
};

static void VerifyAppImage(const ImageHeader& header,
                           const Handle<mirror::ClassLoader>& class_loader,
                           const Handle<mirror::ObjectArray<mirror::DexCache> >& dex_caches,
                           ClassTable* class_table, gc::space::ImageSpace* space)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  header.VisitPackedArtMethods([&](ArtMethod& method) REQUIRES_SHARED(Locks::mutator_lock_) {
    ObjPtr<mirror::Class> klass = method.GetDeclaringClass();
    if (klass != nullptr && !Runtime::Current()->GetHeap()->ObjectIsInBootImageSpace(klass)) {
      CHECK_EQ(class_table->LookupByDescriptor(klass), klass)
          << mirror::Class::PrettyClass(klass);
    }
  }, space->Begin(), kRuntimePointerSize);
  {
    // Verify that all direct interfaces of classes in the class table are also resolved.
    std::vector<ObjPtr<mirror::Class>> classes;
    auto verify_direct_interfaces_in_table = [&](ObjPtr<mirror::Class> klass)
        REQUIRES_SHARED(Locks::mutator_lock_) {
      if (!klass->IsPrimitive() && klass->GetClassLoader() == class_loader.Get()) {
        classes.push_back(klass);
      }
      return true;
    };
    class_table->Visit(verify_direct_interfaces_in_table);
    Thread* self = Thread::Current();
    for (ObjPtr<mirror::Class> klass : classes) {
      for (uint32_t i = 0, num = klass->NumDirectInterfaces(); i != num; ++i) {
        CHECK(klass->GetDirectInterface(self, klass, i) != nullptr)
            << klass->PrettyDescriptor() << " iface #" << i;
      }
    }
  }
  // Check that all non-primitive classes in dex caches are also in the class table.
  for (int32_t i = 0; i < dex_caches->GetLength(); i++) {
    ObjPtr<mirror::DexCache> dex_cache = dex_caches->Get(i);
    mirror::TypeDexCacheType* const types = dex_cache->GetResolvedTypes();
    for (int32_t j = 0, num_types = dex_cache->NumResolvedTypes(); j < num_types; j++) {
      ObjPtr<mirror::Class> klass = types[j].load(std::memory_order_relaxed).object.Read();
      if (klass != nullptr && !klass->IsPrimitive()) {
        CHECK(class_table->Contains(klass))
            << klass->PrettyDescriptor() << " " << dex_cache->GetDexFile()->GetLocation();
      }
    }
  }
}

bool ClassLinker::AddImageSpace(
    gc::space::ImageSpace* space,
    Handle<mirror::ClassLoader> class_loader,
    jobjectArray dex_elements,
    const char* dex_location,
    std::vector<std::unique_ptr<const DexFile>>* out_dex_files,
    std::string* error_msg) {
  DCHECK(out_dex_files != nullptr);
  DCHECK(error_msg != nullptr);
  const uint64_t start_time = NanoTime();
  const bool app_image = class_loader != nullptr;
  const ImageHeader& header = space->GetImageHeader();
  ObjPtr<mirror::Object> dex_caches_object = header.GetImageRoot(ImageHeader::kDexCaches);
  DCHECK(dex_caches_object != nullptr);
  Runtime* const runtime = Runtime::Current();
  gc::Heap* const heap = runtime->GetHeap();
  Thread* const self = Thread::Current();
  // Check that the image is what we are expecting.
  if (image_pointer_size_ != space->GetImageHeader().GetPointerSize()) {
    *error_msg = StringPrintf("Application image pointer size does not match runtime: %zu vs %zu",
                              static_cast<size_t>(space->GetImageHeader().GetPointerSize()),
                              image_pointer_size_);
    return false;
  }
  size_t expected_image_roots = ImageHeader::NumberOfImageRoots(app_image);
  if (static_cast<size_t>(header.GetImageRoots()->GetLength()) != expected_image_roots) {
    *error_msg = StringPrintf("Expected %zu image roots but got %d",
                              expected_image_roots,
                              header.GetImageRoots()->GetLength());
    return false;
  }
  StackHandleScope<3> hs(self);
  Handle<mirror::ObjectArray<mirror::DexCache>> dex_caches(
      hs.NewHandle(dex_caches_object->AsObjectArray<mirror::DexCache>()));
  Handle<mirror::ObjectArray<mirror::Class>> class_roots(hs.NewHandle(
      header.GetImageRoot(ImageHeader::kClassRoots)->AsObjectArray<mirror::Class>()));
  MutableHandle<mirror::ClassLoader> image_class_loader(hs.NewHandle(
      app_image ? header.GetImageRoot(ImageHeader::kAppImageClassLoader)->AsClassLoader()
                : nullptr));
  DCHECK(class_roots != nullptr);
  if (class_roots->GetLength() != static_cast<int32_t>(ClassRoot::kMax)) {
    *error_msg = StringPrintf("Expected %d class roots but got %d",
                              class_roots->GetLength(),
                              static_cast<int32_t>(ClassRoot::kMax));
    return false;
  }
  // Check against existing class roots to make sure they match the ones in the boot image.
  ObjPtr<mirror::ObjectArray<mirror::Class>> existing_class_roots = GetClassRoots();
  for (size_t i = 0; i < static_cast<size_t>(ClassRoot::kMax); i++) {
    if (class_roots->Get(i) != GetClassRoot(static_cast<ClassRoot>(i), existing_class_roots)) {
      *error_msg = "App image class roots must have pointer equality with runtime ones.";
      return false;
    }
  }
  const OatFile* oat_file = space->GetOatFile();
  if (oat_file->GetOatHeader().GetDexFileCount() !=
      static_cast<uint32_t>(dex_caches->GetLength())) {
    *error_msg = "Dex cache count and dex file count mismatch while trying to initialize from "
                 "image";
    return false;
  }

  for (int32_t i = 0; i < dex_caches->GetLength(); i++) {
    ObjPtr<mirror::DexCache> dex_cache = dex_caches->Get(i);
    std::string dex_file_location = dex_cache->GetLocation()->ToModifiedUtf8();
    if (class_loader == nullptr) {
      // For app images, we'll see the relative location. b/130666977.
      DCHECK_EQ(dex_location, DexFileLoader::GetBaseLocation(dex_file_location));
    }
    std::unique_ptr<const DexFile> dex_file = OpenOatDexFile(oat_file,
                                                             dex_file_location.c_str(),
                                                             error_msg);
    if (dex_file == nullptr) {
      return false;
    }

    if (app_image) {
      // The current dex file field is bogus, overwrite it so that we can get the dex file in the
      // loop below.
      dex_cache->SetDexFile(dex_file.get());
      mirror::TypeDexCacheType* const types = dex_cache->GetResolvedTypes();
      for (int32_t j = 0, num_types = dex_cache->NumResolvedTypes(); j < num_types; j++) {
        ObjPtr<mirror::Class> klass = types[j].load(std::memory_order_relaxed).object.Read();
        if (klass != nullptr) {
          DCHECK(!klass->IsErroneous()) << klass->GetStatus();
        }
      }
    } else {
      if (kSanityCheckObjects) {
        ImageSanityChecks::CheckArtMethodDexCacheArray(heap,
                                                       this,
                                                       dex_cache->GetResolvedMethods(),
                                                       dex_cache->NumResolvedMethods());
      }
      // Register dex files, keep track of existing ones that are conflicts.
      AppendToBootClassPath(*dex_file.get(), dex_cache);
    }
    out_dex_files->push_back(std::move(dex_file));
  }

  if (app_image) {
    ScopedObjectAccessUnchecked soa(Thread::Current());
    ScopedAssertNoThreadSuspension sants("Checking app image", soa.Self());
    // Check that the class loader resolves the same way as the ones in the image.
    // Image class loader [A][B][C][image dex files]
    // Class loader = [???][dex_elements][image dex files]
    // Need to ensure that [???][dex_elements] == [A][B][C].
    // For each class loader, PathClassLoader, the loader checks the parent first. Also the logic
    // for PathClassLoader does this by looping through the array of dex files. To ensure they
    // resolve the same way, simply flatten the hierarchy in the way the resolution order would be,
    // and check that the dex file names are the same.
    if (IsBootClassLoader(soa, image_class_loader.Get())) {
      *error_msg = "Unexpected BootClassLoader in app image";
      return false;
    }
    // The dex files of `class_loader` are not setup yet, so we cannot do a full comparison
    // of `class_loader` and `image_class_loader` in `CompareClassLoaders`. Therefore, we
    // special case the comparison of dex files of the two class loaders, but then do full
    // comparisons for their shared libraries and parent.
    auto elements = soa.Decode<mirror::ObjectArray<mirror::Object>>(dex_elements);
    std::list<ObjPtr<mirror::String>> loader_dex_file_names;
    for (size_t i = 0, num_elems = elements->GetLength(); i < num_elems; ++i) {
      ObjPtr<mirror::Object> element = elements->GetWithoutChecks(i);
      if (element != nullptr) {
        // If we are somewhere in the middle of the array, there may be nulls at the end.
        ObjPtr<mirror::String> name;
        if (GetDexPathListElementName(element, &name) && name != nullptr) {
          loader_dex_file_names.push_back(name);
        }
      }
    }
    std::string temp_error_msg;
    std::list<ObjPtr<mirror::String>> image_dex_file_names;
    bool success = GetDexFileNames(
        soa, image_class_loader.Get(), &image_dex_file_names, &temp_error_msg);
    if (success) {
      // Ignore the number of image dex files since we are adding those to the class loader anyways.
      CHECK_GE(static_cast<size_t>(image_dex_file_names.size()),
               static_cast<size_t>(dex_caches->GetLength()));
      size_t image_count = image_dex_file_names.size() - dex_caches->GetLength();
      image_dex_file_names.resize(image_count);
      success = success && CompareDexFiles(image_dex_file_names,
                                           loader_dex_file_names,
                                           &temp_error_msg);
      success = success && CompareClassLoaders(soa,
                                               image_class_loader.Get(),
                                               class_loader.Get(),
                                               /*check_dex_file_names=*/ false,
                                               &temp_error_msg);
    }
    if (!success) {
      *error_msg = StringPrintf("Rejecting application image due to class loader mismatch: '%s'",
                               temp_error_msg.c_str());
      return false;
    }
  }

  if (kSanityCheckObjects) {
    for (int32_t i = 0; i < dex_caches->GetLength(); i++) {
      ObjPtr<mirror::DexCache> dex_cache = dex_caches->Get(i);
      for (size_t j = 0; j < dex_cache->NumResolvedFields(); ++j) {
        auto* field = dex_cache->GetResolvedField(j, image_pointer_size_);
        if (field != nullptr) {
          CHECK(field->GetDeclaringClass()->GetClass() != nullptr);
        }
      }
    }
    if (!app_image) {
      ImageSanityChecks::CheckObjects(heap, this);
    }
  }

  // Set entry point to interpreter if in InterpretOnly mode.
  if (!runtime->IsAotCompiler() && runtime->GetInstrumentation()->InterpretOnly()) {
    // Set image methods' entry point to interpreter.
    header.VisitPackedArtMethods([&](ArtMethod& method) REQUIRES_SHARED(Locks::mutator_lock_) {
      if (!method.IsRuntimeMethod()) {
        DCHECK(method.GetDeclaringClass() != nullptr);
        if (!method.IsNative() && !method.IsResolutionMethod()) {
          method.SetEntryPointFromQuickCompiledCodePtrSize(GetQuickToInterpreterBridge(),
                                                            image_pointer_size_);
        }
      }
    }, space->Begin(), image_pointer_size_);
  }

  ClassTable* class_table = nullptr;
  {
    WriterMutexLock mu(self, *Locks::classlinker_classes_lock_);
    class_table = InsertClassTableForClassLoader(class_loader.Get());
  }
  // If we have a class table section, read it and use it for verification in
  // UpdateAppImageClassLoadersAndDexCaches.
  ClassTable::ClassSet temp_set;
  const ImageSection& class_table_section = header.GetClassTableSection();
  const bool added_class_table = class_table_section.Size() > 0u;
  if (added_class_table) {
    const uint64_t start_time2 = NanoTime();
    size_t read_count = 0;
    temp_set = ClassTable::ClassSet(space->Begin() + class_table_section.Offset(),
                                    /*make copy*/false,
                                    &read_count);
    VLOG(image) << "Adding class table classes took " << PrettyDuration(NanoTime() - start_time2);
  }
  if (app_image) {
    AppImageLoadingHelper::Update(this, space, class_loader, dex_caches, &temp_set);

    {
      ScopedTrace trace("AppImage:UpdateClassLoaders");
      // Update class loader and resolved strings. If added_class_table is false, the resolved
      // strings were forwarded UpdateAppImageClassLoadersAndDexCaches.
      ObjPtr<mirror::ClassLoader> loader(class_loader.Get());
      for (const ClassTable::TableSlot& root : temp_set) {
        // Note: We probably don't need the read barrier unless we copy the app image objects into
        // the region space.
        ObjPtr<mirror::Class> klass(root.Read());
        // Do not update class loader for boot image classes where the app image
        // class loader is only the initiating loader but not the defining loader.
        // Avoid read barrier since we are comparing against null.
        if (klass->GetClassLoader<kDefaultVerifyFlags, kWithoutReadBarrier>() != nullptr) {
          klass->SetClassLoader</*kCheckTransaction=*/ false>(loader);
        }
      }
    }

    if (kBitstringSubtypeCheckEnabled) {
      // Every class in the app image has initially SubtypeCheckInfo in the
      // Uninitialized state.
      //
      // The SubtypeCheck invariants imply that a SubtypeCheckInfo is at least Initialized
      // after class initialization is complete. The app image ClassStatus as-is
      // are almost all ClassStatus::Initialized, and being in the
      // SubtypeCheckInfo::kUninitialized state is violating that invariant.
      //
      // Force every app image class's SubtypeCheck to be at least kIninitialized.
      //
      // See also ImageWriter::FixupClass.
      ScopedTrace trace("AppImage:RecacluateSubtypeCheckBitstrings");
      MutexLock subtype_check_lock(Thread::Current(), *Locks::subtype_check_lock_);
      for (const ClassTable::TableSlot& root : temp_set) {
        SubtypeCheck<ObjPtr<mirror::Class>>::EnsureInitialized(root.Read());
      }
    }
  }
  if (!oat_file->GetBssGcRoots().empty()) {
    // Insert oat file to class table for visiting .bss GC roots.
    class_table->InsertOatFile(oat_file);
  }

  if (added_class_table) {
    WriterMutexLock mu(self, *Locks::classlinker_classes_lock_);
    class_table->AddClassSet(std::move(temp_set));
  }

  if (kIsDebugBuild && app_image) {
    // This verification needs to happen after the classes have been added to the class loader.
    // Since it ensures classes are in the class table.
    ScopedTrace trace("AppImage:Verify");
    VerifyAppImage(header, class_loader, dex_caches, class_table, space);
  }

  VLOG(class_linker) << "Adding image space took " << PrettyDuration(NanoTime() - start_time);
  return true;
}

bool ClassLinker::ClassInClassTable(ObjPtr<mirror::Class> klass) {
  ClassTable* const class_table = ClassTableForClassLoader(klass->GetClassLoader());
  return class_table != nullptr && class_table->Contains(klass);
}

void ClassLinker::VisitClassRoots(RootVisitor* visitor, VisitRootFlags flags) {
  // Acquire tracing_enabled before locking class linker lock to prevent lock order violation. Since
  // enabling tracing requires the mutator lock, there are no race conditions here.
  const bool tracing_enabled = Trace::IsTracingEnabled();
  Thread* const self = Thread::Current();
  WriterMutexLock mu(self, *Locks::classlinker_classes_lock_);
  if (kUseReadBarrier) {
    // We do not track new roots for CC.
    DCHECK_EQ(0, flags & (kVisitRootFlagNewRoots |
                          kVisitRootFlagClearRootLog |
                          kVisitRootFlagStartLoggingNewRoots |
                          kVisitRootFlagStopLoggingNewRoots));
  }
  if ((flags & kVisitRootFlagAllRoots) != 0) {
    // Argument for how root visiting deals with ArtField and ArtMethod roots.
    // There is 3 GC cases to handle:
    // Non moving concurrent:
    // This case is easy to handle since the reference members of ArtMethod and ArtFields are held
    // live by the class and class roots.
    //
    // Moving non-concurrent:
    // This case needs to call visit VisitNativeRoots in case the classes or dex cache arrays move.
    // To prevent missing roots, this case needs to ensure that there is no
    // suspend points between the point which we allocate ArtMethod arrays and place them in a
    // class which is in the class table.
    //
    // Moving concurrent:
    // Need to make sure to not copy ArtMethods without doing read barriers since the roots are
    // marked concurrently and we don't hold the classlinker_classes_lock_ when we do the copy.
    //
    // Use an unbuffered visitor since the class table uses a temporary GcRoot for holding decoded
    // ClassTable::TableSlot. The buffered root visiting would access a stale stack location for
    // these objects.
    UnbufferedRootVisitor root_visitor(visitor, RootInfo(kRootStickyClass));
    boot_class_table_->VisitRoots(root_visitor);
    // If tracing is enabled, then mark all the class loaders to prevent unloading.
    if ((flags & kVisitRootFlagClassLoader) != 0 || tracing_enabled) {
      for (const ClassLoaderData& data : class_loaders_) {
        GcRoot<mirror::Object> root(GcRoot<mirror::Object>(self->DecodeJObject(data.weak_root)));
        root.VisitRoot(visitor, RootInfo(kRootVMInternal));
      }
    }
  } else if (!kUseReadBarrier && (flags & kVisitRootFlagNewRoots) != 0) {
    for (auto& root : new_class_roots_) {
      ObjPtr<mirror::Class> old_ref = root.Read<kWithoutReadBarrier>();
      root.VisitRoot(visitor, RootInfo(kRootStickyClass));
      ObjPtr<mirror::Class> new_ref = root.Read<kWithoutReadBarrier>();
      // Concurrent moving GC marked new roots through the to-space invariant.
      CHECK_EQ(new_ref, old_ref);
    }
    for (const OatFile* oat_file : new_bss_roots_boot_oat_files_) {
      for (GcRoot<mirror::Object>& root : oat_file->GetBssGcRoots()) {
        ObjPtr<mirror::Object> old_ref = root.Read<kWithoutReadBarrier>();
        if (old_ref != nullptr) {
          DCHECK(old_ref->IsClass());
          root.VisitRoot(visitor, RootInfo(kRootStickyClass));
          ObjPtr<mirror::Object> new_ref = root.Read<kWithoutReadBarrier>();
          // Concurrent moving GC marked new roots through the to-space invariant.
          CHECK_EQ(new_ref, old_ref);
        }
      }
    }
  }
  if (!kUseReadBarrier && (flags & kVisitRootFlagClearRootLog) != 0) {
    new_class_roots_.clear();
    new_bss_roots_boot_oat_files_.clear();
  }
  if (!kUseReadBarrier && (flags & kVisitRootFlagStartLoggingNewRoots) != 0) {
    log_new_roots_ = true;
  } else if (!kUseReadBarrier && (flags & kVisitRootFlagStopLoggingNewRoots) != 0) {
    log_new_roots_ = false;
  }
  // We deliberately ignore the class roots in the image since we
  // handle image roots by using the MS/CMS rescanning of dirty cards.
}

// Keep in sync with InitCallback. Anything we visit, we need to
// reinit references to when reinitializing a ClassLinker from a
// mapped image.
void ClassLinker::VisitRoots(RootVisitor* visitor, VisitRootFlags flags) {
  class_roots_.VisitRootIfNonNull(visitor, RootInfo(kRootVMInternal));
  VisitClassRoots(visitor, flags);
  // Instead of visiting the find_array_class_cache_ drop it so that it doesn't prevent class
  // unloading if we are marking roots.
  DropFindArrayClassCache();
}

class VisitClassLoaderClassesVisitor : public ClassLoaderVisitor {
 public:
  explicit VisitClassLoaderClassesVisitor(ClassVisitor* visitor)
      : visitor_(visitor),
        done_(false) {}

  void Visit(ObjPtr<mirror::ClassLoader> class_loader)
      REQUIRES_SHARED(Locks::classlinker_classes_lock_, Locks::mutator_lock_) override {
    ClassTable* const class_table = class_loader->GetClassTable();
    if (!done_ && class_table != nullptr) {
      DefiningClassLoaderFilterVisitor visitor(class_loader, visitor_);
      if (!class_table->Visit(visitor)) {
        // If the visitor ClassTable returns false it means that we don't need to continue.
        done_ = true;
      }
    }
  }

 private:
  // Class visitor that limits the class visits from a ClassTable to the classes with
  // the provided defining class loader. This filter is used to avoid multiple visits
  // of the same class which can be recorded for multiple initiating class loaders.
  class DefiningClassLoaderFilterVisitor : public ClassVisitor {
   public:
    DefiningClassLoaderFilterVisitor(ObjPtr<mirror::ClassLoader> defining_class_loader,
                                     ClassVisitor* visitor)
        : defining_class_loader_(defining_class_loader), visitor_(visitor) { }

    bool operator()(ObjPtr<mirror::Class> klass) override REQUIRES_SHARED(Locks::mutator_lock_) {
      if (klass->GetClassLoader() != defining_class_loader_) {
        return true;
      }
      return (*visitor_)(klass);
    }

    const ObjPtr<mirror::ClassLoader> defining_class_loader_;
    ClassVisitor* const visitor_;
  };

  ClassVisitor* const visitor_;
  // If done is true then we don't need to do any more visiting.
  bool done_;
};

void ClassLinker::VisitClassesInternal(ClassVisitor* visitor) {
  if (boot_class_table_->Visit(*visitor)) {
    VisitClassLoaderClassesVisitor loader_visitor(visitor);
    VisitClassLoaders(&loader_visitor);
  }
}

void ClassLinker::VisitClasses(ClassVisitor* visitor) {
  Thread* const self = Thread::Current();
  ReaderMutexLock mu(self, *Locks::classlinker_classes_lock_);
  // Not safe to have thread suspension when we are holding a lock.
  if (self != nullptr) {
    ScopedAssertNoThreadSuspension nts(__FUNCTION__);
    VisitClassesInternal(visitor);
  } else {
    VisitClassesInternal(visitor);
  }
}

class GetClassesInToVector : public ClassVisitor {
 public:
  bool operator()(ObjPtr<mirror::Class> klass) override {
    classes_.push_back(klass);
    return true;
  }
  std::vector<ObjPtr<mirror::Class>> classes_;
};

class GetClassInToObjectArray : public ClassVisitor {
 public:
  explicit GetClassInToObjectArray(mirror::ObjectArray<mirror::Class>* arr)
      : arr_(arr), index_(0) {}

  bool operator()(ObjPtr<mirror::Class> klass) override REQUIRES_SHARED(Locks::mutator_lock_) {
    ++index_;
    if (index_ <= arr_->GetLength()) {
      arr_->Set(index_ - 1, klass);
      return true;
    }
    return false;
  }

  bool Succeeded() const REQUIRES_SHARED(Locks::mutator_lock_) {
    return index_ <= arr_->GetLength();
  }

 private:
  mirror::ObjectArray<mirror::Class>* const arr_;
  int32_t index_;
};

void ClassLinker::VisitClassesWithoutClassesLock(ClassVisitor* visitor) {
  // TODO: it may be possible to avoid secondary storage if we iterate over dex caches. The problem
  // is avoiding duplicates.
  if (!kMovingClasses) {
    ScopedAssertNoThreadSuspension nts(__FUNCTION__);
    GetClassesInToVector accumulator;
    VisitClasses(&accumulator);
    for (ObjPtr<mirror::Class> klass : accumulator.classes_) {
      if (!visitor->operator()(klass)) {
        return;
      }
    }
  } else {
    Thread* const self = Thread::Current();
    StackHandleScope<1> hs(self);
    auto classes = hs.NewHandle<mirror::ObjectArray<mirror::Class>>(nullptr);
    // We size the array assuming classes won't be added to the class table during the visit.
    // If this assumption fails we iterate again.
    while (true) {
      size_t class_table_size;
      {
        ReaderMutexLock mu(self, *Locks::classlinker_classes_lock_);
        // Add 100 in case new classes get loaded when we are filling in the object array.
        class_table_size = NumZygoteClasses() + NumNonZygoteClasses() + 100;
      }
      ObjPtr<mirror::Class> array_of_class = GetClassRoot<mirror::ObjectArray<mirror::Class>>(this);
      classes.Assign(
          mirror::ObjectArray<mirror::Class>::Alloc(self, array_of_class, class_table_size));
      CHECK(classes != nullptr);  // OOME.
      GetClassInToObjectArray accumulator(classes.Get());
      VisitClasses(&accumulator);
      if (accumulator.Succeeded()) {
        break;
      }
    }
    for (int32_t i = 0; i < classes->GetLength(); ++i) {
      // If the class table shrank during creation of the clases array we expect null elements. If
      // the class table grew then the loop repeats. If classes are created after the loop has
      // finished then we don't visit.
      ObjPtr<mirror::Class> klass = classes->Get(i);
      if (klass != nullptr && !visitor->operator()(klass)) {
        return;
      }
    }
  }
}

ClassLinker::~ClassLinker() {
  Thread* const self = Thread::Current();
  for (const ClassLoaderData& data : class_loaders_) {
    // CHA unloading analysis is not needed. No negative consequences are expected because
    // all the classloaders are deleted at the same time.
    DeleteClassLoader(self, data, /*cleanup_cha=*/ false);
  }
  class_loaders_.clear();
}

void ClassLinker::DeleteClassLoader(Thread* self, const ClassLoaderData& data, bool cleanup_cha) {
  Runtime* const runtime = Runtime::Current();
  JavaVMExt* const vm = runtime->GetJavaVM();
  vm->DeleteWeakGlobalRef(self, data.weak_root);
  // Notify the JIT that we need to remove the methods and/or profiling info.
  if (runtime->GetJit() != nullptr) {
    jit::JitCodeCache* code_cache = runtime->GetJit()->GetCodeCache();
    if (code_cache != nullptr) {
      // For the JIT case, RemoveMethodsIn removes the CHA dependencies.
      code_cache->RemoveMethodsIn(self, *data.allocator);
    }
  } else if (cha_ != nullptr) {
    // If we don't have a JIT, we need to manually remove the CHA dependencies manually.
    cha_->RemoveDependenciesForLinearAlloc(data.allocator);
  }
  // Cleanup references to single implementation ArtMethods that will be deleted.
  if (cleanup_cha) {
    CHAOnDeleteUpdateClassVisitor visitor(data.allocator);
    data.class_table->Visit<CHAOnDeleteUpdateClassVisitor, kWithoutReadBarrier>(visitor);
  }

  delete data.allocator;
  delete data.class_table;
}

ObjPtr<mirror::PointerArray> ClassLinker::AllocPointerArray(Thread* self, size_t length) {
  return ObjPtr<mirror::PointerArray>::DownCast(
      image_pointer_size_ == PointerSize::k64
          ? ObjPtr<mirror::Array>(mirror::LongArray::Alloc(self, length))
          : ObjPtr<mirror::Array>(mirror::IntArray::Alloc(self, length)));
}

ObjPtr<mirror::DexCache> ClassLinker::AllocDexCache(/*out*/ ObjPtr<mirror::String>* out_location,
                                                    Thread* self,
                                                    const DexFile& dex_file) {
  StackHandleScope<1> hs(self);
  DCHECK(out_location != nullptr);
  auto dex_cache(hs.NewHandle(ObjPtr<mirror::DexCache>::DownCast(
      GetClassRoot<mirror::DexCache>(this)->AllocObject(self))));
  if (dex_cache == nullptr) {
    self->AssertPendingOOMException();
    return nullptr;
  }
  ObjPtr<mirror::String> location = intern_table_->InternStrong(dex_file.GetLocation().c_str());
  if (location == nullptr) {
    self->AssertPendingOOMException();
    return nullptr;
  }
  *out_location = location;
  return dex_cache.Get();
}

ObjPtr<mirror::DexCache> ClassLinker::AllocAndInitializeDexCache(Thread* self,
                                                                 const DexFile& dex_file,
                                                                 LinearAlloc* linear_alloc) {
  ObjPtr<mirror::String> location = nullptr;
  ObjPtr<mirror::DexCache> dex_cache = AllocDexCache(&location, self, dex_file);
  if (dex_cache != nullptr) {
    WriterMutexLock mu(self, *Locks::dex_lock_);
    DCHECK(location != nullptr);
    mirror::DexCache::InitializeDexCache(self,
                                         dex_cache,
                                         location,
                                         &dex_file,
                                         linear_alloc,
                                         image_pointer_size_);
  }
  return dex_cache;
}

template <bool kMovable>
ObjPtr<mirror::Class> ClassLinker::AllocClass(Thread* self,
                                              ObjPtr<mirror::Class> java_lang_Class,
                                              uint32_t class_size) {
  DCHECK_GE(class_size, sizeof(mirror::Class));
  gc::Heap* heap = Runtime::Current()->GetHeap();
  mirror::Class::InitializeClassVisitor visitor(class_size);
  ObjPtr<mirror::Object> k = (kMovingClasses && kMovable) ?
      heap->AllocObject<true>(self, java_lang_Class, class_size, visitor) :
      heap->AllocNonMovableObject<true>(self, java_lang_Class, class_size, visitor);
  if (UNLIKELY(k == nullptr)) {
    self->AssertPendingOOMException();
    return nullptr;
  }
  return k->AsClass();
}

ObjPtr<mirror::Class> ClassLinker::AllocClass(Thread* self, uint32_t class_size) {
  return AllocClass(self, GetClassRoot<mirror::Class>(this), class_size);
}

ObjPtr<mirror::Class> ClassLinker::AllocPrimitiveArrayClass(Thread* self,
                                                            ObjPtr<mirror::Class> java_lang_Class) {
  // We make this class non-movable for the unlikely case where it were to be
  // moved by a sticky-bit (minor) collection when using the Generational
  // Concurrent Copying (CC) collector, potentially creating a stale reference
  // in the `klass_` field of one of its instances allocated in the Large-Object
  // Space (LOS) -- see the comment about the dirty card scanning logic in
  // art::gc::collector::ConcurrentCopying::MarkingPhase.
  return AllocClass</* kMovable= */ false>(
      self, java_lang_Class, mirror::Array::ClassSize(image_pointer_size_));
}

ObjPtr<mirror::ObjectArray<mirror::StackTraceElement>> ClassLinker::AllocStackTraceElementArray(
    Thread* self,
    size_t length) {
  return mirror::ObjectArray<mirror::StackTraceElement>::Alloc(
      self, GetClassRoot<mirror::ObjectArray<mirror::StackTraceElement>>(this), length);
}

ObjPtr<mirror::Class> ClassLinker::EnsureResolved(Thread* self,
                                                  const char* descriptor,
                                                  ObjPtr<mirror::Class> klass) {
  DCHECK(klass != nullptr);
  if (kIsDebugBuild) {
    StackHandleScope<1> hs(self);
    HandleWrapperObjPtr<mirror::Class> h = hs.NewHandleWrapper(&klass);
    Thread::PoisonObjectPointersIfDebug();
  }

  // For temporary classes we must wait for them to be retired.
  if (init_done_ && klass->IsTemp()) {
    CHECK(!klass->IsResolved());
    if (klass->IsErroneousUnresolved()) {
      ThrowEarlierClassFailure(klass);
      return nullptr;
    }
    StackHandleScope<1> hs(self);
    Handle<mirror::Class> h_class(hs.NewHandle(klass));
    ObjectLock<mirror::Class> lock(self, h_class);
    // Loop and wait for the resolving thread to retire this class.
    while (!h_class->IsRetired() && !h_class->IsErroneousUnresolved()) {
      lock.WaitIgnoringInterrupts();
    }
    if (h_class->IsErroneousUnresolved()) {
      ThrowEarlierClassFailure(h_class.Get());
      return nullptr;
    }
    CHECK(h_class->IsRetired());
    // Get the updated class from class table.
    klass = LookupClass(self, descriptor, h_class.Get()->GetClassLoader());
  }

  // Wait for the class if it has not already been linked.
  size_t index = 0;
  // Maximum number of yield iterations until we start sleeping.
  static const size_t kNumYieldIterations = 1000;
  // How long each sleep is in us.
  static const size_t kSleepDurationUS = 1000;  // 1 ms.
  while (!klass->IsResolved() && !klass->IsErroneousUnresolved()) {
    StackHandleScope<1> hs(self);
    HandleWrapperObjPtr<mirror::Class> h_class(hs.NewHandleWrapper(&klass));
    {
      ObjectTryLock<mirror::Class> lock(self, h_class);
      // Can not use a monitor wait here since it may block when returning and deadlock if another
      // thread has locked klass.
      if (lock.Acquired()) {
        // Check for circular dependencies between classes, the lock is required for SetStatus.
        if (!h_class->IsResolved() && h_class->GetClinitThreadId() == self->GetTid()) {
          ThrowClassCircularityError(h_class.Get());
          mirror::Class::SetStatus(h_class, ClassStatus::kErrorUnresolved, self);
          return nullptr;
        }
      }
    }
    {
      // Handle wrapper deals with klass moving.
      ScopedThreadSuspension sts(self, kSuspended);
      if (index < kNumYieldIterations) {
        sched_yield();
      } else {
        usleep(kSleepDurationUS);
      }
    }
    ++index;
  }

  if (klass->IsErroneousUnresolved()) {
    ThrowEarlierClassFailure(klass);
    return nullptr;
  }
  // Return the loaded class.  No exceptions should be pending.
  CHECK(klass->IsResolved()) << klass->PrettyClass();
  self->AssertNoPendingException();
  return klass;
}

using ClassPathEntry = std::pair<const DexFile*, const dex::ClassDef*>;

// Search a collection of DexFiles for a descriptor
ClassPathEntry FindInClassPath(const char* descriptor,
                               size_t hash, const std::vector<const DexFile*>& class_path) {
  for (const DexFile* dex_file : class_path) {
    const dex::ClassDef* dex_class_def = OatDexFile::FindClassDef(*dex_file, descriptor, hash);
    if (dex_class_def != nullptr) {
      return ClassPathEntry(dex_file, dex_class_def);
    }
  }
  return ClassPathEntry(nullptr, nullptr);
}

bool ClassLinker::FindClassInSharedLibraries(ScopedObjectAccessAlreadyRunnable& soa,
                                             Thread* self,
                                             const char* descriptor,
                                             size_t hash,
                                             Handle<mirror::ClassLoader> class_loader,
                                             /*out*/ ObjPtr<mirror::Class>* result) {
  ArtField* field =
      jni::DecodeArtField(WellKnownClasses::dalvik_system_BaseDexClassLoader_sharedLibraryLoaders);
  ObjPtr<mirror::Object> raw_shared_libraries = field->GetObject(class_loader.Get());
  if (raw_shared_libraries == nullptr) {
    return true;
  }

  StackHandleScope<2> hs(self);
  Handle<mirror::ObjectArray<mirror::ClassLoader>> shared_libraries(
      hs.NewHandle(raw_shared_libraries->AsObjectArray<mirror::ClassLoader>()));
  MutableHandle<mirror::ClassLoader> temp_loader = hs.NewHandle<mirror::ClassLoader>(nullptr);
  for (int32_t i = 0; i < shared_libraries->GetLength(); ++i) {
    temp_loader.Assign(shared_libraries->Get(i));
    if (!FindClassInBaseDexClassLoader(soa, self, descriptor, hash, temp_loader, result)) {
      return false;  // One of the shared libraries is not supported.
    }
    if (*result != nullptr) {
      return true;  // Found the class up the chain.
    }
  }
  return true;
}

bool ClassLinker::FindClassInBaseDexClassLoader(ScopedObjectAccessAlreadyRunnable& soa,
                                                Thread* self,
                                                const char* descriptor,
                                                size_t hash,
                                                Handle<mirror::ClassLoader> class_loader,
                                                /*out*/ ObjPtr<mirror::Class>* result) {
  // Termination case: boot class loader.
  if (IsBootClassLoader(soa, class_loader.Get())) {
    *result = FindClassInBootClassLoaderClassPath(self, descriptor, hash);
    return true;
  }

  if (IsPathOrDexClassLoader(soa, class_loader) || IsInMemoryDexClassLoader(soa, class_loader)) {
    // For regular path or dex class loader the search order is:
    //    - parent
    //    - shared libraries
    //    - class loader dex files

    // Handles as RegisterDexFile may allocate dex caches (and cause thread suspension).
    StackHandleScope<1> hs(self);
    Handle<mirror::ClassLoader> h_parent(hs.NewHandle(class_loader->GetParent()));
    if (!FindClassInBaseDexClassLoader(soa, self, descriptor, hash, h_parent, result)) {
      return false;  // One of the parents is not supported.
    }
    if (*result != nullptr) {
      return true;  // Found the class up the chain.
    }

    if (!FindClassInSharedLibraries(soa, self, descriptor, hash, class_loader, result)) {
      return false;  // One of the shared library loader is not supported.
    }
    if (*result != nullptr) {
      return true;  // Found the class in a shared library.
    }

    // Search the current class loader classpath.
    *result = FindClassInBaseDexClassLoaderClassPath(soa, descriptor, hash, class_loader);
    return !soa.Self()->IsExceptionPending();
  }

  if (IsDelegateLastClassLoader(soa, class_loader)) {
    // For delegate last, the search order is:
    //    - boot class path
    //    - shared libraries
    //    - class loader dex files
    //    - parent
    *result = FindClassInBootClassLoaderClassPath(self, descriptor, hash);
    if (*result != nullptr) {
      return true;  // The class is part of the boot class path.
    }
    if (self->IsExceptionPending()) {
      // Pending exception means there was an error other than ClassNotFound that must be returned
      // to the caller.
      return false;
    }

    if (!FindClassInSharedLibraries(soa, self, descriptor, hash, class_loader, result)) {
      return false;  // One of the shared library loader is not supported.
    }
    if (*result != nullptr) {
      return true;  // Found the class in a shared library.
    }

    *result = FindClassInBaseDexClassLoaderClassPath(soa, descriptor, hash, class_loader);
    if (*result != nullptr) {
      return true;  // Found the class in the current class loader
    }
    if (self->IsExceptionPending()) {
      // Pending exception means there was an error other than ClassNotFound that must be returned
      // to the caller.
      return false;
    }

    // Handles as RegisterDexFile may allocate dex caches (and cause thread suspension).
    StackHandleScope<1> hs(self);
    Handle<mirror::ClassLoader> h_parent(hs.NewHandle(class_loader->GetParent()));
    return FindClassInBaseDexClassLoader(soa, self, descriptor, hash, h_parent, result);
  }

  // Unsupported class loader.
  *result = nullptr;
  return false;
}

namespace {

// Matches exceptions caught in DexFile.defineClass.
ALWAYS_INLINE bool MatchesDexFileCaughtExceptions(ObjPtr<mirror::Throwable> throwable,
                                                  ClassLinker* class_linker)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  return
      // ClassNotFoundException.
      throwable->InstanceOf(GetClassRoot(ClassRoot::kJavaLangClassNotFoundException,
                                         class_linker))
      ||
      // NoClassDefFoundError. TODO: Reconsider this. b/130746382.
      throwable->InstanceOf(Runtime::Current()->GetPreAllocatedNoClassDefFoundError()->GetClass());
}

// Clear exceptions caught in DexFile.defineClass.
ALWAYS_INLINE void FilterDexFileCaughtExceptions(Thread* self, ClassLinker* class_linker)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  if (MatchesDexFileCaughtExceptions(self->GetException(), class_linker)) {
    self->ClearException();
  }
}

}  // namespace

// Finds the class in the boot class loader.
// If the class is found the method returns the resolved class. Otherwise it returns null.
ObjPtr<mirror::Class> ClassLinker::FindClassInBootClassLoaderClassPath(Thread* self,
                                                                       const char* descriptor,
                                                                       size_t hash) {
  ObjPtr<mirror::Class> result = nullptr;
  ClassPathEntry pair = FindInClassPath(descriptor, hash, boot_class_path_);
  if (pair.second != nullptr) {
    ObjPtr<mirror::Class> klass = LookupClass(self, descriptor, hash, nullptr);
    if (klass != nullptr) {
      result = EnsureResolved(self, descriptor, klass);
    } else {
      result = DefineClass(self,
                           descriptor,
                           hash,
                           ScopedNullHandle<mirror::ClassLoader>(),
                           *pair.first,
                           *pair.second);
    }
    if (result == nullptr) {
      CHECK(self->IsExceptionPending()) << descriptor;
      FilterDexFileCaughtExceptions(self, this);
    }
  }
  return result;
}

ObjPtr<mirror::Class> ClassLinker::FindClassInBaseDexClassLoaderClassPath(
    ScopedObjectAccessAlreadyRunnable& soa,
    const char* descriptor,
    size_t hash,
    Handle<mirror::ClassLoader> class_loader) {
  DCHECK(IsPathOrDexClassLoader(soa, class_loader) ||
         IsInMemoryDexClassLoader(soa, class_loader) ||
         IsDelegateLastClassLoader(soa, class_loader))
      << "Unexpected class loader for descriptor " << descriptor;

  ObjPtr<mirror::Class> ret;
  auto define_class = [&](const DexFile* cp_dex_file) REQUIRES_SHARED(Locks::mutator_lock_) {
    const dex::ClassDef* dex_class_def = OatDexFile::FindClassDef(*cp_dex_file, descriptor, hash);
    if (dex_class_def != nullptr) {
      ObjPtr<mirror::Class> klass = DefineClass(soa.Self(),
                                                descriptor,
                                                hash,
                                                class_loader,
                                                *cp_dex_file,
                                                *dex_class_def);
      if (klass == nullptr) {
        CHECK(soa.Self()->IsExceptionPending()) << descriptor;
        FilterDexFileCaughtExceptions(soa.Self(), this);
        // TODO: Is it really right to break here, and not check the other dex files?
      } else {
        DCHECK(!soa.Self()->IsExceptionPending());
      }
      ret = klass;
      return false;  // Found a Class (or error == nullptr), stop visit.
    }
    return true;  // Continue with the next DexFile.
  };

  VisitClassLoaderDexFiles(soa, class_loader, define_class);
  return ret;
}

ObjPtr<mirror::Class> ClassLinker::FindClass(Thread* self,
                                             const char* descriptor,
                                             Handle<mirror::ClassLoader> class_loader) {
  DCHECK_NE(*descriptor, '\0') << "descriptor is empty string";
  DCHECK(self != nullptr);
  self->AssertNoPendingException();
  self->PoisonObjectPointers();  // For DefineClass, CreateArrayClass, etc...
  if (descriptor[1] == '\0') {
    // only the descriptors of primitive types should be 1 character long, also avoid class lookup
    // for primitive classes that aren't backed by dex files.
    return FindPrimitiveClass(descriptor[0]);
  }
  const size_t hash = ComputeModifiedUtf8Hash(descriptor);
  // Find the class in the loaded classes table.
  ObjPtr<mirror::Class> klass = LookupClass(self, descriptor, hash, class_loader.Get());
  if (klass != nullptr) {
    return EnsureResolved(self, descriptor, klass);
  }
  // Class is not yet loaded.
  if (descriptor[0] != '[' && class_loader == nullptr) {
    // Non-array class and the boot class loader, search the boot class path.
    ClassPathEntry pair = FindInClassPath(descriptor, hash, boot_class_path_);
    if (pair.second != nullptr) {
      return DefineClass(self,
                         descriptor,
                         hash,
                         ScopedNullHandle<mirror::ClassLoader>(),
                         *pair.first,
                         *pair.second);
    } else {
      // The boot class loader is searched ahead of the application class loader, failures are
      // expected and will be wrapped in a ClassNotFoundException. Use the pre-allocated error to
      // trigger the chaining with a proper stack trace.
      ObjPtr<mirror::Throwable> pre_allocated =
          Runtime::Current()->GetPreAllocatedNoClassDefFoundError();
      self->SetException(pre_allocated);
      return nullptr;
    }
  }
  ObjPtr<mirror::Class> result_ptr;
  bool descriptor_equals;
  if (descriptor[0] == '[') {
    result_ptr = CreateArrayClass(self, descriptor, hash, class_loader);
    DCHECK_EQ(result_ptr == nullptr, self->IsExceptionPending());
    DCHECK(result_ptr == nullptr || result_ptr->DescriptorEquals(descriptor));
    descriptor_equals = true;
  } else {
    ScopedObjectAccessUnchecked soa(self);
    bool known_hierarchy =
        FindClassInBaseDexClassLoader(soa, self, descriptor, hash, class_loader, &result_ptr);
    if (result_ptr != nullptr) {
      // The chain was understood and we found the class. We still need to add the class to
      // the class table to protect from racy programs that can try and redefine the path list
      // which would change the Class<?> returned for subsequent evaluation of const-class.
      DCHECK(known_hierarchy);
      DCHECK(result_ptr->DescriptorEquals(descriptor));
      descriptor_equals = true;
    } else if (!self->IsExceptionPending()) {
      // Either the chain wasn't understood or the class wasn't found.
      // If there is a pending exception we didn't clear, it is a not a ClassNotFoundException and
      // we should return it instead of silently clearing and retrying.
      //
      // If the chain was understood but we did not find the class, let the Java-side
      // rediscover all this and throw the exception with the right stack trace. Note that
      // the Java-side could still succeed for racy programs if another thread is actively
      // modifying the class loader's path list.

      // The runtime is not allowed to call into java from a runtime-thread so just abort.
      if (self->IsRuntimeThread()) {
        // Oops, we can't call into java so we can't run actual class-loader code.
        // This is true for e.g. for the compiler (jit or aot).
        ObjPtr<mirror::Throwable> pre_allocated =
            Runtime::Current()->GetPreAllocatedNoClassDefFoundError();
        self->SetException(pre_allocated);
        return nullptr;
      }

      // Inlined DescriptorToDot(descriptor) with extra validation.
      //
      // Throw NoClassDefFoundError early rather than potentially load a class only to fail
      // the DescriptorEquals() check below and give a confusing error message. For example,
      // when native code erroneously calls JNI GetFieldId() with signature "java/lang/String"
      // instead of "Ljava/lang/String;", the message below using the "dot" names would be
      // "class loader [...] returned class java.lang.String instead of java.lang.String".
      size_t descriptor_length = strlen(descriptor);
      if (UNLIKELY(descriptor[0] != 'L') ||
          UNLIKELY(descriptor[descriptor_length - 1] != ';') ||
          UNLIKELY(memchr(descriptor + 1, '.', descriptor_length - 2) != nullptr)) {
        ThrowNoClassDefFoundError("Invalid descriptor: %s.", descriptor);
        return nullptr;
      }

      std::string class_name_string(descriptor + 1, descriptor_length - 2);
      std::replace(class_name_string.begin(), class_name_string.end(), '/', '.');
      if (known_hierarchy &&
          fast_class_not_found_exceptions_ &&
          !Runtime::Current()->IsJavaDebuggable()) {
        // For known hierarchy, we know that the class is going to throw an exception. If we aren't
        // debuggable, optimize this path by throwing directly here without going back to Java
        // language. This reduces how many ClassNotFoundExceptions happen.
        self->ThrowNewExceptionF("Ljava/lang/ClassNotFoundException;",
                                 "%s",
                                 class_name_string.c_str());
      } else {
        ScopedLocalRef<jobject> class_loader_object(
            soa.Env(), soa.AddLocalReference<jobject>(class_loader.Get()));
        ScopedLocalRef<jobject> result(soa.Env(), nullptr);
        {
          ScopedThreadStateChange tsc(self, kNative);
          ScopedLocalRef<jobject> class_name_object(
              soa.Env(), soa.Env()->NewStringUTF(class_name_string.c_str()));
          if (class_name_object.get() == nullptr) {
            DCHECK(self->IsExceptionPending());  // OOME.
            return nullptr;
          }
          CHECK(class_loader_object.get() != nullptr);
          result.reset(soa.Env()->CallObjectMethod(class_loader_object.get(),
                                                   WellKnownClasses::java_lang_ClassLoader_loadClass,
                                                   class_name_object.get()));
        }
        if (result.get() == nullptr && !self->IsExceptionPending()) {
          // broken loader - throw NPE to be compatible with Dalvik
          ThrowNullPointerException(StringPrintf("ClassLoader.loadClass returned null for %s",
                                                 class_name_string.c_str()).c_str());
          return nullptr;
        }
        result_ptr = soa.Decode<mirror::Class>(result.get());
        // Check the name of the returned class.
        descriptor_equals = (result_ptr != nullptr) && result_ptr->DescriptorEquals(descriptor);
      }
    } else {
      DCHECK(!MatchesDexFileCaughtExceptions(self->GetException(), this));
    }
  }

  if (self->IsExceptionPending()) {
    // If the ClassLoader threw or array class allocation failed, pass that exception up.
    // However, to comply with the RI behavior, first check if another thread succeeded.
    result_ptr = LookupClass(self, descriptor, hash, class_loader.Get());
    if (result_ptr != nullptr && !result_ptr->IsErroneous()) {
      self->ClearException();
      return EnsureResolved(self, descriptor, result_ptr);
    }
    return nullptr;
  }

  // Try to insert the class to the class table, checking for mismatch.
  ObjPtr<mirror::Class> old;
  {
    WriterMutexLock mu(self, *Locks::classlinker_classes_lock_);
    ClassTable* const class_table = InsertClassTableForClassLoader(class_loader.Get());
    old = class_table->Lookup(descriptor, hash);
    if (old == nullptr) {
      old = result_ptr;  // For the comparison below, after releasing the lock.
      if (descriptor_equals) {
        class_table->InsertWithHash(result_ptr, hash);
        WriteBarrier::ForEveryFieldWrite(class_loader.Get());
      }  // else throw below, after releasing the lock.
    }
  }
  if (UNLIKELY(old != result_ptr)) {
    // Return `old` (even if `!descriptor_equals`) to mimic the RI behavior for parallel
    // capable class loaders.  (All class loaders are considered parallel capable on Android.)
    ObjPtr<mirror::Class> loader_class = class_loader->GetClass();
    const char* loader_class_name =
        loader_class->GetDexFile().StringByTypeIdx(loader_class->GetDexTypeIndex());
    LOG(WARNING) << "Initiating class loader of type " << DescriptorToDot(loader_class_name)
        << " is not well-behaved; it returned a different Class for racing loadClass(\""
        << DescriptorToDot(descriptor) << "\").";
    return EnsureResolved(self, descriptor, old);
  }
  if (UNLIKELY(!descriptor_equals)) {
    std::string result_storage;
    const char* result_name = result_ptr->GetDescriptor(&result_storage);
    std::string loader_storage;
    const char* loader_class_name = class_loader->GetClass()->GetDescriptor(&loader_storage);
    ThrowNoClassDefFoundError(
        "Initiating class loader of type %s returned class %s instead of %s.",
        DescriptorToDot(loader_class_name).c_str(),
        DescriptorToDot(result_name).c_str(),
        DescriptorToDot(descriptor).c_str());
    return nullptr;
  }
  // Success.
  return result_ptr;
}

static bool IsReservedBootClassPathDescriptor(const char* descriptor) {
  std::string_view descriptor_sv(descriptor);
  return
      // Reserved conscrypt packages (includes sub-packages under these paths).
      StartsWith(descriptor_sv, "Landroid/net/ssl/") ||
      StartsWith(descriptor_sv, "Lcom/android/org/conscrypt/") ||
      // Reserved updatable-media package (includes sub-packages under this path).
      StartsWith(descriptor_sv, "Landroid/media/");
}

ObjPtr<mirror::Class> ClassLinker::DefineClass(Thread* self,
                                               const char* descriptor,
                                               size_t hash,
                                               Handle<mirror::ClassLoader> class_loader,
                                               const DexFile& dex_file,
                                               const dex::ClassDef& dex_class_def) {
  StackHandleScope<3> hs(self);
  auto klass = hs.NewHandle<mirror::Class>(nullptr);

  // Load the class from the dex file.
  if (UNLIKELY(!init_done_)) {
    // finish up init of hand crafted class_roots_
    if (strcmp(descriptor, "Ljava/lang/Object;") == 0) {
      klass.Assign(GetClassRoot<mirror::Object>(this));
    } else if (strcmp(descriptor, "Ljava/lang/Class;") == 0) {
      klass.Assign(GetClassRoot<mirror::Class>(this));
    } else if (strcmp(descriptor, "Ljava/lang/String;") == 0) {
      klass.Assign(GetClassRoot<mirror::String>(this));
    } else if (strcmp(descriptor, "Ljava/lang/ref/Reference;") == 0) {
      klass.Assign(GetClassRoot<mirror::Reference>(this));
    } else if (strcmp(descriptor, "Ljava/lang/DexCache;") == 0) {
      klass.Assign(GetClassRoot<mirror::DexCache>(this));
    } else if (strcmp(descriptor, "Ldalvik/system/ClassExt;") == 0) {
      klass.Assign(GetClassRoot<mirror::ClassExt>(this));
    }
  }

  // For AOT-compilation of an app, we may use a shortened boot class path that excludes
  // some runtime modules. Prevent definition of classes in app class loader that could clash
  // with these modules as these classes could be resolved differently during execution.
  if (class_loader != nullptr &&
      Runtime::Current()->IsAotCompiler() &&
      IsReservedBootClassPathDescriptor(descriptor)) {
    ObjPtr<mirror::Throwable> pre_allocated =
        Runtime::Current()->GetPreAllocatedNoClassDefFoundError();
    self->SetException(pre_allocated);
    return nullptr;
  }

  // This is to prevent the calls to ClassLoad and ClassPrepare which can cause java/user-supplied
  // code to be executed. We put it up here so we can avoid all the allocations associated with
  // creating the class. This can happen with (eg) jit threads.
  if (!self->CanLoadClasses()) {
    // Make sure we don't try to load anything, potentially causing an infinite loop.
    ObjPtr<mirror::Throwable> pre_allocated =
        Runtime::Current()->GetPreAllocatedNoClassDefFoundError();
    self->SetException(pre_allocated);
    return nullptr;
  }

  if (klass == nullptr) {
    // Allocate a class with the status of not ready.
    // Interface object should get the right size here. Regular class will
    // figure out the right size later and be replaced with one of the right
    // size when the class becomes resolved.
    klass.Assign(AllocClass(self, SizeOfClassWithoutEmbeddedTables(dex_file, dex_class_def)));
  }
  if (UNLIKELY(klass == nullptr)) {
    self->AssertPendingOOMException();
    return nullptr;
  }
  // Get the real dex file. This will return the input if there aren't any callbacks or they do
  // nothing.
  DexFile const* new_dex_file = nullptr;
  dex::ClassDef const* new_class_def = nullptr;
  // TODO We should ideally figure out some way to move this after we get a lock on the klass so it
  // will only be called once.
  Runtime::Current()->GetRuntimeCallbacks()->ClassPreDefine(descriptor,
                                                            klass,
                                                            class_loader,
                                                            dex_file,
                                                            dex_class_def,
                                                            &new_dex_file,
                                                            &new_class_def);
  // Check to see if an exception happened during runtime callbacks. Return if so.
  if (self->IsExceptionPending()) {
    return nullptr;
  }
  ObjPtr<mirror::DexCache> dex_cache = RegisterDexFile(*new_dex_file, class_loader.Get());
  if (dex_cache == nullptr) {
    self->AssertPendingException();
    return nullptr;
  }
  klass->SetDexCache(dex_cache);
  SetupClass(*new_dex_file, *new_class_def, klass, class_loader.Get());

  // Mark the string class by setting its access flag.
  if (UNLIKELY(!init_done_)) {
    if (strcmp(descriptor, "Ljava/lang/String;") == 0) {
      klass->SetStringClass();
    }
  }

  ObjectLock<mirror::Class> lock(self, klass);
  klass->SetClinitThreadId(self->GetTid());
  // Make sure we have a valid empty iftable even if there are errors.
  klass->SetIfTable(GetClassRoot<mirror::Object>(this)->GetIfTable());

  // Add the newly loaded class to the loaded classes table.
  ObjPtr<mirror::Class> existing = InsertClass(descriptor, klass.Get(), hash);
  if (existing != nullptr) {
    // We failed to insert because we raced with another thread. Calling EnsureResolved may cause
    // this thread to block.
    return EnsureResolved(self, descriptor, existing);
  }

  // Load the fields and other things after we are inserted in the table. This is so that we don't
  // end up allocating unfree-able linear alloc resources and then lose the race condition. The
  // other reason is that the field roots are only visited from the class table. So we need to be
  // inserted before we allocate / fill in these fields.
  LoadClass(self, *new_dex_file, *new_class_def, klass);
  if (self->IsExceptionPending()) {
    VLOG(class_linker) << self->GetException()->Dump();
    // An exception occured during load, set status to erroneous while holding klass' lock in case
    // notification is necessary.
    if (!klass->IsErroneous()) {
      mirror::Class::SetStatus(klass, ClassStatus::kErrorUnresolved, self);
    }
    return nullptr;
  }

  // Finish loading (if necessary) by finding parents
  CHECK(!klass->IsLoaded());
  if (!LoadSuperAndInterfaces(klass, *new_dex_file)) {
    // Loading failed.
    if (!klass->IsErroneous()) {
      mirror::Class::SetStatus(klass, ClassStatus::kErrorUnresolved, self);
    }
    return nullptr;
  }
  CHECK(klass->IsLoaded());

  // At this point the class is loaded. Publish a ClassLoad event.
  // Note: this may be a temporary class. It is a listener's responsibility to handle this.
  Runtime::Current()->GetRuntimeCallbacks()->ClassLoad(klass);

  // Link the class (if necessary)
  CHECK(!klass->IsResolved());
  // TODO: Use fast jobjects?
  auto interfaces = hs.NewHandle<mirror::ObjectArray<mirror::Class>>(nullptr);

  MutableHandle<mirror::Class> h_new_class = hs.NewHandle<mirror::Class>(nullptr);
  if (!LinkClass(self, descriptor, klass, interfaces, &h_new_class)) {
    // Linking failed.
    if (!klass->IsErroneous()) {
      mirror::Class::SetStatus(klass, ClassStatus::kErrorUnresolved, self);
    }
    return nullptr;
  }
  self->AssertNoPendingException();
  CHECK(h_new_class != nullptr) << descriptor;
  CHECK(h_new_class->IsResolved() && !h_new_class->IsErroneousResolved()) << descriptor;

  // Instrumentation may have updated entrypoints for all methods of all
  // classes. However it could not update methods of this class while we
  // were loading it. Now the class is resolved, we can update entrypoints
  // as required by instrumentation.
  if (Runtime::Current()->GetInstrumentation()->AreExitStubsInstalled()) {
    // We must be in the kRunnable state to prevent instrumentation from
    // suspending all threads to update entrypoints while we are doing it
    // for this class.
    DCHECK_EQ(self->GetState(), kRunnable);
    Runtime::Current()->GetInstrumentation()->InstallStubsForClass(h_new_class.Get());
  }

  /*
   * We send CLASS_PREPARE events to the debugger from here.  The
   * definition of "preparation" is creating the static fields for a
   * class and initializing them to the standard default values, but not
   * executing any code (that comes later, during "initialization").
   *
   * We did the static preparation in LinkClass.
   *
   * The class has been prepared and resolved but possibly not yet verified
   * at this point.
   */
  Runtime::Current()->GetRuntimeCallbacks()->ClassPrepare(klass, h_new_class);

  // Notify native debugger of the new class and its layout.
  jit::Jit::NewTypeLoadedIfUsingJit(h_new_class.Get());

  return h_new_class.Get();
}

uint32_t ClassLinker::SizeOfClassWithoutEmbeddedTables(const DexFile& dex_file,
                                                       const dex::ClassDef& dex_class_def) {
  size_t num_ref = 0;
  size_t num_8 = 0;
  size_t num_16 = 0;
  size_t num_32 = 0;
  size_t num_64 = 0;
  ClassAccessor accessor(dex_file, dex_class_def);
  // We allow duplicate definitions of the same field in a class_data_item
  // but ignore the repeated indexes here, b/21868015.
  uint32_t last_field_idx = dex::kDexNoIndex;
  for (const ClassAccessor::Field& field : accessor.GetStaticFields()) {
    uint32_t field_idx = field.GetIndex();
    // Ordering enforced by DexFileVerifier.
    DCHECK(last_field_idx == dex::kDexNoIndex || last_field_idx <= field_idx);
    if (UNLIKELY(field_idx == last_field_idx)) {
      continue;
    }
    last_field_idx = field_idx;
    const dex::FieldId& field_id = dex_file.GetFieldId(field_idx);
    const char* descriptor = dex_file.GetFieldTypeDescriptor(field_id);
    char c = descriptor[0];
    switch (c) {
      case 'L':
      case '[':
        num_ref++;
        break;
      case 'J':
      case 'D':
        num_64++;
        break;
      case 'I':
      case 'F':
        num_32++;
        break;
      case 'S':
      case 'C':
        num_16++;
        break;
      case 'B':
      case 'Z':
        num_8++;
        break;
      default:
        LOG(FATAL) << "Unknown descriptor: " << c;
        UNREACHABLE();
    }
  }
  return mirror::Class::ComputeClassSize(false,
                                         0,
                                         num_8,
                                         num_16,
                                         num_32,
                                         num_64,
                                         num_ref,
                                         image_pointer_size_);
}

// Special case to get oat code without overwriting a trampoline.
const void* ClassLinker::GetQuickOatCodeFor(ArtMethod* method) {
  CHECK(method->IsInvokable()) << method->PrettyMethod();
  if (method->IsProxyMethod()) {
    return GetQuickProxyInvokeHandler();
  }
  auto* code = method->GetOatMethodQuickCode(GetImagePointerSize());
  if (code != nullptr) {
    return code;
  }
  if (method->IsNative()) {
    // No code and native? Use generic trampoline.
    return GetQuickGenericJniStub();
  }
  return GetQuickToInterpreterBridge();
}

bool ClassLinker::ShouldUseInterpreterEntrypoint(ArtMethod* method, const void* quick_code) {
  ScopedAssertNoThreadSuspension sants(__FUNCTION__);
  if (UNLIKELY(method->IsNative() || method->IsProxyMethod())) {
    return false;
  }

  if (quick_code == nullptr) {
    return true;
  }

  Runtime* runtime = Runtime::Current();
  instrumentation::Instrumentation* instr = runtime->GetInstrumentation();
  if (instr->InterpretOnly()) {
    return true;
  }

  if (runtime->GetClassLinker()->IsQuickToInterpreterBridge(quick_code)) {
    // Doing this check avoids doing compiled/interpreter transitions.
    return true;
  }

  if (Thread::Current()->IsForceInterpreter() ||
      Dbg::IsForcedInterpreterNeededForCalling(Thread::Current(), method)) {
    // Force the use of interpreter when it is required by the debugger.
    return true;
  }

  if (Thread::Current()->IsAsyncExceptionPending()) {
    // Force use of interpreter to handle async-exceptions
    return true;
  }

  if (quick_code == GetQuickInstrumentationEntryPoint()) {
    const void* instr_target = instr->GetCodeForInvoke(method);
    DCHECK_NE(instr_target, GetQuickInstrumentationEntryPoint()) << method->PrettyMethod();
    return ShouldUseInterpreterEntrypoint(method, instr_target);
  }

  if (runtime->IsJavaDebuggable()) {
    // For simplicity, we ignore precompiled code and go to the interpreter
    // assuming we don't already have jitted code.
    // We could look at the oat file where `quick_code` is being defined,
    // and check whether it's been compiled debuggable, but we decided to
    // only rely on the JIT for debuggable apps.
    jit::Jit* jit = Runtime::Current()->GetJit();
    return (jit == nullptr) || !jit->GetCodeCache()->ContainsPc(quick_code);
  }

  if (runtime->IsNativeDebuggable()) {
    DCHECK(runtime->UseJitCompilation() && runtime->GetJit()->JitAtFirstUse());
    // If we are doing native debugging, ignore application's AOT code,
    // since we want to JIT it (at first use) with extra stackmaps for native
    // debugging. We keep however all AOT code from the boot image,
    // since the JIT-at-first-use is blocking and would result in non-negligible
    // startup performance impact.
    return !runtime->GetHeap()->IsInBootImageOatFile(quick_code);
  }

  return false;
}

void ClassLinker::FixupStaticTrampolines(ObjPtr<mirror::Class> klass) {
  ScopedAssertNoThreadSuspension sants(__FUNCTION__);
  DCHECK(klass->IsInitialized()) << klass->PrettyDescriptor();
  if (klass->NumDirectMethods() == 0) {
    return;  // No direct methods => no static methods.
  }
  Runtime* runtime = Runtime::Current();
  if (!runtime->IsStarted()) {
    if (runtime->IsAotCompiler() || runtime->GetHeap()->HasBootImageSpace()) {
      return;  // OAT file unavailable.
    }
  }

  const DexFile& dex_file = klass->GetDexFile();
  const uint16_t class_def_idx = klass->GetDexClassDefIndex();
  CHECK_NE(class_def_idx, DexFile::kDexNoIndex16);
  ClassAccessor accessor(dex_file, class_def_idx);
  // There should always be class data if there were direct methods.
  CHECK(accessor.HasClassData()) << klass->PrettyDescriptor();
  bool has_oat_class;
  OatFile::OatClass oat_class = OatFile::FindOatClass(dex_file,
                                                      klass->GetDexClassDefIndex(),
                                                      &has_oat_class);
  // Link the code of methods skipped by LinkCode.
  for (size_t method_index = 0; method_index < accessor.NumDirectMethods(); ++method_index) {
    ArtMethod* method = klass->GetDirectMethod(method_index, image_pointer_size_);
    if (!method->IsStatic()) {
      // Only update static methods.
      continue;
    }
    const void* quick_code = nullptr;
    if (has_oat_class) {
      OatFile::OatMethod oat_method = oat_class.GetOatMethod(method_index);
      quick_code = oat_method.GetQuickCode();
    }
    // Check if we have JIT compiled code for it.
    if (quick_code == nullptr && Runtime::Current()->GetJit() != nullptr) {
      quick_code = Runtime::Current()->GetJit()->GetCodeCache()->GetZygoteSavedEntryPoint(method);
    }
    // Check whether the method is native, in which case it's generic JNI.
    if (quick_code == nullptr && method->IsNative()) {
      quick_code = GetQuickGenericJniStub();
    } else if (ShouldUseInterpreterEntrypoint(method, quick_code)) {
      // Use interpreter entry point.
      quick_code = GetQuickToInterpreterBridge();
    }
    runtime->GetInstrumentation()->UpdateMethodsCode(method, quick_code);
  }
  // Ignore virtual methods on the iterator.
}

// Does anything needed to make sure that the compiler will not generate a direct invoke to this
// method. Should only be called on non-invokable methods.
inline void EnsureThrowsInvocationError(ClassLinker* class_linker, ArtMethod* method) {
  DCHECK(method != nullptr);
  DCHECK(!method->IsInvokable());
  method->SetEntryPointFromQuickCompiledCodePtrSize(
      class_linker->GetQuickToInterpreterBridgeTrampoline(),
      class_linker->GetImagePointerSize());
}

static void LinkCode(ClassLinker* class_linker,
                     ArtMethod* method,
                     const OatFile::OatClass* oat_class,
                     uint32_t class_def_method_index) REQUIRES_SHARED(Locks::mutator_lock_) {
  ScopedAssertNoThreadSuspension sants(__FUNCTION__);
  Runtime* const runtime = Runtime::Current();
  if (runtime->IsAotCompiler()) {
    // The following code only applies to a non-compiler runtime.
    return;
  }
  // Method shouldn't have already been linked.
  DCHECK(method->GetEntryPointFromQuickCompiledCode() == nullptr);
  if (oat_class != nullptr) {
    // Every kind of method should at least get an invoke stub from the oat_method.
    // non-abstract methods also get their code pointers.
    const OatFile::OatMethod oat_method = oat_class->GetOatMethod(class_def_method_index);
    oat_method.LinkMethod(method);
  }

  // Install entry point from interpreter.
  const void* quick_code = method->GetEntryPointFromQuickCompiledCode();
  bool enter_interpreter = class_linker->ShouldUseInterpreterEntrypoint(method, quick_code);

  if (!method->IsInvokable()) {
    EnsureThrowsInvocationError(class_linker, method);
    return;
  }

  if (method->IsStatic() && !method->IsConstructor()) {
    // For static methods excluding the class initializer, install the trampoline.
    // It will be replaced by the proper entry point by ClassLinker::FixupStaticTrampolines
    // after initializing class (see ClassLinker::InitializeClass method).
    method->SetEntryPointFromQuickCompiledCode(GetQuickResolutionStub());
  } else if (quick_code == nullptr && method->IsNative()) {
    method->SetEntryPointFromQuickCompiledCode(GetQuickGenericJniStub());
  } else if (enter_interpreter) {
    // Set entry point from compiled code if there's no code or in interpreter only mode.
    method->SetEntryPointFromQuickCompiledCode(GetQuickToInterpreterBridge());
  }

  if (method->IsNative()) {
    // Unregistering restores the dlsym lookup stub.
    method->UnregisterNative();

    if (enter_interpreter || quick_code == nullptr) {
      // We have a native method here without code. Then it should have either the generic JNI
      // trampoline as entrypoint (non-static), or the resolution trampoline (static).
      // TODO: this doesn't handle all the cases where trampolines may be installed.
      const void* entry_point = method->GetEntryPointFromQuickCompiledCode();
      DCHECK(class_linker->IsQuickGenericJniStub(entry_point) ||
             class_linker->IsQuickResolutionStub(entry_point));
    }
  }
}

void ClassLinker::SetupClass(const DexFile& dex_file,
                             const dex::ClassDef& dex_class_def,
                             Handle<mirror::Class> klass,
                             ObjPtr<mirror::ClassLoader> class_loader) {
  CHECK(klass != nullptr);
  CHECK(klass->GetDexCache() != nullptr);
  CHECK_EQ(ClassStatus::kNotReady, klass->GetStatus());
  const char* descriptor = dex_file.GetClassDescriptor(dex_class_def);
  CHECK(descriptor != nullptr);

  klass->SetClass(GetClassRoot<mirror::Class>(this));
  uint32_t access_flags = dex_class_def.GetJavaAccessFlags();
  CHECK_EQ(access_flags & ~kAccJavaFlagsMask, 0U);
  klass->SetAccessFlags(access_flags);
  klass->SetClassLoader(class_loader);
  DCHECK_EQ(klass->GetPrimitiveType(), Primitive::kPrimNot);
  mirror::Class::SetStatus(klass, ClassStatus::kIdx, nullptr);

  klass->SetDexClassDefIndex(dex_file.GetIndexForClassDef(dex_class_def));
  klass->SetDexTypeIndex(dex_class_def.class_idx_);
}

LengthPrefixedArray<ArtField>* ClassLinker::AllocArtFieldArray(Thread* self,
                                                               LinearAlloc* allocator,
                                                               size_t length) {
  if (length == 0) {
    return nullptr;
  }
  // If the ArtField alignment changes, review all uses of LengthPrefixedArray<ArtField>.
  static_assert(alignof(ArtField) == 4, "ArtField alignment is expected to be 4.");
  size_t storage_size = LengthPrefixedArray<ArtField>::ComputeSize(length);
  void* array_storage = allocator->Alloc(self, storage_size);
  auto* ret = new(array_storage) LengthPrefixedArray<ArtField>(length);
  CHECK(ret != nullptr);
  std::uninitialized_fill_n(&ret->At(0), length, ArtField());
  return ret;
}

LengthPrefixedArray<ArtMethod>* ClassLinker::AllocArtMethodArray(Thread* self,
                                                                 LinearAlloc* allocator,
                                                                 size_t length) {
  if (length == 0) {
    return nullptr;
  }
  const size_t method_alignment = ArtMethod::Alignment(image_pointer_size_);
  const size_t method_size = ArtMethod::Size(image_pointer_size_);
  const size_t storage_size =
      LengthPrefixedArray<ArtMethod>::ComputeSize(length, method_size, method_alignment);
  void* array_storage = allocator->Alloc(self, storage_size);
  auto* ret = new (array_storage) LengthPrefixedArray<ArtMethod>(length);
  CHECK(ret != nullptr);
  for (size_t i = 0; i < length; ++i) {
    new(reinterpret_cast<void*>(&ret->At(i, method_size, method_alignment))) ArtMethod;
  }
  return ret;
}

LinearAlloc* ClassLinker::GetAllocatorForClassLoader(ObjPtr<mirror::ClassLoader> class_loader) {
  if (class_loader == nullptr) {
    return Runtime::Current()->GetLinearAlloc();
  }
  LinearAlloc* allocator = class_loader->GetAllocator();
  DCHECK(allocator != nullptr);
  return allocator;
}

LinearAlloc* ClassLinker::GetOrCreateAllocatorForClassLoader(ObjPtr<mirror::ClassLoader> class_loader) {
  if (class_loader == nullptr) {
    return Runtime::Current()->GetLinearAlloc();
  }
  WriterMutexLock mu(Thread::Current(), *Locks::classlinker_classes_lock_);
  LinearAlloc* allocator = class_loader->GetAllocator();
  if (allocator == nullptr) {
    RegisterClassLoader(class_loader);
    allocator = class_loader->GetAllocator();
    CHECK(allocator != nullptr);
  }
  return allocator;
}

void ClassLinker::LoadClass(Thread* self,
                            const DexFile& dex_file,
                            const dex::ClassDef& dex_class_def,
                            Handle<mirror::Class> klass) {
  ClassAccessor accessor(dex_file,
                         dex_class_def,
                         /* parse_hiddenapi_class_data= */ klass->IsBootStrapClassLoaded());
  if (!accessor.HasClassData()) {
    return;
  }
  Runtime* const runtime = Runtime::Current();
  {
    // Note: We cannot have thread suspension until the field and method arrays are setup or else
    // Class::VisitFieldRoots may miss some fields or methods.
    ScopedAssertNoThreadSuspension nts(__FUNCTION__);
    // Load static fields.
    // We allow duplicate definitions of the same field in a class_data_item
    // but ignore the repeated indexes here, b/21868015.
    LinearAlloc* const allocator = GetAllocatorForClassLoader(klass->GetClassLoader());
    LengthPrefixedArray<ArtField>* sfields = AllocArtFieldArray(self,
                                                                allocator,
                                                                accessor.NumStaticFields());
    LengthPrefixedArray<ArtField>* ifields = AllocArtFieldArray(self,
                                                                allocator,
                                                                accessor.NumInstanceFields());
    size_t num_sfields = 0u;
    size_t num_ifields = 0u;
    uint32_t last_static_field_idx = 0u;
    uint32_t last_instance_field_idx = 0u;

    // Methods
    bool has_oat_class = false;
    const OatFile::OatClass oat_class = (runtime->IsStarted() && !runtime->IsAotCompiler())
        ? OatFile::FindOatClass(dex_file, klass->GetDexClassDefIndex(), &has_oat_class)
        : OatFile::OatClass::Invalid();
    const OatFile::OatClass* oat_class_ptr = has_oat_class ? &oat_class : nullptr;
    klass->SetMethodsPtr(
        AllocArtMethodArray(self, allocator, accessor.NumMethods()),
        accessor.NumDirectMethods(),
        accessor.NumVirtualMethods());
    size_t class_def_method_index = 0;
    uint32_t last_dex_method_index = dex::kDexNoIndex;
    size_t last_class_def_method_index = 0;

    // Use the visitor since the ranged based loops are bit slower from seeking. Seeking to the
    // methods needs to decode all of the fields.
    accessor.VisitFieldsAndMethods([&](
        const ClassAccessor::Field& field) REQUIRES_SHARED(Locks::mutator_lock_) {
          uint32_t field_idx = field.GetIndex();
          DCHECK_GE(field_idx, last_static_field_idx);  // Ordering enforced by DexFileVerifier.
          if (num_sfields == 0 || LIKELY(field_idx > last_static_field_idx)) {
            LoadField(field, klass, &sfields->At(num_sfields));
            ++num_sfields;
            last_static_field_idx = field_idx;
          }
        }, [&](const ClassAccessor::Field& field) REQUIRES_SHARED(Locks::mutator_lock_) {
          uint32_t field_idx = field.GetIndex();
          DCHECK_GE(field_idx, last_instance_field_idx);  // Ordering enforced by DexFileVerifier.
          if (num_ifields == 0 || LIKELY(field_idx > last_instance_field_idx)) {
            LoadField(field, klass, &ifields->At(num_ifields));
            ++num_ifields;
            last_instance_field_idx = field_idx;
          }
        }, [&](const ClassAccessor::Method& method) REQUIRES_SHARED(Locks::mutator_lock_) {
          ArtMethod* art_method = klass->GetDirectMethodUnchecked(class_def_method_index,
              image_pointer_size_);
          LoadMethod(dex_file, method, klass, art_method);
          LinkCode(this, art_method, oat_class_ptr, class_def_method_index);
          uint32_t it_method_index = method.GetIndex();
          if (last_dex_method_index == it_method_index) {
            // duplicate case
            art_method->SetMethodIndex(last_class_def_method_index);
          } else {
            art_method->SetMethodIndex(class_def_method_index);
            last_dex_method_index = it_method_index;
            last_class_def_method_index = class_def_method_index;
          }
          ++class_def_method_index;
        }, [&](const ClassAccessor::Method& method) REQUIRES_SHARED(Locks::mutator_lock_) {
          ArtMethod* art_method = klass->GetVirtualMethodUnchecked(
              class_def_method_index - accessor.NumDirectMethods(),
              image_pointer_size_);
          LoadMethod(dex_file, method, klass, art_method);
          LinkCode(this, art_method, oat_class_ptr, class_def_method_index);
          ++class_def_method_index;
        });

    if (UNLIKELY(num_ifields + num_sfields != accessor.NumFields())) {
      LOG(WARNING) << "Duplicate fields in class " << klass->PrettyDescriptor()
          << " (unique static fields: " << num_sfields << "/" << accessor.NumStaticFields()
          << ", unique instance fields: " << num_ifields << "/" << accessor.NumInstanceFields()
          << ")";
      // NOTE: Not shrinking the over-allocated sfields/ifields, just setting size.
      if (sfields != nullptr) {
        sfields->SetSize(num_sfields);
      }
      if (ifields != nullptr) {
        ifields->SetSize(num_ifields);
      }
    }
    // Set the field arrays.
    klass->SetSFieldsPtr(sfields);
    DCHECK_EQ(klass->NumStaticFields(), num_sfields);
    klass->SetIFieldsPtr(ifields);
    DCHECK_EQ(klass->NumInstanceFields(), num_ifields);
  }
  // Ensure that the card is marked so that remembered sets pick up native roots.
  WriteBarrier::ForEveryFieldWrite(klass.Get());
  self->AllowThreadSuspension();
}

void ClassLinker::LoadField(const ClassAccessor::Field& field,
                            Handle<mirror::Class> klass,
                            ArtField* dst) {
  const uint32_t field_idx = field.GetIndex();
  dst->SetDexFieldIndex(field_idx);
  dst->SetDeclaringClass(klass.Get());

  // Get access flags from the DexFile and set hiddenapi runtime access flags.
  dst->SetAccessFlags(field.GetAccessFlags() | hiddenapi::CreateRuntimeFlags(field));
}

void ClassLinker::LoadMethod(const DexFile& dex_file,
                             const ClassAccessor::Method& method,
                             Handle<mirror::Class> klass,
                             ArtMethod* dst) {
  const uint32_t dex_method_idx = method.GetIndex();
  const dex::MethodId& method_id = dex_file.GetMethodId(dex_method_idx);
  const char* method_name = dex_file.StringDataByIdx(method_id.name_idx_);

  ScopedAssertNoThreadSuspension ants("LoadMethod");
  dst->SetDexMethodIndex(dex_method_idx);
  dst->SetDeclaringClass(klass.Get());
  dst->SetCodeItemOffset(method.GetCodeItemOffset());

  // Get access flags from the DexFile and set hiddenapi runtime access flags.
  uint32_t access_flags = method.GetAccessFlags() | hiddenapi::CreateRuntimeFlags(method);

  if (UNLIKELY(strcmp("finalize", method_name) == 0)) {
    // Set finalizable flag on declaring class.
    if (strcmp("V", dex_file.GetShorty(method_id.proto_idx_)) == 0) {
      // Void return type.
      if (klass->GetClassLoader() != nullptr) {  // All non-boot finalizer methods are flagged.
        klass->SetFinalizable();
      } else {
        std::string temp;
        const char* klass_descriptor = klass->GetDescriptor(&temp);
        // The Enum class declares a "final" finalize() method to prevent subclasses from
        // introducing a finalizer. We don't want to set the finalizable flag for Enum or its
        // subclasses, so we exclude it here.
        // We also want to avoid setting the flag on Object, where we know that finalize() is
        // empty.
        if (strcmp(klass_descriptor, "Ljava/lang/Object;") != 0 &&
            strcmp(klass_descriptor, "Ljava/lang/Enum;") != 0) {
          klass->SetFinalizable();
        }
      }
    }
  } else if (method_name[0] == '<') {
    // Fix broken access flags for initializers. Bug 11157540.
    bool is_init = (strcmp("<init>", method_name) == 0);
    bool is_clinit = !is_init && (strcmp("<clinit>", method_name) == 0);
    if (UNLIKELY(!is_init && !is_clinit)) {
      LOG(WARNING) << "Unexpected '<' at start of method name " << method_name;
    } else {
      if (UNLIKELY((access_flags & kAccConstructor) == 0)) {
        LOG(WARNING) << method_name << " didn't have expected constructor access flag in class "
            << klass->PrettyDescriptor() << " in dex file " << dex_file.GetLocation();
        access_flags |= kAccConstructor;
      }
    }
  }
  if (UNLIKELY((access_flags & kAccNative) != 0u)) {
    // Check if the native method is annotated with @FastNative or @CriticalNative.
    access_flags |= annotations::GetNativeMethodAnnotationAccessFlags(
        dex_file, dst->GetClassDef(), dex_method_idx);
  }
  dst->SetAccessFlags(access_flags);
  // Must be done after SetAccessFlags since IsAbstract depends on it.
  if (klass->IsInterface() && dst->IsAbstract()) {
    dst->CalculateAndSetImtIndex();
  }
}

void ClassLinker::AppendToBootClassPath(Thread* self, const DexFile& dex_file) {
  ObjPtr<mirror::DexCache> dex_cache = AllocAndInitializeDexCache(
      self,
      dex_file,
      Runtime::Current()->GetLinearAlloc());
  CHECK(dex_cache != nullptr) << "Failed to allocate dex cache for " << dex_file.GetLocation();
  AppendToBootClassPath(dex_file, dex_cache);
}

void ClassLinker::AppendToBootClassPath(const DexFile& dex_file,
                                        ObjPtr<mirror::DexCache> dex_cache) {
  CHECK(dex_cache != nullptr) << dex_file.GetLocation();
  boot_class_path_.push_back(&dex_file);
  WriterMutexLock mu(Thread::Current(), *Locks::dex_lock_);
  RegisterDexFileLocked(dex_file, dex_cache, /* class_loader= */ nullptr);
}

void ClassLinker::RegisterDexFileLocked(const DexFile& dex_file,
                                        ObjPtr<mirror::DexCache> dex_cache,
                                        ObjPtr<mirror::ClassLoader> class_loader) {
  Thread* const self = Thread::Current();
  Locks::dex_lock_->AssertExclusiveHeld(self);
  CHECK(dex_cache != nullptr) << dex_file.GetLocation();
  // For app images, the dex cache location may be a suffix of the dex file location since the
  // dex file location is an absolute path.
  const std::string dex_cache_location = dex_cache->GetLocation()->ToModifiedUtf8();
  const size_t dex_cache_length = dex_cache_location.length();
  CHECK_GT(dex_cache_length, 0u) << dex_file.GetLocation();
  std::string dex_file_location = dex_file.GetLocation();
  // The following paths checks don't work on preopt when using boot dex files, where the dex
  // cache location is the one on device, and the dex_file's location is the one on host.
  if (!(Runtime::Current()->IsAotCompiler() && class_loader == nullptr && !kIsTargetBuild)) {
    CHECK_GE(dex_file_location.length(), dex_cache_length)
        << dex_cache_location << " " << dex_file.GetLocation();
    const std::string dex_file_suffix = dex_file_location.substr(
        dex_file_location.length() - dex_cache_length,
        dex_cache_length);
    // Example dex_cache location is SettingsProvider.apk and
    // dex file location is /system/priv-app/SettingsProvider/SettingsProvider.apk
    CHECK_EQ(dex_cache_location, dex_file_suffix);
  }
  const OatFile* oat_file =
      (dex_file.GetOatDexFile() != nullptr) ? dex_file.GetOatDexFile()->GetOatFile() : nullptr;
  // Clean up pass to remove null dex caches; null dex caches can occur due to class unloading
  // and we are lazily removing null entries. Also check if we need to initialize OatFile data
  // (.data.bimg.rel.ro and .bss sections) needed for code execution.
  bool initialize_oat_file_data = (oat_file != nullptr) && oat_file->IsExecutable();
  JavaVMExt* const vm = self->GetJniEnv()->GetVm();
  for (auto it = dex_caches_.begin(); it != dex_caches_.end(); ) {
    DexCacheData data = *it;
    if (self->IsJWeakCleared(data.weak_root)) {
      vm->DeleteWeakGlobalRef(self, data.weak_root);
      it = dex_caches_.erase(it);
    } else {
      if (initialize_oat_file_data &&
          it->dex_file->GetOatDexFile() != nullptr &&
          it->dex_file->GetOatDexFile()->GetOatFile() == oat_file) {
        initialize_oat_file_data = false;  // Already initialized.
      }
      ++it;
    }
  }
  if (initialize_oat_file_data) {
    oat_file->InitializeRelocations();
  }
  // Let hiddenapi assign a domain to the newly registered dex file.
  hiddenapi::InitializeDexFileDomain(dex_file, class_loader);

  jweak dex_cache_jweak = vm->AddWeakGlobalRef(self, dex_cache);
  dex_cache->SetDexFile(&dex_file);
  DexCacheData data;
  data.weak_root = dex_cache_jweak;
  data.dex_file = dex_cache->GetDexFile();
  data.class_table = ClassTableForClassLoader(class_loader);
  AddNativeDebugInfoForDex(self, data.dex_file);
  DCHECK(data.class_table != nullptr);
  // Make sure to hold the dex cache live in the class table. This case happens for the boot class
  // path dex caches without an image.
  data.class_table->InsertStrongRoot(dex_cache);
  if (class_loader != nullptr) {
    // Since we added a strong root to the class table, do the write barrier as required for
    // remembered sets and generational GCs.
    WriteBarrier::ForEveryFieldWrite(class_loader);
  }
  dex_caches_.push_back(data);
}

ObjPtr<mirror::DexCache> ClassLinker::DecodeDexCache(Thread* self, const DexCacheData& data) {
  return data.IsValid()
      ? ObjPtr<mirror::DexCache>::DownCast(self->DecodeJObject(data.weak_root))
      : nullptr;
}

ObjPtr<mirror::DexCache> ClassLinker::EnsureSameClassLoader(
    Thread* self,
    ObjPtr<mirror::DexCache> dex_cache,
    const DexCacheData& data,
    ObjPtr<mirror::ClassLoader> class_loader) {
  DCHECK_EQ(dex_cache->GetDexFile(), data.dex_file);
  if (data.class_table != ClassTableForClassLoader(class_loader)) {
    self->ThrowNewExceptionF("Ljava/lang/InternalError;",
                             "Attempt to register dex file %s with multiple class loaders",
                             data.dex_file->GetLocation().c_str());
    return nullptr;
  }
  return dex_cache;
}

void ClassLinker::RegisterExistingDexCache(ObjPtr<mirror::DexCache> dex_cache,
                                           ObjPtr<mirror::ClassLoader> class_loader) {
  SCOPED_TRACE << __FUNCTION__ << " " << dex_cache->GetDexFile()->GetLocation();
  Thread* self = Thread::Current();
  StackHandleScope<2> hs(self);
  Handle<mirror::DexCache> h_dex_cache(hs.NewHandle(dex_cache));
  Handle<mirror::ClassLoader> h_class_loader(hs.NewHandle(class_loader));
  const DexFile* dex_file = dex_cache->GetDexFile();
  DCHECK(dex_file != nullptr) << "Attempt to register uninitialized dex_cache object!";
  if (kIsDebugBuild) {
    DexCacheData old_data;
    {
      ReaderMutexLock mu(self, *Locks::dex_lock_);
      old_data = FindDexCacheDataLocked(*dex_file);
    }
    ObjPtr<mirror::DexCache> old_dex_cache = DecodeDexCache(self, old_data);
    DCHECK(old_dex_cache.IsNull()) << "Attempt to manually register a dex cache thats already "
                                   << "been registered on dex file " << dex_file->GetLocation();
  }
  ClassTable* table;
  {
    WriterMutexLock mu(self, *Locks::classlinker_classes_lock_);
    table = InsertClassTableForClassLoader(h_class_loader.Get());
  }
  // Avoid a deadlock between a garbage collecting thread running a checkpoint,
  // a thread holding the dex lock and blocking on a condition variable regarding
  // weak references access, and a thread blocking on the dex lock.
  gc::ScopedGCCriticalSection gcs(self, gc::kGcCauseClassLinker, gc::kCollectorTypeClassLinker);
  WriterMutexLock mu(self, *Locks::dex_lock_);
  RegisterDexFileLocked(*dex_file, h_dex_cache.Get(), h_class_loader.Get());
  table->InsertStrongRoot(h_dex_cache.Get());
  if (h_class_loader.Get() != nullptr) {
    // Since we added a strong root to the class table, do the write barrier as required for
    // remembered sets and generational GCs.
    WriteBarrier::ForEveryFieldWrite(h_class_loader.Get());
  }
}

ObjPtr<mirror::DexCache> ClassLinker::RegisterDexFile(const DexFile& dex_file,
                                                      ObjPtr<mirror::ClassLoader> class_loader) {
  Thread* self = Thread::Current();
  DexCacheData old_data;
  {
    ReaderMutexLock mu(self, *Locks::dex_lock_);
    old_data = FindDexCacheDataLocked(dex_file);
  }
  ObjPtr<mirror::DexCache> old_dex_cache = DecodeDexCache(self, old_data);
  if (old_dex_cache != nullptr) {
    return EnsureSameClassLoader(self, old_dex_cache, old_data, class_loader);
  }
  SCOPED_TRACE << __FUNCTION__ << " " << dex_file.GetLocation();
  LinearAlloc* const linear_alloc = GetOrCreateAllocatorForClassLoader(class_loader);
  DCHECK(linear_alloc != nullptr);
  ClassTable* table;
  {
    WriterMutexLock mu(self, *Locks::classlinker_classes_lock_);
    table = InsertClassTableForClassLoader(class_loader);
  }
  // Don't alloc while holding the lock, since allocation may need to
  // suspend all threads and another thread may need the dex_lock_ to
  // get to a suspend point.
  StackHandleScope<3> hs(self);
  Handle<mirror::ClassLoader> h_class_loader(hs.NewHandle(class_loader));
  ObjPtr<mirror::String> location;
  Handle<mirror::DexCache> h_dex_cache(hs.NewHandle(AllocDexCache(/*out*/&location,
                                                                  self,
                                                                  dex_file)));
  Handle<mirror::String> h_location(hs.NewHandle(location));
  {
    // Avoid a deadlock between a garbage collecting thread running a checkpoint,
    // a thread holding the dex lock and blocking on a condition variable regarding
    // weak references access, and a thread blocking on the dex lock.
    gc::ScopedGCCriticalSection gcs(self, gc::kGcCauseClassLinker, gc::kCollectorTypeClassLinker);
    WriterMutexLock mu(self, *Locks::dex_lock_);
    old_data = FindDexCacheDataLocked(dex_file);
    old_dex_cache = DecodeDexCache(self, old_data);
    if (old_dex_cache == nullptr && h_dex_cache != nullptr) {
      // Do InitializeDexCache while holding dex lock to make sure two threads don't call it at the
      // same time with the same dex cache. Since the .bss is shared this can cause failing DCHECK
      // that the arrays are null.
      mirror::DexCache::InitializeDexCache(self,
                                           h_dex_cache.Get(),
                                           h_location.Get(),
                                           &dex_file,
                                           linear_alloc,
                                           image_pointer_size_);
      RegisterDexFileLocked(dex_file, h_dex_cache.Get(), h_class_loader.Get());
    }
  }
  if (old_dex_cache != nullptr) {
    // Another thread managed to initialize the dex cache faster, so use that DexCache.
    // If this thread encountered OOME, ignore it.
    DCHECK_EQ(h_dex_cache == nullptr, self->IsExceptionPending());
    self->ClearException();
    // We cannot call EnsureSameClassLoader() while holding the dex_lock_.
    return EnsureSameClassLoader(self, old_dex_cache, old_data, h_class_loader.Get());
  }
  if (h_dex_cache == nullptr) {
    self->AssertPendingOOMException();
    return nullptr;
  }
  table->InsertStrongRoot(h_dex_cache.Get());
  if (h_class_loader.Get() != nullptr) {
    // Since we added a strong root to the class table, do the write barrier as required for
    // remembered sets and generational GCs.
    WriteBarrier::ForEveryFieldWrite(h_class_loader.Get());
  }
  return h_dex_cache.Get();
}

bool ClassLinker::IsDexFileRegistered(Thread* self, const DexFile& dex_file) {
  ReaderMutexLock mu(self, *Locks::dex_lock_);
  return DecodeDexCache(self, FindDexCacheDataLocked(dex_file)) != nullptr;
}

ObjPtr<mirror::DexCache> ClassLinker::FindDexCache(Thread* self, const DexFile& dex_file) {
  ReaderMutexLock mu(self, *Locks::dex_lock_);
  DexCacheData dex_cache_data = FindDexCacheDataLocked(dex_file);
  ObjPtr<mirror::DexCache> dex_cache = DecodeDexCache(self, dex_cache_data);
  if (dex_cache != nullptr) {
    return dex_cache;
  }
  // Failure, dump diagnostic and abort.
  for (const DexCacheData& data : dex_caches_) {
    if (DecodeDexCache(self, data) != nullptr) {
      LOG(FATAL_WITHOUT_ABORT) << "Registered dex file " << data.dex_file->GetLocation();
    }
  }
  LOG(FATAL) << "Failed to find DexCache for DexFile " << dex_file.GetLocation()
             << " " << &dex_file << " " << dex_cache_data.dex_file;
  UNREACHABLE();
}

ClassTable* ClassLinker::FindClassTable(Thread* self, ObjPtr<mirror::DexCache> dex_cache) {
  const DexFile* dex_file = dex_cache->GetDexFile();
  DCHECK(dex_file != nullptr);
  ReaderMutexLock mu(self, *Locks::dex_lock_);
  // Search assuming unique-ness of dex file.
  for (const DexCacheData& data : dex_caches_) {
    // Avoid decoding (and read barriers) other unrelated dex caches.
    if (data.dex_file == dex_file) {
      ObjPtr<mirror::DexCache> registered_dex_cache = DecodeDexCache(self, data);
      if (registered_dex_cache != nullptr) {
        CHECK_EQ(registered_dex_cache, dex_cache) << dex_file->GetLocation();
        return data.class_table;
      }
    }
  }
  return nullptr;
}

ClassLinker::DexCacheData ClassLinker::FindDexCacheDataLocked(const DexFile& dex_file) {
  // Search assuming unique-ness of dex file.
  for (const DexCacheData& data : dex_caches_) {
    // Avoid decoding (and read barriers) other unrelated dex caches.
    if (data.dex_file == &dex_file) {
      return data;
    }
  }
  return DexCacheData();
}

ObjPtr<mirror::Class> ClassLinker::CreatePrimitiveClass(Thread* self, Primitive::Type type) {
  ObjPtr<mirror::Class> primitive_class =
      AllocClass(self, mirror::Class::PrimitiveClassSize(image_pointer_size_));
  if (UNLIKELY(primitive_class == nullptr)) {
    self->AssertPendingOOMException();
    return nullptr;
  }
  // Must hold lock on object when initializing.
  StackHandleScope<1> hs(self);
  Handle<mirror::Class> h_class(hs.NewHandle(primitive_class));
  ObjectLock<mirror::Class> lock(self, h_class);
  h_class->SetAccessFlags(kAccPublic | kAccFinal | kAccAbstract);
  h_class->SetPrimitiveType(type);
  h_class->SetIfTable(GetClassRoot<mirror::Object>(this)->GetIfTable());
  EnsureSkipAccessChecksMethods</* kNeedsVerified= */ true>(h_class, image_pointer_size_);
  mirror::Class::SetStatus(h_class, ClassStatus::kInitialized, self);
  const char* descriptor = Primitive::Descriptor(type);
  ObjPtr<mirror::Class> existing = InsertClass(descriptor,
                                               h_class.Get(),
                                               ComputeModifiedUtf8Hash(descriptor));
  CHECK(existing == nullptr) << "InitPrimitiveClass(" << type << ") failed";
  return h_class.Get();
}

inline ObjPtr<mirror::IfTable> ClassLinker::GetArrayIfTable() {
  return GetClassRoot<mirror::ObjectArray<mirror::Object>>(this)->GetIfTable();
}

// Create an array class (i.e. the class object for the array, not the
// array itself).  "descriptor" looks like "[C" or "[[[[B" or
// "[Ljava/lang/String;".
//
// If "descriptor" refers to an array of primitives, look up the
// primitive type's internally-generated class object.
//
// "class_loader" is the class loader of the class that's referring to
// us.  It's used to ensure that we're looking for the element type in
// the right context.  It does NOT become the class loader for the
// array class; that always comes from the base element class.
//
// Returns null with an exception raised on failure.
ObjPtr<mirror::Class> ClassLinker::CreateArrayClass(Thread* self,
                                                    const char* descriptor,
                                                    size_t hash,
                                                    Handle<mirror::ClassLoader> class_loader) {
  // Identify the underlying component type
  CHECK_EQ('[', descriptor[0]);
  StackHandleScope<2> hs(self);

  // This is to prevent the calls to ClassLoad and ClassPrepare which can cause java/user-supplied
  // code to be executed. We put it up here so we can avoid all the allocations associated with
  // creating the class. This can happen with (eg) jit threads.
  if (!self->CanLoadClasses()) {
    // Make sure we don't try to load anything, potentially causing an infinite loop.
    ObjPtr<mirror::Throwable> pre_allocated =
        Runtime::Current()->GetPreAllocatedNoClassDefFoundError();
    self->SetException(pre_allocated);
    return nullptr;
  }

  MutableHandle<mirror::Class> component_type(hs.NewHandle(FindClass(self, descriptor + 1,
                                                                     class_loader)));
  if (component_type == nullptr) {
    DCHECK(self->IsExceptionPending());
    // We need to accept erroneous classes as component types.
    const size_t component_hash = ComputeModifiedUtf8Hash(descriptor + 1);
    component_type.Assign(LookupClass(self, descriptor + 1, component_hash, class_loader.Get()));
    if (component_type == nullptr) {
      DCHECK(self->IsExceptionPending());
      return nullptr;
    } else {
      self->ClearException();
    }
  }
  if (UNLIKELY(component_type->IsPrimitiveVoid())) {
    ThrowNoClassDefFoundError("Attempt to create array of void primitive type");
    return nullptr;
  }
  // See if the component type is already loaded.  Array classes are
  // always associated with the class loader of their underlying
  // element type -- an array of Strings goes with the loader for
  // java/lang/String -- so we need to look for it there.  (The
  // caller should have checked for the existence of the class
  // before calling here, but they did so with *their* class loader,
  // not the component type's loader.)
  //
  // If we find it, the caller adds "loader" to the class' initiating
  // loader list, which should prevent us from going through this again.
  //
  // This call is unnecessary if "loader" and "component_type->GetClassLoader()"
  // are the same, because our caller (FindClass) just did the
  // lookup.  (Even if we get this wrong we still have correct behavior,
  // because we effectively do this lookup again when we add the new
  // class to the hash table --- necessary because of possible races with
  // other threads.)
  if (class_loader.Get() != component_type->GetClassLoader()) {
    ObjPtr<mirror::Class> new_class =
        LookupClass(self, descriptor, hash, component_type->GetClassLoader());
    if (new_class != nullptr) {
      return new_class;
    }
  }

  // Fill out the fields in the Class.
  //
  // It is possible to execute some methods against arrays, because
  // all arrays are subclasses of java_lang_Object_, so we need to set
  // up a vtable.  We can just point at the one in java_lang_Object_.
  //
  // Array classes are simple enough that we don't need to do a full
  // link step.
  auto new_class = hs.NewHandle<mirror::Class>(nullptr);
  if (UNLIKELY(!init_done_)) {
    // Classes that were hand created, ie not by FindSystemClass
    if (strcmp(descriptor, "[Ljava/lang/Class;") == 0) {
      new_class.Assign(GetClassRoot<mirror::ObjectArray<mirror::Class>>(this));
    } else if (strcmp(descriptor, "[Ljava/lang/Object;") == 0) {
      new_class.Assign(GetClassRoot<mirror::ObjectArray<mirror::Object>>(this));
    } else if (strcmp(descriptor, "[Ljava/lang/String;") == 0) {
      new_class.Assign(GetClassRoot<mirror::ObjectArray<mirror::String>>(this));
    } else if (strcmp(descriptor, "[Z") == 0) {
      new_class.Assign(GetClassRoot<mirror::BooleanArray>(this));
    } else if (strcmp(descriptor, "[B") == 0) {
      new_class.Assign(GetClassRoot<mirror::ByteArray>(this));
    } else if (strcmp(descriptor, "[C") == 0) {
      new_class.Assign(GetClassRoot<mirror::CharArray>(this));
    } else if (strcmp(descriptor, "[S") == 0) {
      new_class.Assign(GetClassRoot<mirror::ShortArray>(this));
    } else if (strcmp(descriptor, "[I") == 0) {
      new_class.Assign(GetClassRoot<mirror::IntArray>(this));
    } else if (strcmp(descriptor, "[J") == 0) {
      new_class.Assign(GetClassRoot<mirror::LongArray>(this));
    } else if (strcmp(descriptor, "[F") == 0) {
      new_class.Assign(GetClassRoot<mirror::FloatArray>(this));
    } else if (strcmp(descriptor, "[D") == 0) {
      new_class.Assign(GetClassRoot<mirror::DoubleArray>(this));
    }
  }
  if (new_class == nullptr) {
    new_class.Assign(AllocClass(self, mirror::Array::ClassSize(image_pointer_size_)));
    if (new_class == nullptr) {
      self->AssertPendingOOMException();
      return nullptr;
    }
    new_class->SetComponentType(component_type.Get());
  }
  ObjectLock<mirror::Class> lock(self, new_class);  // Must hold lock on object when initializing.
  DCHECK(new_class->GetComponentType() != nullptr);
  ObjPtr<mirror::Class> java_lang_Object = GetClassRoot<mirror::Object>(this);
  new_class->SetSuperClass(java_lang_Object);
  new_class->SetVTable(java_lang_Object->GetVTable());
  new_class->SetPrimitiveType(Primitive::kPrimNot);
  new_class->SetClassLoader(component_type->GetClassLoader());
  if (component_type->IsPrimitive()) {
    new_class->SetClassFlags(mirror::kClassFlagNoReferenceFields);
  } else {
    new_class->SetClassFlags(mirror::kClassFlagObjectArray);
  }
  mirror::Class::SetStatus(new_class, ClassStatus::kLoaded, self);
  new_class->PopulateEmbeddedVTable(image_pointer_size_);
  ImTable* object_imt = java_lang_Object->GetImt(image_pointer_size_);
  new_class->SetImt(object_imt, image_pointer_size_);
  EnsureSkipAccessChecksMethods</* kNeedsVerified= */ true>(new_class, image_pointer_size_);
  mirror::Class::SetStatus(new_class, ClassStatus::kInitialized, self);
  // don't need to set new_class->SetObjectSize(..)
  // because Object::SizeOf delegates to Array::SizeOf

  // All arrays have java/lang/Cloneable and java/io/Serializable as
  // interfaces.  We need to set that up here, so that stuff like
  // "instanceof" works right.
  //
  // Note: The GC could run during the call to FindSystemClass,
  // so we need to make sure the class object is GC-valid while we're in
  // there.  Do this by clearing the interface list so the GC will just
  // think that the entries are null.


  // Use the single, global copies of "interfaces" and "iftable"
  // (remember not to free them for arrays).
  {
    ObjPtr<mirror::IfTable> array_iftable = GetArrayIfTable();
    CHECK(array_iftable != nullptr);
    new_class->SetIfTable(array_iftable);
  }

  // Inherit access flags from the component type.
  int access_flags = new_class->GetComponentType()->GetAccessFlags();
  // Lose any implementation detail flags; in particular, arrays aren't finalizable.
  access_flags &= kAccJavaFlagsMask;
  // Arrays can't be used as a superclass or interface, so we want to add "abstract final"
  // and remove "interface".
  access_flags |= kAccAbstract | kAccFinal;
  access_flags &= ~kAccInterface;
  // Arrays are access-checks-clean and preverified.
  access_flags |= kAccVerificationAttempted;

  new_class->SetAccessFlags(access_flags);

  ObjPtr<mirror::Class> existing = InsertClass(descriptor, new_class.Get(), hash);
  if (existing == nullptr) {
    // We postpone ClassLoad and ClassPrepare events to this point in time to avoid
    // duplicate events in case of races. Array classes don't really follow dedicated
    // load and prepare, anyways.
    Runtime::Current()->GetRuntimeCallbacks()->ClassLoad(new_class);
    Runtime::Current()->GetRuntimeCallbacks()->ClassPrepare(new_class, new_class);

    jit::Jit::NewTypeLoadedIfUsingJit(new_class.Get());
    return new_class.Get();
  }
  // Another thread must have loaded the class after we
  // started but before we finished.  Abandon what we've
  // done.
  //
  // (Yes, this happens.)

  return existing;
}

ObjPtr<mirror::Class> ClassLinker::LookupPrimitiveClass(char type) {
  ClassRoot class_root;
  switch (type) {
    case 'B': class_root = ClassRoot::kPrimitiveByte; break;
    case 'C': class_root = ClassRoot::kPrimitiveChar; break;
    case 'D': class_root = ClassRoot::kPrimitiveDouble; break;
    case 'F': class_root = ClassRoot::kPrimitiveFloat; break;
    case 'I': class_root = ClassRoot::kPrimitiveInt; break;
    case 'J': class_root = ClassRoot::kPrimitiveLong; break;
    case 'S': class_root = ClassRoot::kPrimitiveShort; break;
    case 'Z': class_root = ClassRoot::kPrimitiveBoolean; break;
    case 'V': class_root = ClassRoot::kPrimitiveVoid; break;
    default:
      return nullptr;
  }
  return GetClassRoot(class_root, this);
}

ObjPtr<mirror::Class> ClassLinker::FindPrimitiveClass(char type) {
  ObjPtr<mirror::Class> result = LookupPrimitiveClass(type);
  if (UNLIKELY(result == nullptr)) {
    std::string printable_type(PrintableChar(type));
    ThrowNoClassDefFoundError("Not a primitive type: %s", printable_type.c_str());
  }
  return result;
}

ObjPtr<mirror::Class> ClassLinker::InsertClass(const char* descriptor,
                                               ObjPtr<mirror::Class> klass,
                                               size_t hash) {
  DCHECK(Thread::Current()->CanLoadClasses());
  if (VLOG_IS_ON(class_linker)) {
    ObjPtr<mirror::DexCache> dex_cache = klass->GetDexCache();
    std::string source;
    if (dex_cache != nullptr) {
      source += " from ";
      source += dex_cache->GetLocation()->ToModifiedUtf8();
    }
    LOG(INFO) << "Loaded class " << descriptor << source;
  }
  {
    WriterMutexLock mu(Thread::Current(), *Locks::classlinker_classes_lock_);
    const ObjPtr<mirror::ClassLoader> class_loader = klass->GetClassLoader();
    ClassTable* const class_table = InsertClassTableForClassLoader(class_loader);
    ObjPtr<mirror::Class> existing = class_table->Lookup(descriptor, hash);
    if (existing != nullptr) {
      return existing;
    }
    VerifyObject(klass);
    class_table->InsertWithHash(klass, hash);
    if (class_loader != nullptr) {
      // This is necessary because we need to have the card dirtied for remembered sets.
      WriteBarrier::ForEveryFieldWrite(class_loader);
    }
    if (log_new_roots_) {
      new_class_roots_.push_back(GcRoot<mirror::Class>(klass));
    }
  }
  if (kIsDebugBuild) {
    // Test that copied methods correctly can find their holder.
    for (ArtMethod& method : klass->GetCopiedMethods(image_pointer_size_)) {
      CHECK_EQ(GetHoldingClassOfCopiedMethod(&method), klass);
    }
  }
  return nullptr;
}

void ClassLinker::WriteBarrierForBootOatFileBssRoots(const OatFile* oat_file) {
  WriterMutexLock mu(Thread::Current(), *Locks::classlinker_classes_lock_);
  DCHECK(!oat_file->GetBssGcRoots().empty()) << oat_file->GetLocation();
  if (log_new_roots_ && !ContainsElement(new_bss_roots_boot_oat_files_, oat_file)) {
    new_bss_roots_boot_oat_files_.push_back(oat_file);
  }
}

// TODO This should really be in mirror::Class.
void ClassLinker::UpdateClassMethods(ObjPtr<mirror::Class> klass,
                                     LengthPrefixedArray<ArtMethod>* new_methods) {
  klass->SetMethodsPtrUnchecked(new_methods,
                                klass->NumDirectMethods(),
                                klass->NumDeclaredVirtualMethods());
  // Need to mark the card so that the remembered sets and mod union tables get updated.
  WriteBarrier::ForEveryFieldWrite(klass);
}

ObjPtr<mirror::Class> ClassLinker::LookupClass(Thread* self,
                                               const char* descriptor,
                                               ObjPtr<mirror::ClassLoader> class_loader) {
  return LookupClass(self, descriptor, ComputeModifiedUtf8Hash(descriptor), class_loader);
}

ObjPtr<mirror::Class> ClassLinker::LookupClass(Thread* self,
                                               const char* descriptor,
                                               size_t hash,
                                               ObjPtr<mirror::ClassLoader> class_loader) {
  ReaderMutexLock mu(self, *Locks::classlinker_classes_lock_);
  ClassTable* const class_table = ClassTableForClassLoader(class_loader);
  if (class_table != nullptr) {
    ObjPtr<mirror::Class> result = class_table->Lookup(descriptor, hash);
    if (result != nullptr) {
      return result;
    }
  }
  return nullptr;
}

class MoveClassTableToPreZygoteVisitor : public ClassLoaderVisitor {
 public:
  MoveClassTableToPreZygoteVisitor() {}

  void Visit(ObjPtr<mirror::ClassLoader> class_loader)
      REQUIRES(Locks::classlinker_classes_lock_)
      REQUIRES_SHARED(Locks::mutator_lock_) override {
    ClassTable* const class_table = class_loader->GetClassTable();
    if (class_table != nullptr) {
      class_table->FreezeSnapshot();
    }
  }
};

void ClassLinker::MoveClassTableToPreZygote() {
  WriterMutexLock mu(Thread::Current(), *Locks::classlinker_classes_lock_);
  boot_class_table_->FreezeSnapshot();
  MoveClassTableToPreZygoteVisitor visitor;
  VisitClassLoaders(&visitor);
}

// Look up classes by hash and descriptor and put all matching ones in the result array.
class LookupClassesVisitor : public ClassLoaderVisitor {
 public:
  LookupClassesVisitor(const char* descriptor,
                       size_t hash,
                       std::vector<ObjPtr<mirror::Class>>* result)
     : descriptor_(descriptor),
       hash_(hash),
       result_(result) {}

  void Visit(ObjPtr<mirror::ClassLoader> class_loader)
      REQUIRES_SHARED(Locks::classlinker_classes_lock_, Locks::mutator_lock_) override {
    ClassTable* const class_table = class_loader->GetClassTable();
    ObjPtr<mirror::Class> klass = class_table->Lookup(descriptor_, hash_);
    // Add `klass` only if `class_loader` is its defining (not just initiating) class loader.
    if (klass != nullptr && klass->GetClassLoader() == class_loader) {
      result_->push_back(klass);
    }
  }

 private:
  const char* const descriptor_;
  const size_t hash_;
  std::vector<ObjPtr<mirror::Class>>* const result_;
};

void ClassLinker::LookupClasses(const char* descriptor,
                                std::vector<ObjPtr<mirror::Class>>& result) {
  result.clear();
  Thread* const self = Thread::Current();
  ReaderMutexLock mu(self, *Locks::classlinker_classes_lock_);
  const size_t hash = ComputeModifiedUtf8Hash(descriptor);
  ObjPtr<mirror::Class> klass = boot_class_table_->Lookup(descriptor, hash);
  if (klass != nullptr) {
    DCHECK(klass->GetClassLoader() == nullptr);
    result.push_back(klass);
  }
  LookupClassesVisitor visitor(descriptor, hash, &result);
  VisitClassLoaders(&visitor);
}

bool ClassLinker::AttemptSupertypeVerification(Thread* self,
                                               Handle<mirror::Class> klass,
                                               Handle<mirror::Class> supertype) {
  DCHECK(self != nullptr);
  DCHECK(klass != nullptr);
  DCHECK(supertype != nullptr);

  if (!supertype->IsVerified() && !supertype->IsErroneous()) {
    VerifyClass(self, supertype);
  }

  if (supertype->IsVerified() || supertype->ShouldVerifyAtRuntime()) {
    // The supertype is either verified, or we soft failed at AOT time.
    DCHECK(supertype->IsVerified() || Runtime::Current()->IsAotCompiler());
    return true;
  }
  // If we got this far then we have a hard failure.
  std::string error_msg =
      StringPrintf("Rejecting class %s that attempts to sub-type erroneous class %s",
                   klass->PrettyDescriptor().c_str(),
                   supertype->PrettyDescriptor().c_str());
  LOG(WARNING) << error_msg  << " in " << klass->GetDexCache()->GetLocation()->ToModifiedUtf8();
  StackHandleScope<1> hs(self);
  Handle<mirror::Throwable> cause(hs.NewHandle(self->GetException()));
  if (cause != nullptr) {
    // Set during VerifyClass call (if at all).
    self->ClearException();
  }
  // Change into a verify error.
  ThrowVerifyError(klass.Get(), "%s", error_msg.c_str());
  if (cause != nullptr) {
    self->GetException()->SetCause(cause.Get());
  }
  ClassReference ref(klass->GetDexCache()->GetDexFile(), klass->GetDexClassDefIndex());
  if (Runtime::Current()->IsAotCompiler()) {
    Runtime::Current()->GetCompilerCallbacks()->ClassRejected(ref);
  }
  // Need to grab the lock to change status.
  ObjectLock<mirror::Class> super_lock(self, klass);
  mirror::Class::SetStatus(klass, ClassStatus::kErrorResolved, self);
  return false;
}

verifier::FailureKind ClassLinker::VerifyClass(
    Thread* self, Handle<mirror::Class> klass, verifier::HardFailLogMode log_level) {
  {
    // TODO: assert that the monitor on the Class is held
    ObjectLock<mirror::Class> lock(self, klass);

    // Is somebody verifying this now?
    ClassStatus old_status = klass->GetStatus();
    while (old_status == ClassStatus::kVerifying ||
        old_status == ClassStatus::kVerifyingAtRuntime) {
      lock.WaitIgnoringInterrupts();
      // WaitIgnoringInterrupts can still receive an interrupt and return early, in this
      // case we may see the same status again. b/62912904. This is why the check is
      // greater or equal.
      CHECK(klass->IsErroneous() || (klass->GetStatus() >= old_status))
          << "Class '" << klass->PrettyClass()
          << "' performed an illegal verification state transition from " << old_status
          << " to " << klass->GetStatus();
      old_status = klass->GetStatus();
    }

    // The class might already be erroneous, for example at compile time if we attempted to verify
    // this class as a parent to another.
    if (klass->IsErroneous()) {
      ThrowEarlierClassFailure(klass.Get());
      return verifier::FailureKind::kHardFailure;
    }

    // Don't attempt to re-verify if already verified.
    if (klass->IsVerified()) {
      EnsureSkipAccessChecksMethods(klass, image_pointer_size_);
      return verifier::FailureKind::kNoFailure;
    }

    // For AOT, don't attempt to re-verify if we have already found we should
    // verify at runtime.
    if (Runtime::Current()->IsAotCompiler() && klass->ShouldVerifyAtRuntime()) {
      return verifier::FailureKind::kSoftFailure;
    }

    if (klass->GetStatus() == ClassStatus::kResolved) {
      mirror::Class::SetStatus(klass, ClassStatus::kVerifying, self);
    } else {
      CHECK_EQ(klass->GetStatus(), ClassStatus::kRetryVerificationAtRuntime)
          << klass->PrettyClass();
      CHECK(!Runtime::Current()->IsAotCompiler());
      mirror::Class::SetStatus(klass, ClassStatus::kVerifyingAtRuntime, self);
    }

    // Skip verification if disabled.
    if (!Runtime::Current()->IsVerificationEnabled()) {
      mirror::Class::SetStatus(klass, ClassStatus::kVerified, self);
      EnsureSkipAccessChecksMethods(klass, image_pointer_size_);
      return verifier::FailureKind::kNoFailure;
    }
  }

  VLOG(class_linker) << "Beginning verification for class: "
                     << klass->PrettyDescriptor()
                     << " in " << klass->GetDexCache()->GetLocation()->ToModifiedUtf8();

  // Verify super class.
  StackHandleScope<2> hs(self);
  MutableHandle<mirror::Class> supertype(hs.NewHandle(klass->GetSuperClass()));
  // If we have a superclass and we get a hard verification failure we can return immediately.
  if (supertype != nullptr && !AttemptSupertypeVerification(self, klass, supertype)) {
    CHECK(self->IsExceptionPending()) << "Verification error should be pending.";
    return verifier::FailureKind::kHardFailure;
  }

  // Verify all default super-interfaces.
  //
  // (1) Don't bother if the superclass has already had a soft verification failure.
  //
  // (2) Interfaces shouldn't bother to do this recursive verification because they cannot cause
  //     recursive initialization by themselves. This is because when an interface is initialized
  //     directly it must not initialize its superinterfaces. We are allowed to verify regardless
  //     but choose not to for an optimization. If the interfaces is being verified due to a class
  //     initialization (which would need all the default interfaces to be verified) the class code
  //     will trigger the recursive verification anyway.
  if ((supertype == nullptr || supertype->IsVerified())  // See (1)
      && !klass->IsInterface()) {                              // See (2)
    int32_t iftable_count = klass->GetIfTableCount();
    MutableHandle<mirror::Class> iface(hs.NewHandle<mirror::Class>(nullptr));
    // Loop through all interfaces this class has defined. It doesn't matter the order.
    for (int32_t i = 0; i < iftable_count; i++) {
      iface.Assign(klass->GetIfTable()->GetInterface(i));
      DCHECK(iface != nullptr);
      // We only care if we have default interfaces and can skip if we are already verified...
      if (LIKELY(!iface->HasDefaultMethods() || iface->IsVerified())) {
        continue;
      } else if (UNLIKELY(!AttemptSupertypeVerification(self, klass, iface))) {
        // We had a hard failure while verifying this interface. Just return immediately.
        CHECK(self->IsExceptionPending()) << "Verification error should be pending.";
        return verifier::FailureKind::kHardFailure;
      } else if (UNLIKELY(!iface->IsVerified())) {
        // We softly failed to verify the iface. Stop checking and clean up.
        // Put the iface into the supertype handle so we know what caused us to fail.
        supertype.Assign(iface.Get());
        break;
      }
    }
  }

  // At this point if verification failed, then supertype is the "first" supertype that failed
  // verification (without a specific order). If verification succeeded, then supertype is either
  // null or the original superclass of klass and is verified.
  DCHECK(supertype == nullptr ||
         supertype.Get() == klass->GetSuperClass() ||
         !supertype->IsVerified());

  // Try to use verification information from the oat file, otherwise do runtime verification.
  const DexFile& dex_file = *klass->GetDexCache()->GetDexFile();
  ClassStatus oat_file_class_status(ClassStatus::kNotReady);
  bool preverified = VerifyClassUsingOatFile(dex_file, klass.Get(), oat_file_class_status);

  VLOG(class_linker) << "Class preverified status for class "
                     << klass->PrettyDescriptor()
                     << " in " << klass->GetDexCache()->GetLocation()->ToModifiedUtf8()
                     << ": "
                     << preverified;

  // If the oat file says the class had an error, re-run the verifier. That way we will get a
  // precise error message. To ensure a rerun, test:
  //     mirror::Class::IsErroneous(oat_file_class_status) => !preverified
  DCHECK(!mirror::Class::IsErroneous(oat_file_class_status) || !preverified);

  std::string error_msg;
  verifier::FailureKind verifier_failure = verifier::FailureKind::kNoFailure;
  if (!preverified) {
    verifier_failure = PerformClassVerification(self, klass, log_level, &error_msg);
  }

  // Verification is done, grab the lock again.
  ObjectLock<mirror::Class> lock(self, klass);

  if (preverified || verifier_failure != verifier::FailureKind::kHardFailure) {
    if (!preverified && verifier_failure != verifier::FailureKind::kNoFailure) {
      VLOG(class_linker) << "Soft verification failure in class "
                         << klass->PrettyDescriptor()
                         << " in " << klass->GetDexCache()->GetLocation()->ToModifiedUtf8()
                         << " because: " << error_msg;
    }
    self->AssertNoPendingException();
    // Make sure all classes referenced by catch blocks are resolved.
    ResolveClassExceptionHandlerTypes(klass);
    if (verifier_failure == verifier::FailureKind::kNoFailure) {
      // Even though there were no verifier failures we need to respect whether the super-class and
      // super-default-interfaces were verified or requiring runtime reverification.
      if (supertype == nullptr || supertype->IsVerified()) {
        mirror::Class::SetStatus(klass, ClassStatus::kVerified, self);
      } else {
        CHECK_EQ(supertype->GetStatus(), ClassStatus::kRetryVerificationAtRuntime);
        mirror::Class::SetStatus(klass, ClassStatus::kRetryVerificationAtRuntime, self);
        // Pretend a soft failure occurred so that we don't consider the class verified below.
        verifier_failure = verifier::FailureKind::kSoftFailure;
      }
    } else {
      CHECK_EQ(verifier_failure, verifier::FailureKind::kSoftFailure);
      // Soft failures at compile time should be retried at runtime. Soft
      // failures at runtime will be handled by slow paths in the generated
      // code. Set status accordingly.
      if (Runtime::Current()->IsAotCompiler()) {
        mirror::Class::SetStatus(klass, ClassStatus::kRetryVerificationAtRuntime, self);
      } else {
        mirror::Class::SetStatus(klass, ClassStatus::kVerified, self);
        // As this is a fake verified status, make sure the methods are _not_ marked
        // kAccSkipAccessChecks later.
        klass->SetVerificationAttempted();
      }
    }
  } else {
    VLOG(verifier) << "Verification failed on class " << klass->PrettyDescriptor()
                  << " in " << klass->GetDexCache()->GetLocation()->ToModifiedUtf8()
                  << " because: " << error_msg;
    self->AssertNoPendingException();
    ThrowVerifyError(klass.Get(), "%s", error_msg.c_str());
    mirror::Class::SetStatus(klass, ClassStatus::kErrorResolved, self);
  }
  if (preverified || verifier_failure == verifier::FailureKind::kNoFailure) {
    // Class is verified so we don't need to do any access check on its methods.
    // Let the interpreter know it by setting the kAccSkipAccessChecks flag onto each
    // method.
    // Note: we're going here during compilation and at runtime. When we set the
    // kAccSkipAccessChecks flag when compiling image classes, the flag is recorded
    // in the image and is set when loading the image.

    if (UNLIKELY(Runtime::Current()->IsVerificationSoftFail())) {
      // Never skip access checks if the verification soft fail is forced.
      // Mark the class as having a verification attempt to avoid re-running the verifier.
      klass->SetVerificationAttempted();
    } else {
      EnsureSkipAccessChecksMethods(klass, image_pointer_size_);
    }
  }
  // Done verifying. Notify the compiler about the verification status, in case the class
  // was verified implicitly (eg super class of a compiled class).
  if (Runtime::Current()->IsAotCompiler()) {
    Runtime::Current()->GetCompilerCallbacks()->UpdateClassState(
        ClassReference(&klass->GetDexFile(), klass->GetDexClassDefIndex()), klass->GetStatus());
  }
  return verifier_failure;
}

verifier::FailureKind ClassLinker::PerformClassVerification(Thread* self,
                                                            Handle<mirror::Class> klass,
                                                            verifier::HardFailLogMode log_level,
                                                            std::string* error_msg) {
  Runtime* const runtime = Runtime::Current();
  return verifier::ClassVerifier::VerifyClass(self,
                                              klass.Get(),
                                              runtime->GetCompilerCallbacks(),
                                              runtime->IsAotCompiler(),
                                              log_level,
                                              Runtime::Current()->GetTargetSdkVersion(),
                                              error_msg);
}

bool ClassLinker::VerifyClassUsingOatFile(const DexFile& dex_file,
                                          ObjPtr<mirror::Class> klass,
                                          ClassStatus& oat_file_class_status) {
  // If we're compiling, we can only verify the class using the oat file if
  // we are not compiling the image or if the class we're verifying is not part of
  // the compilation unit (app - dependencies). We will let the compiler callback
  // tell us about the latter.
  if (Runtime::Current()->IsAotCompiler()) {
    CompilerCallbacks* callbacks = Runtime::Current()->GetCompilerCallbacks();
    // Are we compiling the bootclasspath?
    if (callbacks->IsBootImage()) {
      return false;
    }
    // We are compiling an app (not the image).
    if (!callbacks->CanUseOatStatusForVerification(klass.Ptr())) {
      return false;
    }
  }

  const OatDexFile* oat_dex_file = dex_file.GetOatDexFile();
  // In case we run without an image there won't be a backing oat file.
  if (oat_dex_file == nullptr || oat_dex_file->GetOatFile() == nullptr) {
    if (!kIsDebugBuild && klass->GetClassLoader() == nullptr) {
      // For boot classpath classes in the case we're not using a default boot image:
      // we don't have the infrastructure yet to query verification data on individual
      // boot vdex files, so it's simpler for now to consider all boot classpath classes
      // verified. This should be taken into account when measuring boot time and app
      // startup compare to the (current) production system where both:
      // 1) updatable boot classpath classes, and
      // 2) classes in /system referencing updatable classes
      // will be verified at runtime.
      if (Runtime::Current()->IsUsingApexBootImageLocation()) {
        oat_file_class_status = ClassStatus::kVerified;
        return true;
      }
    }
    return false;
  }

  uint16_t class_def_index = klass->GetDexClassDefIndex();
  oat_file_class_status = oat_dex_file->GetOatClass(class_def_index).GetStatus();
  if (oat_file_class_status >= ClassStatus::kVerified) {
    return true;
  }
  // If we only verified a subset of the classes at compile time, we can end up with classes that
  // were resolved by the verifier.
  if (oat_file_class_status == ClassStatus::kResolved) {
    return false;
  }
  if (oat_file_class_status == ClassStatus::kRetryVerificationAtRuntime) {
    // Compile time verification failed with a soft error. Compile time verification can fail
    // because we have incomplete type information. Consider the following:
    // class ... {
    //   Foo x;
    //   .... () {
    //     if (...) {
    //       v1 gets assigned a type of resolved class Foo
    //     } else {
    //       v1 gets assigned a type of unresolved class Bar
    //     }
    //     iput x = v1
    // } }
    // when we merge v1 following the if-the-else it results in Conflict
    // (see verifier::RegType::Merge) as we can't know the type of Bar and we could possibly be
    // allowing an unsafe assignment to the field x in the iput (javac may have compiled this as
    // it knew Bar was a sub-class of Foo, but for us this may have been moved into a separate apk
    // at compile time).
    return false;
  }
  if (mirror::Class::IsErroneous(oat_file_class_status)) {
    // Compile time verification failed with a hard error. This is caused by invalid instructions
    // in the class. These errors are unrecoverable.
    return false;
  }
  if (oat_file_class_status == ClassStatus::kNotReady) {
    // Status is uninitialized if we couldn't determine the status at compile time, for example,
    // not loading the class.
    // TODO: when the verifier doesn't rely on Class-es failing to resolve/load the type hierarchy
    // isn't a problem and this case shouldn't occur
    return false;
  }
  std::string temp;
  LOG(FATAL) << "Unexpected class status: " << oat_file_class_status
             << " " << dex_file.GetLocation() << " " << klass->PrettyClass() << " "
             << klass->GetDescriptor(&temp);
  UNREACHABLE();
}

void ClassLinker::ResolveClassExceptionHandlerTypes(Handle<mirror::Class> klass) {
  for (ArtMethod& method : klass->GetMethods(image_pointer_size_)) {
    ResolveMethodExceptionHandlerTypes(&method);
  }
}

void ClassLinker::ResolveMethodExceptionHandlerTypes(ArtMethod* method) {
  // similar to DexVerifier::ScanTryCatchBlocks and dex2oat's ResolveExceptionsForMethod.
  CodeItemDataAccessor accessor(method->DexInstructionData());
  if (!accessor.HasCodeItem()) {
    return;  // native or abstract method
  }
  if (accessor.TriesSize() == 0) {
    return;  // nothing to process
  }
  const uint8_t* handlers_ptr = accessor.GetCatchHandlerData(0);
  uint32_t handlers_size = DecodeUnsignedLeb128(&handlers_ptr);
  for (uint32_t idx = 0; idx < handlers_size; idx++) {
    CatchHandlerIterator iterator(handlers_ptr);
    for (; iterator.HasNext(); iterator.Next()) {
      // Ensure exception types are resolved so that they don't need resolution to be delivered,
      // unresolved exception types will be ignored by exception delivery
      if (iterator.GetHandlerTypeIndex().IsValid()) {
        ObjPtr<mirror::Class> exception_type = ResolveType(iterator.GetHandlerTypeIndex(), method);
        if (exception_type == nullptr) {
          DCHECK(Thread::Current()->IsExceptionPending());
          Thread::Current()->ClearException();
        }
      }
    }
    handlers_ptr = iterator.EndDataPointer();
  }
}

ObjPtr<mirror::Class> ClassLinker::CreateProxyClass(ScopedObjectAccessAlreadyRunnable& soa,
                                                    jstring name,
                                                    jobjectArray interfaces,
                                                    jobject loader,
                                                    jobjectArray methods,
                                                    jobjectArray throws) {
  Thread* self = soa.Self();

  // This is to prevent the calls to ClassLoad and ClassPrepare which can cause java/user-supplied
  // code to be executed. We put it up here so we can avoid all the allocations associated with
  // creating the class. This can happen with (eg) jit-threads.
  if (!self->CanLoadClasses()) {
    // Make sure we don't try to load anything, potentially causing an infinite loop.
    ObjPtr<mirror::Throwable> pre_allocated =
        Runtime::Current()->GetPreAllocatedNoClassDefFoundError();
    self->SetException(pre_allocated);
    return nullptr;
  }

  StackHandleScope<10> hs(self);
  MutableHandle<mirror::Class> temp_klass(hs.NewHandle(
      AllocClass(self, GetClassRoot<mirror::Class>(this), sizeof(mirror::Class))));
  if (temp_klass == nullptr) {
    CHECK(self->IsExceptionPending());  // OOME.
    return nullptr;
  }
  DCHECK(temp_klass->GetClass() != nullptr);
  temp_klass->SetObjectSize(sizeof(mirror::Proxy));
  // Set the class access flags incl. VerificationAttempted, so we do not try to set the flag on
  // the methods.
  temp_klass->SetAccessFlags(kAccClassIsProxy | kAccPublic | kAccFinal | kAccVerificationAttempted);
  temp_klass->SetClassLoader(soa.Decode<mirror::ClassLoader>(loader));
  DCHECK_EQ(temp_klass->GetPrimitiveType(), Primitive::kPrimNot);
  temp_klass->SetName(soa.Decode<mirror::String>(name));
  temp_klass->SetDexCache(GetClassRoot<mirror::Proxy>(this)->GetDexCache());
  // Object has an empty iftable, copy it for that reason.
  temp_klass->SetIfTable(GetClassRoot<mirror::Object>(this)->GetIfTable());
  mirror::Class::SetStatus(temp_klass, ClassStatus::kIdx, self);
  std::string storage;
  const char* descriptor = temp_klass->GetDescriptor(&storage);
  const size_t hash = ComputeModifiedUtf8Hash(descriptor);

  // Needs to be before we insert the class so that the allocator field is set.
  LinearAlloc* const allocator = GetOrCreateAllocatorForClassLoader(temp_klass->GetClassLoader());

  // Insert the class before loading the fields as the field roots
  // (ArtField::declaring_class_) are only visited from the class
  // table. There can't be any suspend points between inserting the
  // class and setting the field arrays below.
  ObjPtr<mirror::Class> existing = InsertClass(descriptor, temp_klass.Get(), hash);
  CHECK(existing == nullptr);

  // Instance fields are inherited, but we add a couple of static fields...
  const size_t num_fields = 2;
  LengthPrefixedArray<ArtField>* sfields = AllocArtFieldArray(self, allocator, num_fields);
  temp_klass->SetSFieldsPtr(sfields);

  // 1. Create a static field 'interfaces' that holds the _declared_ interfaces implemented by
  // our proxy, so Class.getInterfaces doesn't return the flattened set.
  ArtField& interfaces_sfield = sfields->At(0);
  interfaces_sfield.SetDexFieldIndex(0);
  interfaces_sfield.SetDeclaringClass(temp_klass.Get());
  interfaces_sfield.SetAccessFlags(kAccStatic | kAccPublic | kAccFinal);

  // 2. Create a static field 'throws' that holds exceptions thrown by our methods.
  ArtField& throws_sfield = sfields->At(1);
  throws_sfield.SetDexFieldIndex(1);
  throws_sfield.SetDeclaringClass(temp_klass.Get());
  throws_sfield.SetAccessFlags(kAccStatic | kAccPublic | kAccFinal);

  // Proxies have 1 direct method, the constructor
  const size_t num_direct_methods = 1;

  // They have as many virtual methods as the array
  auto h_methods = hs.NewHandle(soa.Decode<mirror::ObjectArray<mirror::Method>>(methods));
  DCHECK_EQ(h_methods->GetClass(), GetClassRoot<mirror::ObjectArray<mirror::Method>>())
      << mirror::Class::PrettyClass(h_methods->GetClass());
  const size_t num_virtual_methods = h_methods->GetLength();

  // Create the methods array.
  LengthPrefixedArray<ArtMethod>* proxy_class_methods = AllocArtMethodArray(
        self, allocator, num_direct_methods + num_virtual_methods);
  // Currently AllocArtMethodArray cannot return null, but the OOM logic is left there in case we
  // want to throw OOM in the future.
  if (UNLIKELY(proxy_class_methods == nullptr)) {
    self->AssertPendingOOMException();
    return nullptr;
  }
  temp_klass->SetMethodsPtr(proxy_class_methods, num_direct_methods, num_virtual_methods);

  // Create the single direct method.
  CreateProxyConstructor(temp_klass, temp_klass->GetDirectMethodUnchecked(0, image_pointer_size_));

  // Create virtual method using specified prototypes.
  // TODO These should really use the iterators.
  for (size_t i = 0; i < num_virtual_methods; ++i) {
    auto* virtual_method = temp_klass->GetVirtualMethodUnchecked(i, image_pointer_size_);
    auto* prototype = h_methods->Get(i)->GetArtMethod();
    CreateProxyMethod(temp_klass, prototype, virtual_method);
    DCHECK(virtual_method->GetDeclaringClass() != nullptr);
    DCHECK(prototype->GetDeclaringClass() != nullptr);
  }

  // The super class is java.lang.reflect.Proxy
  temp_klass->SetSuperClass(GetClassRoot<mirror::Proxy>(this));
  // Now effectively in the loaded state.
  mirror::Class::SetStatus(temp_klass, ClassStatus::kLoaded, self);
  self->AssertNoPendingException();

  // At this point the class is loaded. Publish a ClassLoad event.
  // Note: this may be a temporary class. It is a listener's responsibility to handle this.
  Runtime::Current()->GetRuntimeCallbacks()->ClassLoad(temp_klass);

  MutableHandle<mirror::Class> klass = hs.NewHandle<mirror::Class>(nullptr);
  {
    // Must hold lock on object when resolved.
    ObjectLock<mirror::Class> resolution_lock(self, temp_klass);
    // Link the fields and virtual methods, creating vtable and iftables.
    // The new class will replace the old one in the class table.
    Handle<mirror::ObjectArray<mirror::Class>> h_interfaces(
        hs.NewHandle(soa.Decode<mirror::ObjectArray<mirror::Class>>(interfaces)));
    if (!LinkClass(self, descriptor, temp_klass, h_interfaces, &klass)) {
      mirror::Class::SetStatus(temp_klass, ClassStatus::kErrorUnresolved, self);
      return nullptr;
    }
  }
  CHECK(temp_klass->IsRetired());
  CHECK_NE(temp_klass.Get(), klass.Get());

  CHECK_EQ(interfaces_sfield.GetDeclaringClass(), klass.Get());
  interfaces_sfield.SetObject<false>(
      klass.Get(),
      soa.Decode<mirror::ObjectArray<mirror::Class>>(interfaces));
  CHECK_EQ(throws_sfield.GetDeclaringClass(), klass.Get());
  throws_sfield.SetObject<false>(
      klass.Get(),
      soa.Decode<mirror::ObjectArray<mirror::ObjectArray<mirror::Class>>>(throws));

  Runtime::Current()->GetRuntimeCallbacks()->ClassPrepare(temp_klass, klass);

  // SubtypeCheckInfo::Initialized must happen-before any new-instance for that type.
  // See also ClassLinker::EnsureInitialized().
  if (kBitstringSubtypeCheckEnabled) {
    MutexLock subtype_check_lock(Thread::Current(), *Locks::subtype_check_lock_);
    SubtypeCheck<ObjPtr<mirror::Class>>::EnsureInitialized(klass.Get());
    // TODO: Avoid taking subtype_check_lock_ if SubtypeCheck for j.l.r.Proxy is already assigned.
  }

  {
    // Lock on klass is released. Lock new class object.
    ObjectLock<mirror::Class> initialization_lock(self, klass);
    EnsureSkipAccessChecksMethods(klass, image_pointer_size_);
    mirror::Class::SetStatus(klass, ClassStatus::kInitialized, self);
  }

  // sanity checks
  if (kIsDebugBuild) {
    CHECK(klass->GetIFieldsPtr() == nullptr);
    CheckProxyConstructor(klass->GetDirectMethod(0, image_pointer_size_));

    for (size_t i = 0; i < num_virtual_methods; ++i) {
      auto* virtual_method = klass->GetVirtualMethodUnchecked(i, image_pointer_size_);
      auto* prototype = h_methods->Get(i++)->GetArtMethod();
      CheckProxyMethod(virtual_method, prototype);
    }

    StackHandleScope<1> hs2(self);
    Handle<mirror::String> decoded_name = hs2.NewHandle(soa.Decode<mirror::String>(name));
    std::string interfaces_field_name(StringPrintf("java.lang.Class[] %s.interfaces",
                                                   decoded_name->ToModifiedUtf8().c_str()));
    CHECK_EQ(ArtField::PrettyField(klass->GetStaticField(0)), interfaces_field_name);

    std::string throws_field_name(StringPrintf("java.lang.Class[][] %s.throws",
                                               decoded_name->ToModifiedUtf8().c_str()));
    CHECK_EQ(ArtField::PrettyField(klass->GetStaticField(1)), throws_field_name);

    CHECK_EQ(klass.Get()->GetProxyInterfaces(),
             soa.Decode<mirror::ObjectArray<mirror::Class>>(interfaces));
    CHECK_EQ(klass.Get()->GetProxyThrows(),
             soa.Decode<mirror::ObjectArray<mirror::ObjectArray<mirror::Class>>>(throws));
  }
  return klass.Get();
}

void ClassLinker::CreateProxyConstructor(Handle<mirror::Class> klass, ArtMethod* out) {
  // Create constructor for Proxy that must initialize the method.
  ObjPtr<mirror::Class> proxy_class = GetClassRoot<mirror::Proxy>(this);
  CHECK_EQ(proxy_class->NumDirectMethods(), 21u);

  // Find the <init>(InvocationHandler)V method. The exact method offset varies depending
  // on which front-end compiler was used to build the libcore DEX files.
  ArtMethod* proxy_constructor =
      jni::DecodeArtMethod(WellKnownClasses::java_lang_reflect_Proxy_init);
  DCHECK(proxy_constructor != nullptr)
      << "Could not find <init> method in java.lang.reflect.Proxy";

  // Clone the existing constructor of Proxy (our constructor would just invoke it so steal its
  // code_ too)
  DCHECK(out != nullptr);
  out->CopyFrom(proxy_constructor, image_pointer_size_);
  // Make this constructor public and fix the class to be our Proxy version.
  // Mark kAccCompileDontBother so that we don't take JIT samples for the method. b/62349349
  // Note that the compiler calls a ResolveMethod() overload that does not handle a Proxy referrer.
  out->SetAccessFlags((out->GetAccessFlags() & ~kAccProtected) |
                      kAccPublic |
                      kAccCompileDontBother);
  out->SetDeclaringClass(klass.Get());

  // Set the original constructor method.
  out->SetDataPtrSize(proxy_constructor, image_pointer_size_);
}

void ClassLinker::CheckProxyConstructor(ArtMethod* constructor) const {
  CHECK(constructor->IsConstructor());
  auto* np = constructor->GetInterfaceMethodIfProxy(image_pointer_size_);
  CHECK_STREQ(np->GetName(), "<init>");
  CHECK_STREQ(np->GetSignature().ToString().c_str(), "(Ljava/lang/reflect/InvocationHandler;)V");
  DCHECK(constructor->IsPublic());
}

void ClassLinker::CreateProxyMethod(Handle<mirror::Class> klass, ArtMethod* prototype,
                                    ArtMethod* out) {
  // We steal everything from the prototype (such as DexCache, invoke stub, etc.) then specialize
  // as necessary
  DCHECK(out != nullptr);
  out->CopyFrom(prototype, image_pointer_size_);

  // Set class to be the concrete proxy class.
  out->SetDeclaringClass(klass.Get());
  // Clear the abstract, default and conflict flags to ensure that defaults aren't picked in
  // preference to the invocation handler.
  const uint32_t kRemoveFlags = kAccAbstract | kAccDefault | kAccDefaultConflict;
  // Make the method final.
  // Mark kAccCompileDontBother so that we don't take JIT samples for the method. b/62349349
  const uint32_t kAddFlags = kAccFinal | kAccCompileDontBother;
  out->SetAccessFlags((out->GetAccessFlags() & ~kRemoveFlags) | kAddFlags);

  // Clear the dex_code_item_offset_. It needs to be 0 since proxy methods have no CodeItems but the
  // method they copy might (if it's a default method).
  out->SetCodeItemOffset(0);

  // Set the original interface method.
  out->SetDataPtrSize(prototype, image_pointer_size_);

  // At runtime the method looks like a reference and argument saving method, clone the code
  // related parameters from this method.
  out->SetEntryPointFromQuickCompiledCode(GetQuickProxyInvokeHandler());
}

void ClassLinker::CheckProxyMethod(ArtMethod* method, ArtMethod* prototype) const {
  // Basic sanity
  CHECK(!prototype->IsFinal());
  CHECK(method->IsFinal());
  CHECK(method->IsInvokable());

  // The proxy method doesn't have its own dex cache or dex file and so it steals those of its
  // interface prototype. The exception to this are Constructors and the Class of the Proxy itself.
  CHECK_EQ(prototype->GetDexMethodIndex(), method->GetDexMethodIndex());
  CHECK_EQ(prototype, method->GetInterfaceMethodIfProxy(image_pointer_size_));
}

bool ClassLinker::CanWeInitializeClass(ObjPtr<mirror::Class> klass, bool can_init_statics,
                                       bool can_init_parents) {
  if (can_init_statics && can_init_parents) {
    return true;
  }
  if (!can_init_statics) {
    // Check if there's a class initializer.
    ArtMethod* clinit = klass->FindClassInitializer(image_pointer_size_);
    if (clinit != nullptr) {
      return false;
    }
    // Check if there are encoded static values needing initialization.
    if (klass->NumStaticFields() != 0) {
      const dex::ClassDef* dex_class_def = klass->GetClassDef();
      DCHECK(dex_class_def != nullptr);
      if (dex_class_def->static_values_off_ != 0) {
        return false;
      }
    }
    // If we are a class we need to initialize all interfaces with default methods when we are
    // initialized. Check all of them.
    if (!klass->IsInterface()) {
      size_t num_interfaces = klass->GetIfTableCount();
      for (size_t i = 0; i < num_interfaces; i++) {
        ObjPtr<mirror::Class> iface = klass->GetIfTable()->GetInterface(i);
        if (iface->HasDefaultMethods() &&
            !CanWeInitializeClass(iface, can_init_statics, can_init_parents)) {
          return false;
        }
      }
    }
  }
  if (klass->IsInterface() || !klass->HasSuperClass()) {
    return true;
  }
  ObjPtr<mirror::Class> super_class = klass->GetSuperClass();
  if (!can_init_parents && !super_class->IsInitialized()) {
    return false;
  }
  return CanWeInitializeClass(super_class, can_init_statics, can_init_parents);
}

bool ClassLinker::InitializeClass(Thread* self, Handle<mirror::Class> klass,
                                  bool can_init_statics, bool can_init_parents) {
  // see JLS 3rd edition, 12.4.2 "Detailed Initialization Procedure" for the locking protocol

  // Are we already initialized and therefore done?
  // Note: we differ from the JLS here as we don't do this under the lock, this is benign as
  // an initialized class will never change its state.
  if (klass->IsInitialized()) {
    return true;
  }

  // Fast fail if initialization requires a full runtime. Not part of the JLS.
  if (!CanWeInitializeClass(klass.Get(), can_init_statics, can_init_parents)) {
    return false;
  }

  self->AllowThreadSuspension();
  uint64_t t0;
  {
    ObjectLock<mirror::Class> lock(self, klass);

    // Re-check under the lock in case another thread initialized ahead of us.
    if (klass->IsInitialized()) {
      return true;
    }

    // Was the class already found to be erroneous? Done under the lock to match the JLS.
    if (klass->IsErroneous()) {
      ThrowEarlierClassFailure(klass.Get(), true, /* log= */ true);
      VlogClassInitializationFailure(klass);
      return false;
    }

    CHECK(klass->IsResolved() && !klass->IsErroneousResolved())
        << klass->PrettyClass() << ": state=" << klass->GetStatus();

    if (!klass->IsVerified()) {
      VerifyClass(self, klass);
      if (!klass->IsVerified()) {
        // We failed to verify, expect either the klass to be erroneous or verification failed at
        // compile time.
        if (klass->IsErroneous()) {
          // The class is erroneous. This may be a verifier error, or another thread attempted
          // verification and/or initialization and failed. We can distinguish those cases by
          // whether an exception is already pending.
          if (self->IsExceptionPending()) {
            // Check that it's a VerifyError.
            DCHECK_EQ("java.lang.Class<java.lang.VerifyError>",
                      mirror::Class::PrettyClass(self->GetException()->GetClass()));
          } else {
            // Check that another thread attempted initialization.
            DCHECK_NE(0, klass->GetClinitThreadId());
            DCHECK_NE(self->GetTid(), klass->GetClinitThreadId());
            // Need to rethrow the previous failure now.
            ThrowEarlierClassFailure(klass.Get(), true);
          }
          VlogClassInitializationFailure(klass);
        } else {
          CHECK(Runtime::Current()->IsAotCompiler());
          CHECK_EQ(klass->GetStatus(), ClassStatus::kRetryVerificationAtRuntime);
          self->AssertNoPendingException();
          self->SetException(Runtime::Current()->GetPreAllocatedNoClassDefFoundError());
        }
        self->AssertPendingException();
        return false;
      } else {
        self->AssertNoPendingException();
      }

      // A separate thread could have moved us all the way to initialized. A "simple" example
      // involves a subclass of the current class being initialized at the same time (which
      // will implicitly initialize the superclass, if scheduled that way). b/28254258
      DCHECK(!klass->IsErroneous()) << klass->GetStatus();
      if (klass->IsInitialized()) {
        return true;
      }
    }

    // If the class is ClassStatus::kInitializing, either this thread is
    // initializing higher up the stack or another thread has beat us
    // to initializing and we need to wait. Either way, this
    // invocation of InitializeClass will not be responsible for
    // running <clinit> and will return.
    if (klass->GetStatus() == ClassStatus::kInitializing) {
      // Could have got an exception during verification.
      if (self->IsExceptionPending()) {
        VlogClassInitializationFailure(klass);
        return false;
      }
      // We caught somebody else in the act; was it us?
      if (klass->GetClinitThreadId() == self->GetTid()) {
        // Yes. That's fine. Return so we can continue initializing.
        return true;
      }
      // No. That's fine. Wait for another thread to finish initializing.
      return WaitForInitializeClass(klass, self, lock);
    }

    // Try to get the oat class's status for this class if the oat file is present. The compiler
    // tries to validate superclass descriptors, and writes the result into the oat file.
    // Runtime correctness is guaranteed by classpath checks done on loading. If the classpath
    // is different at runtime than it was at compile time, the oat file is rejected. So if the
    // oat file is present, the classpaths must match, and the runtime time check can be skipped.
    bool has_oat_class = false;
    const Runtime* runtime = Runtime::Current();
    const OatFile::OatClass oat_class = (runtime->IsStarted() && !runtime->IsAotCompiler())
        ? OatFile::FindOatClass(klass->GetDexFile(), klass->GetDexClassDefIndex(), &has_oat_class)
        : OatFile::OatClass::Invalid();
    if (oat_class.GetStatus() < ClassStatus::kSuperclassValidated &&
        !ValidateSuperClassDescriptors(klass)) {
      mirror::Class::SetStatus(klass, ClassStatus::kErrorResolved, self);
      return false;
    }
    self->AllowThreadSuspension();

    CHECK_EQ(klass->GetStatus(), ClassStatus::kVerified) << klass->PrettyClass()
        << " self.tid=" << self->GetTid() << " clinit.tid=" << klass->GetClinitThreadId();

    // From here out other threads may observe that we're initializing and so changes of state
    // require the a notification.
    klass->SetClinitThreadId(self->GetTid());
    mirror::Class::SetStatus(klass, ClassStatus::kInitializing, self);

    t0 = NanoTime();
  }

  // Initialize super classes, must be done while initializing for the JLS.
  if (!klass->IsInterface() && klass->HasSuperClass()) {
    ObjPtr<mirror::Class> super_class = klass->GetSuperClass();
    if (!super_class->IsInitialized()) {
      CHECK(!super_class->IsInterface());
      CHECK(can_init_parents);
      StackHandleScope<1> hs(self);
      Handle<mirror::Class> handle_scope_super(hs.NewHandle(super_class));
      bool super_initialized = InitializeClass(self, handle_scope_super, can_init_statics, true);
      if (!super_initialized) {
        // The super class was verified ahead of entering initializing, we should only be here if
        // the super class became erroneous due to initialization.
        // For the case of aot compiler, the super class might also be initializing but we don't
        // want to process circular dependencies in pre-compile.
        CHECK(self->IsExceptionPending())
            << "Super class initialization failed for "
            << handle_scope_super->PrettyDescriptor()
            << " that has unexpected status " << handle_scope_super->GetStatus()
            << "\nPending exception:\n"
            << (self->GetException() != nullptr ? self->GetException()->Dump() : "");
        ObjectLock<mirror::Class> lock(self, klass);
        // Initialization failed because the super-class is erroneous.
        mirror::Class::SetStatus(klass, ClassStatus::kErrorResolved, self);
        return false;
      }
    }
  }

  if (!klass->IsInterface()) {
    // Initialize interfaces with default methods for the JLS.
    size_t num_direct_interfaces = klass->NumDirectInterfaces();
    // Only setup the (expensive) handle scope if we actually need to.
    if (UNLIKELY(num_direct_interfaces > 0)) {
      StackHandleScope<1> hs_iface(self);
      MutableHandle<mirror::Class> handle_scope_iface(hs_iface.NewHandle<mirror::Class>(nullptr));
      for (size_t i = 0; i < num_direct_interfaces; i++) {
        handle_scope_iface.Assign(mirror::Class::GetDirectInterface(self, klass.Get(), i));
        CHECK(handle_scope_iface != nullptr) << klass->PrettyDescriptor() << " iface #" << i;
        CHECK(handle_scope_iface->IsInterface());
        if (handle_scope_iface->HasBeenRecursivelyInitialized()) {
          // We have already done this for this interface. Skip it.
          continue;
        }
        // We cannot just call initialize class directly because we need to ensure that ALL
        // interfaces with default methods are initialized. Non-default interface initialization
        // will not affect other non-default super-interfaces.
        bool iface_initialized = InitializeDefaultInterfaceRecursive(self,
                                                                     handle_scope_iface,
                                                                     can_init_statics,
                                                                     can_init_parents);
        if (!iface_initialized) {
          ObjectLock<mirror::Class> lock(self, klass);
          // Initialization failed because one of our interfaces with default methods is erroneous.
          mirror::Class::SetStatus(klass, ClassStatus::kErrorResolved, self);
          return false;
        }
      }
    }
  }

  const size_t num_static_fields = klass->NumStaticFields();
  if (num_static_fields > 0) {
    const dex::ClassDef* dex_class_def = klass->GetClassDef();
    CHECK(dex_class_def != nullptr);
    StackHandleScope<3> hs(self);
    Handle<mirror::ClassLoader> class_loader(hs.NewHandle(klass->GetClassLoader()));
    Handle<mirror::DexCache> dex_cache(hs.NewHandle(klass->GetDexCache()));

    // Eagerly fill in static fields so that the we don't have to do as many expensive
    // Class::FindStaticField in ResolveField.
    for (size_t i = 0; i < num_static_fields; ++i) {
      ArtField* field = klass->GetStaticField(i);
      const uint32_t field_idx = field->GetDexFieldIndex();
      ArtField* resolved_field = dex_cache->GetResolvedField(field_idx, image_pointer_size_);
      if (resolved_field == nullptr) {
        // Populating cache of a dex file which defines `klass` should always be allowed.
        DCHECK(!hiddenapi::ShouldDenyAccessToMember(
            field,
            hiddenapi::AccessContext(class_loader.Get(), dex_cache.Get()),
            hiddenapi::AccessMethod::kNone));
        dex_cache->SetResolvedField(field_idx, field, image_pointer_size_);
      } else {
        DCHECK_EQ(field, resolved_field);
      }
    }

    annotations::RuntimeEncodedStaticFieldValueIterator value_it(dex_cache,
                                                                 class_loader,
                                                                 this,
                                                                 *dex_class_def);
    const DexFile& dex_file = *dex_cache->GetDexFile();

    if (value_it.HasNext()) {
      ClassAccessor accessor(dex_file, *dex_class_def);
      CHECK(can_init_statics);
      for (const ClassAccessor::Field& field : accessor.GetStaticFields()) {
        if (!value_it.HasNext()) {
          break;
        }
        ArtField* art_field = ResolveField(field.GetIndex(),
                                           dex_cache,
                                           class_loader,
                                           /* is_static= */ true);
        if (Runtime::Current()->IsActiveTransaction()) {
          value_it.ReadValueToField<true>(art_field);
        } else {
          value_it.ReadValueToField<false>(art_field);
        }
        if (self->IsExceptionPending()) {
          break;
        }
        value_it.Next();
      }
      DCHECK(self->IsExceptionPending() || !value_it.HasNext());
    }
  }


  if (!self->IsExceptionPending()) {
    ArtMethod* clinit = klass->FindClassInitializer(image_pointer_size_);
    if (clinit != nullptr) {
      CHECK(can_init_statics);
      JValue result;
      clinit->Invoke(self, nullptr, 0, &result, "V");
    }
  }
  self->AllowThreadSuspension();
  uint64_t t1 = NanoTime();

  bool success = true;
  {
    ObjectLock<mirror::Class> lock(self, klass);

    if (self->IsExceptionPending()) {
      WrapExceptionInInitializer(klass);
      mirror::Class::SetStatus(klass, ClassStatus::kErrorResolved, self);
      success = false;
    } else if (Runtime::Current()->IsTransactionAborted()) {
      // The exception thrown when the transaction aborted has been caught and cleared
      // so we need to throw it again now.
      VLOG(compiler) << "Return from class initializer of "
                     << mirror::Class::PrettyDescriptor(klass.Get())
                     << " without exception while transaction was aborted: re-throw it now.";
      Runtime::Current()->ThrowTransactionAbortError(self);
      mirror::Class::SetStatus(klass, ClassStatus::kErrorResolved, self);
      success = false;
    } else {
      RuntimeStats* global_stats = Runtime::Current()->GetStats();
      RuntimeStats* thread_stats = self->GetStats();
      ++global_stats->class_init_count;
      ++thread_stats->class_init_count;
      global_stats->class_init_time_ns += (t1 - t0);
      thread_stats->class_init_time_ns += (t1 - t0);
      // Set the class as initialized except if failed to initialize static fields.
      mirror::Class::SetStatus(klass, ClassStatus::kInitialized, self);
      if (VLOG_IS_ON(class_linker)) {
        std::string temp;
        LOG(INFO) << "Initialized class " << klass->GetDescriptor(&temp) << " from " <<
            klass->GetLocation();
      }
      // Opportunistically set static method trampolines to their destination.
      FixupStaticTrampolines(klass.Get());
    }
  }
  return success;
}

// We recursively run down the tree of interfaces. We need to do this in the order they are declared
// and perform the initialization only on those interfaces that contain default methods.
bool ClassLinker::InitializeDefaultInterfaceRecursive(Thread* self,
                                                      Handle<mirror::Class> iface,
                                                      bool can_init_statics,
                                                      bool can_init_parents) {
  CHECK(iface->IsInterface());
  size_t num_direct_ifaces = iface->NumDirectInterfaces();
  // Only create the (expensive) handle scope if we need it.
  if (UNLIKELY(num_direct_ifaces > 0)) {
    StackHandleScope<1> hs(self);
    MutableHandle<mirror::Class> handle_super_iface(hs.NewHandle<mirror::Class>(nullptr));
    // First we initialize all of iface's super-interfaces recursively.
    for (size_t i = 0; i < num_direct_ifaces; i++) {
      ObjPtr<mirror::Class> super_iface = mirror::Class::GetDirectInterface(self, iface.Get(), i);
      CHECK(super_iface != nullptr) << iface->PrettyDescriptor() << " iface #" << i;
      if (!super_iface->HasBeenRecursivelyInitialized()) {
        // Recursive step
        handle_super_iface.Assign(super_iface);
        if (!InitializeDefaultInterfaceRecursive(self,
                                                 handle_super_iface,
                                                 can_init_statics,
                                                 can_init_parents)) {
          return false;
        }
      }
    }
  }

  bool result = true;
  // Then we initialize 'iface' if it has default methods. We do not need to (and in fact must not)
  // initialize if we don't have default methods.
  if (iface->HasDefaultMethods()) {
    result = EnsureInitialized(self, iface, can_init_statics, can_init_parents);
  }

  // Mark that this interface has undergone recursive default interface initialization so we know we
  // can skip it on any later class initializations. We do this even if we are not a default
  // interface since we can still avoid the traversal. This is purely a performance optimization.
  if (result) {
    // TODO This should be done in a better way
    // Note: Use a try-lock to avoid blocking when someone else is holding the lock on this
    //       interface. It is bad (Java) style, but not impossible. Marking the recursive
    //       initialization is a performance optimization (to avoid another idempotent visit
    //       for other implementing classes/interfaces), and can be revisited later.
    ObjectTryLock<mirror::Class> lock(self, iface);
    if (lock.Acquired()) {
      iface->SetRecursivelyInitialized();
    }
  }
  return result;
}

bool ClassLinker::WaitForInitializeClass(Handle<mirror::Class> klass,
                                         Thread* self,
                                         ObjectLock<mirror::Class>& lock)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  while (true) {
    self->AssertNoPendingException();
    CHECK(!klass->IsInitialized());
    lock.WaitIgnoringInterrupts();

    // When we wake up, repeat the test for init-in-progress.  If
    // there's an exception pending (only possible if
    // we were not using WaitIgnoringInterrupts), bail out.
    if (self->IsExceptionPending()) {
      WrapExceptionInInitializer(klass);
      mirror::Class::SetStatus(klass, ClassStatus::kErrorResolved, self);
      return false;
    }
    // Spurious wakeup? Go back to waiting.
    if (klass->GetStatus() == ClassStatus::kInitializing) {
      continue;
    }
    if (klass->GetStatus() == ClassStatus::kVerified &&
        Runtime::Current()->IsAotCompiler()) {
      // Compile time initialization failed.
      return false;
    }
    if (klass->IsErroneous()) {
      // The caller wants an exception, but it was thrown in a
      // different thread.  Synthesize one here.
      ThrowNoClassDefFoundError("<clinit> failed for class %s; see exception in other thread",
                                klass->PrettyDescriptor().c_str());
      VlogClassInitializationFailure(klass);
      return false;
    }
    if (klass->IsInitialized()) {
      return true;
    }
    LOG(FATAL) << "Unexpected class status. " << klass->PrettyClass() << " is "
        << klass->GetStatus();
  }
  UNREACHABLE();
}

static void ThrowSignatureCheckResolveReturnTypeException(Handle<mirror::Class> klass,
                                                          Handle<mirror::Class> super_klass,
                                                          ArtMethod* method,
                                                          ArtMethod* m)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  DCHECK(Thread::Current()->IsExceptionPending());
  DCHECK(!m->IsProxyMethod());
  const DexFile* dex_file = m->GetDexFile();
  const dex::MethodId& method_id = dex_file->GetMethodId(m->GetDexMethodIndex());
  const dex::ProtoId& proto_id = dex_file->GetMethodPrototype(method_id);
  dex::TypeIndex return_type_idx = proto_id.return_type_idx_;
  std::string return_type = dex_file->PrettyType(return_type_idx);
  std::string class_loader = mirror::Object::PrettyTypeOf(m->GetDeclaringClass()->GetClassLoader());
  ThrowWrappedLinkageError(klass.Get(),
                           "While checking class %s method %s signature against %s %s: "
                           "Failed to resolve return type %s with %s",
                           mirror::Class::PrettyDescriptor(klass.Get()).c_str(),
                           ArtMethod::PrettyMethod(method).c_str(),
                           super_klass->IsInterface() ? "interface" : "superclass",
                           mirror::Class::PrettyDescriptor(super_klass.Get()).c_str(),
                           return_type.c_str(), class_loader.c_str());
}

static void ThrowSignatureCheckResolveArgException(Handle<mirror::Class> klass,
                                                   Handle<mirror::Class> super_klass,
                                                   ArtMethod* method,
                                                   ArtMethod* m,
                                                   uint32_t index,
                                                   dex::TypeIndex arg_type_idx)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  DCHECK(Thread::Current()->IsExceptionPending());
  DCHECK(!m->IsProxyMethod());
  const DexFile* dex_file = m->GetDexFile();
  std::string arg_type = dex_file->PrettyType(arg_type_idx);
  std::string class_loader = mirror::Object::PrettyTypeOf(m->GetDeclaringClass()->GetClassLoader());
  ThrowWrappedLinkageError(klass.Get(),
                           "While checking class %s method %s signature against %s %s: "
                           "Failed to resolve arg %u type %s with %s",
                           mirror::Class::PrettyDescriptor(klass.Get()).c_str(),
                           ArtMethod::PrettyMethod(method).c_str(),
                           super_klass->IsInterface() ? "interface" : "superclass",
                           mirror::Class::PrettyDescriptor(super_klass.Get()).c_str(),
                           index, arg_type.c_str(), class_loader.c_str());
}

static void ThrowSignatureMismatch(Handle<mirror::Class> klass,
                                   Handle<mirror::Class> super_klass,
                                   ArtMethod* method,
                                   const std::string& error_msg)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  ThrowLinkageError(klass.Get(),
                    "Class %s method %s resolves differently in %s %s: %s",
                    mirror::Class::PrettyDescriptor(klass.Get()).c_str(),
                    ArtMethod::PrettyMethod(method).c_str(),
                    super_klass->IsInterface() ? "interface" : "superclass",
                    mirror::Class::PrettyDescriptor(super_klass.Get()).c_str(),
                    error_msg.c_str());
}

static bool HasSameSignatureWithDifferentClassLoaders(Thread* self,
                                                      Handle<mirror::Class> klass,
                                                      Handle<mirror::Class> super_klass,
                                                      ArtMethod* method1,
                                                      ArtMethod* method2)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  {
    StackHandleScope<1> hs(self);
    Handle<mirror::Class> return_type(hs.NewHandle(method1->ResolveReturnType()));
    if (UNLIKELY(return_type == nullptr)) {
      ThrowSignatureCheckResolveReturnTypeException(klass, super_klass, method1, method1);
      return false;
    }
    ObjPtr<mirror::Class> other_return_type = method2->ResolveReturnType();
    if (UNLIKELY(other_return_type == nullptr)) {
      ThrowSignatureCheckResolveReturnTypeException(klass, super_klass, method1, method2);
      return false;
    }
    if (UNLIKELY(other_return_type != return_type.Get())) {
      ThrowSignatureMismatch(klass, super_klass, method1,
                             StringPrintf("Return types mismatch: %s(%p) vs %s(%p)",
                                          return_type->PrettyClassAndClassLoader().c_str(),
                                          return_type.Get(),
                                          other_return_type->PrettyClassAndClassLoader().c_str(),
                                          other_return_type.Ptr()));
      return false;
    }
  }
  const dex::TypeList* types1 = method1->GetParameterTypeList();
  const dex::TypeList* types2 = method2->GetParameterTypeList();
  if (types1 == nullptr) {
    if (types2 != nullptr && types2->Size() != 0) {
      ThrowSignatureMismatch(klass, super_klass, method1,
                             StringPrintf("Type list mismatch with %s",
                                          method2->PrettyMethod(true).c_str()));
      return false;
    }
    return true;
  } else if (UNLIKELY(types2 == nullptr)) {
    if (types1->Size() != 0) {
      ThrowSignatureMismatch(klass, super_klass, method1,
                             StringPrintf("Type list mismatch with %s",
                                          method2->PrettyMethod(true).c_str()));
      return false;
    }
    return true;
  }
  uint32_t num_types = types1->Size();
  if (UNLIKELY(num_types != types2->Size())) {
    ThrowSignatureMismatch(klass, super_klass, method1,
                           StringPrintf("Type list mismatch with %s",
                                        method2->PrettyMethod(true).c_str()));
    return false;
  }
  for (uint32_t i = 0; i < num_types; ++i) {
    StackHandleScope<1> hs(self);
    dex::TypeIndex param_type_idx = types1->GetTypeItem(i).type_idx_;
    Handle<mirror::Class> param_type(hs.NewHandle(
        method1->ResolveClassFromTypeIndex(param_type_idx)));
    if (UNLIKELY(param_type == nullptr)) {
      ThrowSignatureCheckResolveArgException(klass, super_klass, method1,
                                             method1, i, param_type_idx);
      return false;
    }
    dex::TypeIndex other_param_type_idx = types2->GetTypeItem(i).type_idx_;
    ObjPtr<mirror::Class> other_param_type =
        method2->ResolveClassFromTypeIndex(other_param_type_idx);
    if (UNLIKELY(other_param_type == nullptr)) {
      ThrowSignatureCheckResolveArgException(klass, super_klass, method1,
                                             method2, i, other_param_type_idx);
      return false;
    }
    if (UNLIKELY(param_type.Get() != other_param_type)) {
      ThrowSignatureMismatch(klass, super_klass, method1,
                             StringPrintf("Parameter %u type mismatch: %s(%p) vs %s(%p)",
                                          i,
                                          param_type->PrettyClassAndClassLoader().c_str(),
                                          param_type.Get(),
                                          other_param_type->PrettyClassAndClassLoader().c_str(),
                                          other_param_type.Ptr()));
      return false;
    }
  }
  return true;
}


bool ClassLinker::ValidateSuperClassDescriptors(Handle<mirror::Class> klass) {
  if (klass->IsInterface()) {
    return true;
  }
  // Begin with the methods local to the superclass.
  Thread* self = Thread::Current();
  StackHandleScope<1> hs(self);
  MutableHandle<mirror::Class> super_klass(hs.NewHandle<mirror::Class>(nullptr));
  if (klass->HasSuperClass() &&
      klass->GetClassLoader() != klass->GetSuperClass()->GetClassLoader()) {
    super_klass.Assign(klass->GetSuperClass());
    for (int i = klass->GetSuperClass()->GetVTableLength() - 1; i >= 0; --i) {
      auto* m = klass->GetVTableEntry(i, image_pointer_size_);
      auto* super_m = klass->GetSuperClass()->GetVTableEntry(i, image_pointer_size_);
      if (m != super_m) {
        if (UNLIKELY(!HasSameSignatureWithDifferentClassLoaders(self,
                                                                klass,
                                                                super_klass,
                                                                m,
                                                                super_m))) {
          self->AssertPendingException();
          return false;
        }
      }
    }
  }
  for (int32_t i = 0; i < klass->GetIfTableCount(); ++i) {
    super_klass.Assign(klass->GetIfTable()->GetInterface(i));
    if (klass->GetClassLoader() != super_klass->GetClassLoader()) {
      uint32_t num_methods = super_klass->NumVirtualMethods();
      for (uint32_t j = 0; j < num_methods; ++j) {
        auto* m = klass->GetIfTable()->GetMethodArray(i)->GetElementPtrSize<ArtMethod*>(
            j, image_pointer_size_);
        auto* super_m = super_klass->GetVirtualMethod(j, image_pointer_size_);
        if (m != super_m) {
          if (UNLIKELY(!HasSameSignatureWithDifferentClassLoaders(self,
                                                                  klass,
                                                                  super_klass,
                                                                  m,
                                                                  super_m))) {
            self->AssertPendingException();
            return false;
          }
        }
      }
    }
  }
  return true;
}

bool ClassLinker::EnsureInitialized(Thread* self,
                                    Handle<mirror::Class> c,
                                    bool can_init_fields,
                                    bool can_init_parents) {
  DCHECK(c != nullptr);

  if (c->IsInitialized()) {
    DCHECK(c->WasVerificationAttempted()) << c->PrettyClassAndClassLoader();
    return true;
  }
  // SubtypeCheckInfo::Initialized must happen-before any new-instance for that type.
  //
  // Ensure the bitstring is initialized before any of the class initialization
  // logic occurs. Once a class initializer starts running, objects can
  // escape into the heap and use the subtype checking code.
  //
  // Note: A class whose SubtypeCheckInfo is at least Initialized means it
  // can be used as a source for the IsSubClass check, and that all ancestors
  // of the class are Assigned (can be used as a target for IsSubClass check)
  // or Overflowed (can be used as a source for IsSubClass check).
  if (kBitstringSubtypeCheckEnabled) {
    MutexLock subtype_check_lock(Thread::Current(), *Locks::subtype_check_lock_);
    SubtypeCheck<ObjPtr<mirror::Class>>::EnsureInitialized(c.Get());
    // TODO: Avoid taking subtype_check_lock_ if SubtypeCheck is already initialized.
  }
  const bool success = InitializeClass(self, c, can_init_fields, can_init_parents);
  if (!success) {
    if (can_init_fields && can_init_parents) {
      CHECK(self->IsExceptionPending()) << c->PrettyClass();
    }
  } else {
    self->AssertNoPendingException();
  }
  return success;
}

void ClassLinker::FixupTemporaryDeclaringClass(ObjPtr<mirror::Class> temp_class,
                                               ObjPtr<mirror::Class> new_class) {
  DCHECK_EQ(temp_class->NumInstanceFields(), 0u);
  for (ArtField& field : new_class->GetIFields()) {
    if (field.GetDeclaringClass() == temp_class) {
      field.SetDeclaringClass(new_class);
    }
  }

  DCHECK_EQ(temp_class->NumStaticFields(), 0u);
  for (ArtField& field : new_class->GetSFields()) {
    if (field.GetDeclaringClass() == temp_class) {
      field.SetDeclaringClass(new_class);
    }
  }

  DCHECK_EQ(temp_class->NumDirectMethods(), 0u);
  DCHECK_EQ(temp_class->NumVirtualMethods(), 0u);
  for (auto& method : new_class->GetMethods(image_pointer_size_)) {
    if (method.GetDeclaringClass() == temp_class) {
      method.SetDeclaringClass(new_class);
    }
  }

  // Make sure the remembered set and mod-union tables know that we updated some of the native
  // roots.
  WriteBarrier::ForEveryFieldWrite(new_class);
}

void ClassLinker::RegisterClassLoader(ObjPtr<mirror::ClassLoader> class_loader) {
  CHECK(class_loader->GetAllocator() == nullptr);
  CHECK(class_loader->GetClassTable() == nullptr);
  Thread* const self = Thread::Current();
  ClassLoaderData data;
  data.weak_root = self->GetJniEnv()->GetVm()->AddWeakGlobalRef(self, class_loader);
  // Create and set the class table.
  data.class_table = new ClassTable;
  class_loader->SetClassTable(data.class_table);
  // Create and set the linear allocator.
  data.allocator = Runtime::Current()->CreateLinearAlloc();
  class_loader->SetAllocator(data.allocator);
  // Add to the list so that we know to free the data later.
  class_loaders_.push_back(data);
}

ClassTable* ClassLinker::InsertClassTableForClassLoader(ObjPtr<mirror::ClassLoader> class_loader) {
  if (class_loader == nullptr) {
    return boot_class_table_.get();
  }
  ClassTable* class_table = class_loader->GetClassTable();
  if (class_table == nullptr) {
    RegisterClassLoader(class_loader);
    class_table = class_loader->GetClassTable();
    DCHECK(class_table != nullptr);
  }
  return class_table;
}

ClassTable* ClassLinker::ClassTableForClassLoader(ObjPtr<mirror::ClassLoader> class_loader) {
  return class_loader == nullptr ? boot_class_table_.get() : class_loader->GetClassTable();
}

static ImTable* FindSuperImt(ObjPtr<mirror::Class> klass, PointerSize pointer_size)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  while (klass->HasSuperClass()) {
    klass = klass->GetSuperClass();
    if (klass->ShouldHaveImt()) {
      return klass->GetImt(pointer_size);
    }
  }
  return nullptr;
}

bool ClassLinker::LinkClass(Thread* self,
                            const char* descriptor,
                            Handle<mirror::Class> klass,
                            Handle<mirror::ObjectArray<mirror::Class>> interfaces,
                            MutableHandle<mirror::Class>* h_new_class_out) {
  CHECK_EQ(ClassStatus::kLoaded, klass->GetStatus());

  if (!LinkSuperClass(klass)) {
    return false;
  }
  ArtMethod* imt_data[ImTable::kSize];
  // If there are any new conflicts compared to super class.
  bool new_conflict = false;
  std::fill_n(imt_data, arraysize(imt_data), Runtime::Current()->GetImtUnimplementedMethod());
  if (!LinkMethods(self, klass, interfaces, &new_conflict, imt_data)) {
    return false;
  }
  if (!LinkInstanceFields(self, klass)) {
    return false;
  }
  size_t class_size;
  if (!LinkStaticFields(self, klass, &class_size)) {
    return false;
  }
  CreateReferenceInstanceOffsets(klass);
  CHECK_EQ(ClassStatus::kLoaded, klass->GetStatus());

  ImTable* imt = nullptr;
  if (klass->ShouldHaveImt()) {
    // If there are any new conflicts compared to the super class we can not make a copy. There
    // can be cases where both will have a conflict method at the same slot without having the same
    // set of conflicts. In this case, we can not share the IMT since the conflict table slow path
    // will possibly create a table that is incorrect for either of the classes.
    // Same IMT with new_conflict does not happen very often.
    if (!new_conflict) {
      ImTable* super_imt = FindSuperImt(klass.Get(), image_pointer_size_);
      if (super_imt != nullptr) {
        bool imt_equals = true;
        for (size_t i = 0; i < ImTable::kSize && imt_equals; ++i) {
          imt_equals = imt_equals && (super_imt->Get(i, image_pointer_size_) == imt_data[i]);
        }
        if (imt_equals) {
          imt = super_imt;
        }
      }
    }
    if (imt == nullptr) {
      LinearAlloc* allocator = GetAllocatorForClassLoader(klass->GetClassLoader());
      imt = reinterpret_cast<ImTable*>(
          allocator->Alloc(self, ImTable::SizeInBytes(image_pointer_size_)));
      if (imt == nullptr) {
        return false;
      }
      imt->Populate(imt_data, image_pointer_size_);
    }
  }

  if (!klass->IsTemp() || (!init_done_ && klass->GetClassSize() == class_size)) {
    // We don't need to retire this class as it has no embedded tables or it was created the
    // correct size during class linker initialization.
    CHECK_EQ(klass->GetClassSize(), class_size) << klass->PrettyDescriptor();

    if (klass->ShouldHaveEmbeddedVTable()) {
      klass->PopulateEmbeddedVTable(image_pointer_size_);
    }
    if (klass->ShouldHaveImt()) {
      klass->SetImt(imt, image_pointer_size_);
    }

    // Update CHA info based on whether we override methods.
    // Have to do this before setting the class as resolved which allows
    // instantiation of klass.
    if (cha_ != nullptr) {
      cha_->UpdateAfterLoadingOf(klass);
    }

    // This will notify waiters on klass that saw the not yet resolved
    // class in the class_table_ during EnsureResolved.
    mirror::Class::SetStatus(klass, ClassStatus::kResolved, self);
    h_new_class_out->Assign(klass.Get());
  } else {
    CHECK(!klass->IsResolved());
    // Retire the temporary class and create the correctly sized resolved class.
    StackHandleScope<1> hs(self);
    auto h_new_class = hs.NewHandle(klass->CopyOf(self, class_size, imt, image_pointer_size_));
    // Set arrays to null since we don't want to have multiple classes with the same ArtField or
    // ArtMethod array pointers. If this occurs, it causes bugs in remembered sets since the GC
    // may not see any references to the target space and clean the card for a class if another
    // class had the same array pointer.
    klass->SetMethodsPtrUnchecked(nullptr, 0, 0);
    klass->SetSFieldsPtrUnchecked(nullptr);
    klass->SetIFieldsPtrUnchecked(nullptr);
    if (UNLIKELY(h_new_class == nullptr)) {
      self->AssertPendingOOMException();
      mirror::Class::SetStatus(klass, ClassStatus::kErrorUnresolved, self);
      return false;
    }

    CHECK_EQ(h_new_class->GetClassSize(), class_size);
    ObjectLock<mirror::Class> lock(self, h_new_class);
    FixupTemporaryDeclaringClass(klass.Get(), h_new_class.Get());

    {
      WriterMutexLock mu(self, *Locks::classlinker_classes_lock_);
      const ObjPtr<mirror::ClassLoader> class_loader = h_new_class.Get()->GetClassLoader();
      ClassTable* const table = InsertClassTableForClassLoader(class_loader);
      const ObjPtr<mirror::Class> existing =
          table->UpdateClass(descriptor, h_new_class.Get(), ComputeModifiedUtf8Hash(descriptor));
      if (class_loader != nullptr) {
        // We updated the class in the class table, perform the write barrier so that the GC knows
        // about the change.
        WriteBarrier::ForEveryFieldWrite(class_loader);
      }
      CHECK_EQ(existing, klass.Get());
      if (log_new_roots_) {
        new_class_roots_.push_back(GcRoot<mirror::Class>(h_new_class.Get()));
      }
    }

    // Update CHA info based on whether we override methods.
    // Have to do this before setting the class as resolved which allows
    // instantiation of klass.
    if (cha_ != nullptr) {
      cha_->UpdateAfterLoadingOf(h_new_class);
    }

    // This will notify waiters on temp class that saw the not yet resolved class in the
    // class_table_ during EnsureResolved.
    mirror::Class::SetStatus(klass, ClassStatus::kRetired, self);

    CHECK_EQ(h_new_class->GetStatus(), ClassStatus::kResolving);
    // This will notify waiters on new_class that saw the not yet resolved
    // class in the class_table_ during EnsureResolved.
    mirror::Class::SetStatus(h_new_class, ClassStatus::kResolved, self);
    // Return the new class.
    h_new_class_out->Assign(h_new_class.Get());
  }
  return true;
}

bool ClassLinker::LoadSuperAndInterfaces(Handle<mirror::Class> klass, const DexFile& dex_file) {
  CHECK_EQ(ClassStatus::kIdx, klass->GetStatus());
  const dex::ClassDef& class_def = dex_file.GetClassDef(klass->GetDexClassDefIndex());
  dex::TypeIndex super_class_idx = class_def.superclass_idx_;
  if (super_class_idx.IsValid()) {
    // Check that a class does not inherit from itself directly.
    //
    // TODO: This is a cheap check to detect the straightforward case
    // of a class extending itself (b/28685551), but we should do a
    // proper cycle detection on loaded classes, to detect all cases
    // of class circularity errors (b/28830038).
    if (super_class_idx == class_def.class_idx_) {
      ThrowClassCircularityError(klass.Get(),
                                 "Class %s extends itself",
                                 klass->PrettyDescriptor().c_str());
      return false;
    }

    ObjPtr<mirror::Class> super_class = ResolveType(super_class_idx, klass.Get());
    if (super_class == nullptr) {
      DCHECK(Thread::Current()->IsExceptionPending());
      return false;
    }
    // Verify
    if (!klass->CanAccess(super_class)) {
      ThrowIllegalAccessError(klass.Get(), "Class %s extended by class %s is inaccessible",
                              super_class->PrettyDescriptor().c_str(),
                              klass->PrettyDescriptor().c_str());
      return false;
    }
    CHECK(super_class->IsResolved());
    klass->SetSuperClass(super_class);
  }
  const dex::TypeList* interfaces = dex_file.GetInterfacesList(class_def);
  if (interfaces != nullptr) {
    for (size_t i = 0; i < interfaces->Size(); i++) {
      dex::TypeIndex idx = interfaces->GetTypeItem(i).type_idx_;
      ObjPtr<mirror::Class> interface = ResolveType(idx, klass.Get());
      if (interface == nullptr) {
        DCHECK(Thread::Current()->IsExceptionPending());
        return false;
      }
      // Verify
      if (!klass->CanAccess(interface)) {
        // TODO: the RI seemed to ignore this in my testing.
        ThrowIllegalAccessError(klass.Get(),
                                "Interface %s implemented by class %s is inaccessible",
                                interface->PrettyDescriptor().c_str(),
                                klass->PrettyDescriptor().c_str());
        return false;
      }
    }
  }
  // Mark the class as loaded.
  mirror::Class::SetStatus(klass, ClassStatus::kLoaded, nullptr);
  return true;
}

bool ClassLinker::LinkSuperClass(Handle<mirror::Class> klass) {
  CHECK(!klass->IsPrimitive());
  ObjPtr<mirror::Class> super = klass->GetSuperClass();
  ObjPtr<mirror::Class> object_class = GetClassRoot<mirror::Object>(this);
  if (klass.Get() == object_class) {
    if (super != nullptr) {
      ThrowClassFormatError(klass.Get(), "java.lang.Object must not have a superclass");
      return false;
    }
    return true;
  }
  if (super == nullptr) {
    ThrowLinkageError(klass.Get(), "No superclass defined for class %s",
                      klass->PrettyDescriptor().c_str());
    return false;
  }
  // Verify
  if (klass->IsInterface() && super != object_class) {
    ThrowClassFormatError(klass.Get(), "Interfaces must have java.lang.Object as superclass");
    return false;
  }
  if (super->IsFinal()) {
    ThrowVerifyError(klass.Get(),
                     "Superclass %s of %s is declared final",
                     super->PrettyDescriptor().c_str(),
                     klass->PrettyDescriptor().c_str());
    return false;
  }
  if (super->IsInterface()) {
    ThrowIncompatibleClassChangeError(klass.Get(),
                                      "Superclass %s of %s is an interface",
                                      super->PrettyDescriptor().c_str(),
                                      klass->PrettyDescriptor().c_str());
    return false;
  }
  if (!klass->CanAccess(super)) {
    ThrowIllegalAccessError(klass.Get(), "Superclass %s is inaccessible to class %s",
                            super->PrettyDescriptor().c_str(),
                            klass->PrettyDescriptor().c_str());
    return false;
  }

  // Inherit kAccClassIsFinalizable from the superclass in case this
  // class doesn't override finalize.
  if (super->IsFinalizable()) {
    klass->SetFinalizable();
  }

  // Inherit class loader flag form super class.
  if (super->IsClassLoaderClass()) {
    klass->SetClassLoaderClass();
  }

  // Inherit reference flags (if any) from the superclass.
  uint32_t reference_flags = (super->GetClassFlags() & mirror::kClassFlagReference);
  if (reference_flags != 0) {
    CHECK_EQ(klass->GetClassFlags(), 0u);
    klass->SetClassFlags(klass->GetClassFlags() | reference_flags);
  }
  // Disallow custom direct subclasses of java.lang.ref.Reference.
  if (init_done_ && super == GetClassRoot<mirror::Reference>(this)) {
    ThrowLinkageError(klass.Get(),
                      "Class %s attempts to subclass java.lang.ref.Reference, which is not allowed",
                      klass->PrettyDescriptor().c_str());
    return false;
  }

  if (kIsDebugBuild) {
    // Ensure super classes are fully resolved prior to resolving fields..
    while (super != nullptr) {
      CHECK(super->IsResolved());
      super = super->GetSuperClass();
    }
  }
  return true;
}

// Populate the class vtable and itable. Compute return type indices.
bool ClassLinker::LinkMethods(Thread* self,
                              Handle<mirror::Class> klass,
                              Handle<mirror::ObjectArray<mirror::Class>> interfaces,
                              bool* out_new_conflict,
                              ArtMethod** out_imt) {
  self->AllowThreadSuspension();
  // A map from vtable indexes to the method they need to be updated to point to. Used because we
  // need to have default methods be in the virtuals array of each class but we don't set that up
  // until LinkInterfaceMethods.
  std::unordered_map<size_t, ClassLinker::MethodTranslation> default_translations;
  // Link virtual methods then interface methods.
  // We set up the interface lookup table first because we need it to determine if we need to update
  // any vtable entries with new default method implementations.
  return SetupInterfaceLookupTable(self, klass, interfaces)
          && LinkVirtualMethods(self, klass, /*out*/ &default_translations)
          && LinkInterfaceMethods(self, klass, default_translations, out_new_conflict, out_imt);
}

// Comparator for name and signature of a method, used in finding overriding methods. Implementation
// avoids the use of handles, if it didn't then rather than compare dex files we could compare dex
// caches in the implementation below.
class MethodNameAndSignatureComparator final : public ValueObject {
 public:
  explicit MethodNameAndSignatureComparator(ArtMethod* method)
      REQUIRES_SHARED(Locks::mutator_lock_) :
      dex_file_(method->GetDexFile()), mid_(&dex_file_->GetMethodId(method->GetDexMethodIndex())),
      name_(nullptr), name_len_(0) {
    DCHECK(!method->IsProxyMethod()) << method->PrettyMethod();
  }

  const char* GetName() {
    if (name_ == nullptr) {
      name_ = dex_file_->StringDataAndUtf16LengthByIdx(mid_->name_idx_, &name_len_);
    }
    return name_;
  }

  bool HasSameNameAndSignature(ArtMethod* other)
      REQUIRES_SHARED(Locks::mutator_lock_) {
    DCHECK(!other->IsProxyMethod()) << other->PrettyMethod();
    const DexFile* other_dex_file = other->GetDexFile();
    const dex::MethodId& other_mid = other_dex_file->GetMethodId(other->GetDexMethodIndex());
    if (dex_file_ == other_dex_file) {
      return mid_->name_idx_ == other_mid.name_idx_ && mid_->proto_idx_ == other_mid.proto_idx_;
    }
    GetName();  // Only used to make sure its calculated.
    uint32_t other_name_len;
    const char* other_name = other_dex_file->StringDataAndUtf16LengthByIdx(other_mid.name_idx_,
                                                                           &other_name_len);
    if (name_len_ != other_name_len || strcmp(name_, other_name) != 0) {
      return false;
    }
    return dex_file_->GetMethodSignature(*mid_) == other_dex_file->GetMethodSignature(other_mid);
  }

 private:
  // Dex file for the method to compare against.
  const DexFile* const dex_file_;
  // MethodId for the method to compare against.
  const dex::MethodId* const mid_;
  // Lazily computed name from the dex file's strings.
  const char* name_;
  // Lazily computed name length.
  uint32_t name_len_;
};

class LinkVirtualHashTable {
 public:
  LinkVirtualHashTable(Handle<mirror::Class> klass,
                       size_t hash_size,
                       uint32_t* hash_table,
                       PointerSize image_pointer_size)
     : klass_(klass),
       hash_size_(hash_size),
       hash_table_(hash_table),
       image_pointer_size_(image_pointer_size) {
    std::fill(hash_table_, hash_table_ + hash_size_, invalid_index_);
  }

  void Add(uint32_t virtual_method_index) REQUIRES_SHARED(Locks::mutator_lock_) {
    ArtMethod* local_method = klass_->GetVirtualMethodDuringLinking(
        virtual_method_index, image_pointer_size_);
    const char* name = local_method->GetInterfaceMethodIfProxy(image_pointer_size_)->GetName();
    uint32_t hash = ComputeModifiedUtf8Hash(name);
    uint32_t index = hash % hash_size_;
    // Linear probe until we have an empty slot.
    while (hash_table_[index] != invalid_index_) {
      if (++index == hash_size_) {
        index = 0;
      }
    }
    hash_table_[index] = virtual_method_index;
  }

  uint32_t FindAndRemove(MethodNameAndSignatureComparator* comparator)
      REQUIRES_SHARED(Locks::mutator_lock_) {
    const char* name = comparator->GetName();
    uint32_t hash = ComputeModifiedUtf8Hash(name);
    size_t index = hash % hash_size_;
    while (true) {
      const uint32_t value = hash_table_[index];
      // Since linear probe makes continuous blocks, hitting an invalid index means we are done
      // the block and can safely assume not found.
      if (value == invalid_index_) {
        break;
      }
      if (value != removed_index_) {  // This signifies not already overriden.
        ArtMethod* virtual_method =
            klass_->GetVirtualMethodDuringLinking(value, image_pointer_size_);
        if (comparator->HasSameNameAndSignature(
            virtual_method->GetInterfaceMethodIfProxy(image_pointer_size_))) {
          hash_table_[index] = removed_index_;
          return value;
        }
      }
      if (++index == hash_size_) {
        index = 0;
      }
    }
    return GetNotFoundIndex();
  }

  static uint32_t GetNotFoundIndex() {
    return invalid_index_;
  }

 private:
  static const uint32_t invalid_index_;
  static const uint32_t removed_index_;

  Handle<mirror::Class> klass_;
  const size_t hash_size_;
  uint32_t* const hash_table_;
  const PointerSize image_pointer_size_;
};

const uint32_t LinkVirtualHashTable::invalid_index_ = std::numeric_limits<uint32_t>::max();
const uint32_t LinkVirtualHashTable::removed_index_ = std::numeric_limits<uint32_t>::max() - 1;

bool ClassLinker::LinkVirtualMethods(
    Thread* self,
    Handle<mirror::Class> klass,
    /*out*/std::unordered_map<size_t, ClassLinker::MethodTranslation>* default_translations) {
  const size_t num_virtual_methods = klass->NumVirtualMethods();
  if (klass->IsInterface()) {
    // No vtable.
    if (!IsUint<16>(num_virtual_methods)) {
      ThrowClassFormatError(klass.Get(), "Too many methods on interface: %zu", num_virtual_methods);
      return false;
    }
    bool has_defaults = false;
    // Assign each method an IMT index and set the default flag.
    for (size_t i = 0; i < num_virtual_methods; ++i) {
      ArtMethod* m = klass->GetVirtualMethodDuringLinking(i, image_pointer_size_);
      m->SetMethodIndex(i);
      if (!m->IsAbstract()) {
        m->SetAccessFlags(m->GetAccessFlags() | kAccDefault);
        has_defaults = true;
      }
    }
    // Mark that we have default methods so that we won't need to scan the virtual_methods_ array
    // during initialization. This is a performance optimization. We could simply traverse the
    // virtual_methods_ array again during initialization.
    if (has_defaults) {
      klass->SetHasDefaultMethods();
    }
    return true;
  } else if (klass->HasSuperClass()) {
    const size_t super_vtable_length = klass->GetSuperClass()->GetVTableLength();
    const size_t max_count = num_virtual_methods + super_vtable_length;
    StackHandleScope<2> hs(self);
    Handle<mirror::Class> super_class(hs.NewHandle(klass->GetSuperClass()));
    MutableHandle<mirror::PointerArray> vtable;
    if (super_class->ShouldHaveEmbeddedVTable()) {
      vtable = hs.NewHandle(AllocPointerArray(self, max_count));
      if (UNLIKELY(vtable == nullptr)) {
        self->AssertPendingOOMException();
        return false;
      }
      for (size_t i = 0; i < super_vtable_length; i++) {
        vtable->SetElementPtrSize(
            i, super_class->GetEmbeddedVTableEntry(i, image_pointer_size_), image_pointer_size_);
      }
      // We might need to change vtable if we have new virtual methods or new interfaces (since that
      // might give us new default methods). If no new interfaces then we can skip the rest since
      // the class cannot override any of the super-class's methods. This is required for
      // correctness since without it we might not update overridden default method vtable entries
      // correctly.
      if (num_virtual_methods == 0 && super_class->GetIfTableCount() == klass->GetIfTableCount()) {
        klass->SetVTable(vtable.Get());
        return true;
      }
    } else {
      DCHECK(super_class->IsAbstract() && !super_class->IsArrayClass());
      ObjPtr<mirror::PointerArray> super_vtable = super_class->GetVTable();
      CHECK(super_vtable != nullptr) << super_class->PrettyClass();
      // We might need to change vtable if we have new virtual methods or new interfaces (since that
      // might give us new default methods). See comment above.
      if (num_virtual_methods == 0 && super_class->GetIfTableCount() == klass->GetIfTableCount()) {
        klass->SetVTable(super_vtable);
        return true;
      }
      vtable = hs.NewHandle(
          ObjPtr<mirror::PointerArray>::DownCast(super_vtable->CopyOf(self, max_count)));
      if (UNLIKELY(vtable == nullptr)) {
        self->AssertPendingOOMException();
        return false;
      }
    }
    // How the algorithm works:
    // 1. Populate hash table by adding num_virtual_methods from klass. The values in the hash
    // table are: invalid_index for unused slots, index super_vtable_length + i for a virtual
    // method which has not been matched to a vtable method, and j if the virtual method at the
    // index overrode the super virtual method at index j.
    // 2. Loop through super virtual methods, if they overwrite, update hash table to j
    // (j < super_vtable_length) to avoid redundant checks. (TODO maybe use this info for reducing
    // the need for the initial vtable which we later shrink back down).
    // 3. Add non overridden methods to the end of the vtable.
    static constexpr size_t kMaxStackHash = 250;
    // + 1 so that even if we only have new default methods we will still be able to use this hash
    // table (i.e. it will never have 0 size).
    const size_t hash_table_size = num_virtual_methods * 3 + 1;
    uint32_t* hash_table_ptr;
    std::unique_ptr<uint32_t[]> hash_heap_storage;
    if (hash_table_size <= kMaxStackHash) {
      hash_table_ptr = reinterpret_cast<uint32_t*>(
          alloca(hash_table_size * sizeof(*hash_table_ptr)));
    } else {
      hash_heap_storage.reset(new uint32_t[hash_table_size]);
      hash_table_ptr = hash_heap_storage.get();
    }
    LinkVirtualHashTable hash_table(klass, hash_table_size, hash_table_ptr, image_pointer_size_);
    // Add virtual methods to the hash table.
    for (size_t i = 0; i < num_virtual_methods; ++i) {
      DCHECK(klass->GetVirtualMethodDuringLinking(
          i, image_pointer_size_)->GetDeclaringClass() != nullptr);
      hash_table.Add(i);
    }
    // Loop through each super vtable method and see if they are overridden by a method we added to
    // the hash table.
    for (size_t j = 0; j < super_vtable_length; ++j) {
      // Search the hash table to see if we are overridden by any method.
      ArtMethod* super_method = vtable->GetElementPtrSize<ArtMethod*>(j, image_pointer_size_);
      if (!klass->CanAccessMember(super_method->GetDeclaringClass(),
                                  super_method->GetAccessFlags())) {
        // Continue on to the next method since this one is package private and canot be overridden.
        // Before Android 4.1, the package-private method super_method might have been incorrectly
        // overridden.
        continue;
      }
      MethodNameAndSignatureComparator super_method_name_comparator(
          super_method->GetInterfaceMethodIfProxy(image_pointer_size_));
      // We remove the method so that subsequent lookups will be faster by making the hash-map
      // smaller as we go on.
      uint32_t hash_index = hash_table.FindAndRemove(&super_method_name_comparator);
      if (hash_index != hash_table.GetNotFoundIndex()) {
        ArtMethod* virtual_method = klass->GetVirtualMethodDuringLinking(
            hash_index, image_pointer_size_);
        if (super_method->IsFinal()) {
          ThrowLinkageError(klass.Get(), "Method %s overrides final method in class %s",
                            virtual_method->PrettyMethod().c_str(),
                            super_method->GetDeclaringClassDescriptor());
          return false;
        }
        vtable->SetElementPtrSize(j, virtual_method, image_pointer_size_);
        virtual_method->SetMethodIndex(j);
      } else if (super_method->IsOverridableByDefaultMethod()) {
        // We didn't directly override this method but we might through default methods...
        // Check for default method update.
        ArtMethod* default_method = nullptr;
        switch (FindDefaultMethodImplementation(self,
                                                super_method,
                                                klass,
                                                /*out*/&default_method)) {
          case DefaultMethodSearchResult::kDefaultConflict: {
            // A conflict was found looking for default methods. Note this (assuming it wasn't
            // pre-existing) in the translations map.
            if (UNLIKELY(!super_method->IsDefaultConflicting())) {
              // Don't generate another conflict method to reduce memory use as an optimization.
              default_translations->insert(
                  {j, ClassLinker::MethodTranslation::CreateConflictingMethod()});
            }
            break;
          }
          case DefaultMethodSearchResult::kAbstractFound: {
            // No conflict but method is abstract.
            // We note that this vtable entry must be made abstract.
            if (UNLIKELY(!super_method->IsAbstract())) {
              default_translations->insert(
                  {j, ClassLinker::MethodTranslation::CreateAbstractMethod()});
            }
            break;
          }
          case DefaultMethodSearchResult::kDefaultFound: {
            if (UNLIKELY(super_method->IsDefaultConflicting() ||
                        default_method->GetDeclaringClass() != super_method->GetDeclaringClass())) {
              // Found a default method implementation that is new.
              // TODO Refactor this add default methods to virtuals here and not in
              //      LinkInterfaceMethods maybe.
              //      The problem is default methods might override previously present
              //      default-method or miranda-method vtable entries from the superclass.
              //      Unfortunately we need these to be entries in this class's virtuals. We do not
              //      give these entries there until LinkInterfaceMethods so we pass this map around
              //      to let it know which vtable entries need to be updated.
              // Make a note that vtable entry j must be updated, store what it needs to be updated
              // to. We will allocate a virtual method slot in LinkInterfaceMethods and fix it up
              // then.
              default_translations->insert(
                  {j, ClassLinker::MethodTranslation::CreateTranslatedMethod(default_method)});
              VLOG(class_linker) << "Method " << super_method->PrettyMethod()
                                 << " overridden by default "
                                 << default_method->PrettyMethod()
                                 << " in " << mirror::Class::PrettyClass(klass.Get());
            }
            break;
          }
        }
      }
    }
    size_t actual_count = super_vtable_length;
    // Add the non-overridden methods at the end.
    for (size_t i = 0; i < num_virtual_methods; ++i) {
      ArtMethod* local_method = klass->GetVirtualMethodDuringLinking(i, image_pointer_size_);
      size_t method_idx = local_method->GetMethodIndexDuringLinking();
      if (method_idx < super_vtable_length &&
          local_method == vtable->GetElementPtrSize<ArtMethod*>(method_idx, image_pointer_size_)) {
        continue;
      }
      vtable->SetElementPtrSize(actual_count, local_method, image_pointer_size_);
      local_method->SetMethodIndex(actual_count);
      ++actual_count;
    }
    if (!IsUint<16>(actual_count)) {
      ThrowClassFormatError(klass.Get(), "Too many methods defined on class: %zd", actual_count);
      return false;
    }
    // Shrink vtable if possible
    CHECK_LE(actual_count, max_count);
    if (actual_count < max_count) {
      vtable.Assign(ObjPtr<mirror::PointerArray>::DownCast(vtable->CopyOf(self, actual_count)));
      if (UNLIKELY(vtable == nullptr)) {
        self->AssertPendingOOMException();
        return false;
      }
    }
    klass->SetVTable(vtable.Get());
  } else {
    CHECK_EQ(klass.Get(), GetClassRoot<mirror::Object>(this));
    if (!IsUint<16>(num_virtual_methods)) {
      ThrowClassFormatError(klass.Get(), "Too many methods: %d",
                            static_cast<int>(num_virtual_methods));
      return false;
    }
    ObjPtr<mirror::PointerArray> vtable = AllocPointerArray(self, num_virtual_methods);
    if (UNLIKELY(vtable == nullptr)) {
      self->AssertPendingOOMException();
      return false;
    }
    for (size_t i = 0; i < num_virtual_methods; ++i) {
      ArtMethod* virtual_method = klass->GetVirtualMethodDuringLinking(i, image_pointer_size_);
      vtable->SetElementPtrSize(i, virtual_method, image_pointer_size_);
      virtual_method->SetMethodIndex(i & 0xFFFF);
    }
    klass->SetVTable(vtable);
  }
  return true;
}

// Determine if the given iface has any subinterface in the given list that declares the method
// specified by 'target'.
//
// Arguments
// - self:    The thread we are running on
// - target:  A comparator that will match any method that overrides the method we are checking for
// - iftable: The iftable we are searching for an overriding method on.
// - ifstart: The index of the interface we are checking to see if anything overrides
// - iface:   The interface we are checking to see if anything overrides.
// - image_pointer_size:
//            The image pointer size.
//
// Returns
// - True:  There is some method that matches the target comparator defined in an interface that
//          is a subtype of iface.
// - False: There is no method that matches the target comparator in any interface that is a subtype
//          of iface.
static bool ContainsOverridingMethodOf(Thread* self,
                                       MethodNameAndSignatureComparator& target,
                                       Handle<mirror::IfTable> iftable,
                                       size_t ifstart,
                                       Handle<mirror::Class> iface,
                                       PointerSize image_pointer_size)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  DCHECK(self != nullptr);
  DCHECK(iface != nullptr);
  DCHECK(iftable != nullptr);
  DCHECK_GE(ifstart, 0u);
  DCHECK_LT(ifstart, iftable->Count());
  DCHECK_EQ(iface.Get(), iftable->GetInterface(ifstart));
  DCHECK(iface->IsInterface());

  size_t iftable_count = iftable->Count();
  StackHandleScope<1> hs(self);
  MutableHandle<mirror::Class> current_iface(hs.NewHandle<mirror::Class>(nullptr));
  for (size_t k = ifstart + 1; k < iftable_count; k++) {
    // Skip ifstart since our current interface obviously cannot override itself.
    current_iface.Assign(iftable->GetInterface(k));
    // Iterate through every method on this interface. The order does not matter.
    for (ArtMethod& current_method : current_iface->GetDeclaredVirtualMethods(image_pointer_size)) {
      if (UNLIKELY(target.HasSameNameAndSignature(
                      current_method.GetInterfaceMethodIfProxy(image_pointer_size)))) {
        // Check if the i'th interface is a subtype of this one.
        if (iface->IsAssignableFrom(current_iface.Get())) {
          return true;
        }
        break;
      }
    }
  }
  return false;
}

// Find the default method implementation for 'interface_method' in 'klass'. Stores it into
// out_default_method and returns kDefaultFound on success. If no default method was found return
// kAbstractFound and store nullptr into out_default_method. If an error occurs (such as a
// default_method conflict) it will return kDefaultConflict.
ClassLinker::DefaultMethodSearchResult ClassLinker::FindDefaultMethodImplementation(
    Thread* self,
    ArtMethod* target_method,
    Handle<mirror::Class> klass,
    /*out*/ArtMethod** out_default_method) const {
  DCHECK(self != nullptr);
  DCHECK(target_method != nullptr);
  DCHECK(out_default_method != nullptr);

  *out_default_method = nullptr;

  // We organize the interface table so that, for interface I any subinterfaces J follow it in the
  // table. This lets us walk the table backwards when searching for default methods.  The first one
  // we encounter is the best candidate since it is the most specific. Once we have found it we keep
  // track of it and then continue checking all other interfaces, since we need to throw an error if
  // we encounter conflicting default method implementations (one is not a subtype of the other).
  //
  // The order of unrelated interfaces does not matter and is not defined.
  size_t iftable_count = klass->GetIfTableCount();
  if (iftable_count == 0) {
    // No interfaces. We have already reset out to null so just return kAbstractFound.
    return DefaultMethodSearchResult::kAbstractFound;
  }

  StackHandleScope<3> hs(self);
  MutableHandle<mirror::Class> chosen_iface(hs.NewHandle<mirror::Class>(nullptr));
  MutableHandle<mirror::IfTable> iftable(hs.NewHandle(klass->GetIfTable()));
  MutableHandle<mirror::Class> iface(hs.NewHandle<mirror::Class>(nullptr));
  MethodNameAndSignatureComparator target_name_comparator(
      target_method->GetInterfaceMethodIfProxy(image_pointer_size_));
  // Iterates over the klass's iftable in reverse
  for (size_t k = iftable_count; k != 0; ) {
    --k;

    DCHECK_LT(k, iftable->Count());

    iface.Assign(iftable->GetInterface(k));
    // Iterate through every declared method on this interface. The order does not matter.
    for (auto& method_iter : iface->GetDeclaredVirtualMethods(image_pointer_size_)) {
      ArtMethod* current_method = &method_iter;
      // Skip abstract methods and methods with different names.
      if (current_method->IsAbstract() ||
          !target_name_comparator.HasSameNameAndSignature(
              current_method->GetInterfaceMethodIfProxy(image_pointer_size_))) {
        continue;
      } else if (!current_method->IsPublic()) {
        // The verifier should have caught the non-public method for dex version 37. Just warn and
        // skip it since this is from before default-methods so we don't really need to care that it
        // has code.
        LOG(WARNING) << "Interface method " << current_method->PrettyMethod()
                     << " is not public! "
                     << "This will be a fatal error in subsequent versions of android. "
                     << "Continuing anyway.";
      }
      if (UNLIKELY(chosen_iface != nullptr)) {
        // We have multiple default impls of the same method. This is a potential default conflict.
        // We need to check if this possibly conflicting method is either a superclass of the chosen
        // default implementation or is overridden by a non-default interface method. In either case
        // there is no conflict.
        if (!iface->IsAssignableFrom(chosen_iface.Get()) &&
            !ContainsOverridingMethodOf(self,
                                        target_name_comparator,
                                        iftable,
                                        k,
                                        iface,
                                        image_pointer_size_)) {
          VLOG(class_linker) << "Conflicting default method implementations found: "
                             << current_method->PrettyMethod() << " and "
                             << ArtMethod::PrettyMethod(*out_default_method) << " in class "
                             << klass->PrettyClass() << " conflict.";
          *out_default_method = nullptr;
          return DefaultMethodSearchResult::kDefaultConflict;
        } else {
          break;  // Continue checking at the next interface.
        }
      } else {
        // chosen_iface == null
        if (!ContainsOverridingMethodOf(self,
                                        target_name_comparator,
                                        iftable,
                                        k,
                                        iface,
                                        image_pointer_size_)) {
          // Don't set this as the chosen interface if something else is overriding it (because that
          // other interface would be potentially chosen instead if it was default). If the other
          // interface was abstract then we wouldn't select this interface as chosen anyway since
          // the abstract method masks it.
          *out_default_method = current_method;
          chosen_iface.Assign(iface.Get());
          // We should now finish traversing the graph to find if we have default methods that
          // conflict.
        } else {
          VLOG(class_linker) << "A default method '" << current_method->PrettyMethod()
                             << "' was "
                             << "skipped because it was overridden by an abstract method in a "
                             << "subinterface on class '" << klass->PrettyClass() << "'";
        }
      }
      break;
    }
  }
  if (*out_default_method != nullptr) {
    VLOG(class_linker) << "Default method '" << (*out_default_method)->PrettyMethod()
                       << "' selected "
                       << "as the implementation for '" << target_method->PrettyMethod()
                       << "' in '" << klass->PrettyClass() << "'";
    return DefaultMethodSearchResult::kDefaultFound;
  } else {
    return DefaultMethodSearchResult::kAbstractFound;
  }
}

ArtMethod* ClassLinker::AddMethodToConflictTable(ObjPtr<mirror::Class> klass,
                                                 ArtMethod* conflict_method,
                                                 ArtMethod* interface_method,
                                                 ArtMethod* method,
                                                 bool force_new_conflict_method) {
  ImtConflictTable* current_table = conflict_method->GetImtConflictTable(kRuntimePointerSize);
  Runtime* const runtime = Runtime::Current();
  LinearAlloc* linear_alloc = GetAllocatorForClassLoader(klass->GetClassLoader());
  bool new_entry = conflict_method == runtime->GetImtConflictMethod() || force_new_conflict_method;

  // Create a new entry if the existing one is the shared conflict method.
  ArtMethod* new_conflict_method = new_entry
      ? runtime->CreateImtConflictMethod(linear_alloc)
      : conflict_method;

  // Allocate a new table. Note that we will leak this table at the next conflict,
  // but that's a tradeoff compared to making the table fixed size.
  void* data = linear_alloc->Alloc(
      Thread::Current(), ImtConflictTable::ComputeSizeWithOneMoreEntry(current_table,
                                                                       image_pointer_size_));
  if (data == nullptr) {
    LOG(ERROR) << "Failed to allocate conflict table";
    return conflict_method;
  }
  ImtConflictTable* new_table = new (data) ImtConflictTable(current_table,
                                                            interface_method,
                                                            method,
                                                            image_pointer_size_);

  // Do a fence to ensure threads see the data in the table before it is assigned
  // to the conflict method.
  // Note that there is a race in the presence of multiple threads and we may leak
  // memory from the LinearAlloc, but that's a tradeoff compared to using
  // atomic operations.
  std::atomic_thread_fence(std::memory_order_release);
  new_conflict_method->SetImtConflictTable(new_table, image_pointer_size_);
  return new_conflict_method;
}

bool ClassLinker::AllocateIfTableMethodArrays(Thread* self,
                                              Handle<mirror::Class> klass,
                                              Handle<mirror::IfTable> iftable) {
  DCHECK(!klass->IsInterface());
  const bool has_superclass = klass->HasSuperClass();
  const bool extend_super_iftable = has_superclass;
  const size_t ifcount = klass->GetIfTableCount();
  const size_t super_ifcount = has_superclass ? klass->GetSuperClass()->GetIfTableCount() : 0U;
  for (size_t i = 0; i < ifcount; ++i) {
    size_t num_methods = iftable->GetInterface(i)->NumDeclaredVirtualMethods();
    if (num_methods > 0) {
      const bool is_super = i < super_ifcount;
      // This is an interface implemented by a super-class. Therefore we can just copy the method
      // array from the superclass.
      const bool super_interface = is_super && extend_super_iftable;
      ObjPtr<mirror::PointerArray> method_array;
      if (super_interface) {
        ObjPtr<mirror::IfTable> if_table = klass->GetSuperClass()->GetIfTable();
        DCHECK(if_table != nullptr);
        DCHECK(if_table->GetMethodArray(i) != nullptr);
        // If we are working on a super interface, try extending the existing method array.
        method_array = ObjPtr<mirror::PointerArray>::DownCast(
            if_table->GetMethodArray(i)->Clone(self));
      } else {
        method_array = AllocPointerArray(self, num_methods);
      }
      if (UNLIKELY(method_array == nullptr)) {
        self->AssertPendingOOMException();
        return false;
      }
      iftable->SetMethodArray(i, method_array);
    }
  }
  return true;
}

void ClassLinker::SetIMTRef(ArtMethod* unimplemented_method,
                            ArtMethod* imt_conflict_method,
                            ArtMethod* current_method,
                            /*out*/bool* new_conflict,
                            /*out*/ArtMethod** imt_ref) {
  // Place method in imt if entry is empty, place conflict otherwise.
  if (*imt_ref == unimplemented_method) {
    *imt_ref = current_method;
  } else if (!(*imt_ref)->IsRuntimeMethod()) {
    // If we are not a conflict and we have the same signature and name as the imt
    // entry, it must be that we overwrote a superclass vtable entry.
    // Note that we have checked IsRuntimeMethod, as there may be multiple different
    // conflict methods.
    MethodNameAndSignatureComparator imt_comparator(
        (*imt_ref)->GetInterfaceMethodIfProxy(image_pointer_size_));
    if (imt_comparator.HasSameNameAndSignature(
          current_method->GetInterfaceMethodIfProxy(image_pointer_size_))) {
      *imt_ref = current_method;
    } else {
      *imt_ref = imt_conflict_method;
      *new_conflict = true;
    }
  } else {
    // Place the default conflict method. Note that there may be an existing conflict
    // method in the IMT, but it could be one tailored to the super class, with a
    // specific ImtConflictTable.
    *imt_ref = imt_conflict_method;
    *new_conflict = true;
  }
}

void ClassLinker::FillIMTAndConflictTables(ObjPtr<mirror::Class> klass) {
  DCHECK(klass->ShouldHaveImt()) << klass->PrettyClass();
  DCHECK(!klass->IsTemp()) << klass->PrettyClass();
  ArtMethod* imt_data[ImTable::kSize];
  Runtime* const runtime = Runtime::Current();
  ArtMethod* const unimplemented_method = runtime->GetImtUnimplementedMethod();
  ArtMethod* const conflict_method = runtime->GetImtConflictMethod();
  std::fill_n(imt_data, arraysize(imt_data), unimplemented_method);
  if (klass->GetIfTable() != nullptr) {
    bool new_conflict = false;
    FillIMTFromIfTable(klass->GetIfTable(),
                       unimplemented_method,
                       conflict_method,
                       klass,
                       /*create_conflict_tables=*/true,
                       /*ignore_copied_methods=*/false,
                       &new_conflict,
                       &imt_data[0]);
  }
  if (!klass->ShouldHaveImt()) {
    return;
  }
  // Compare the IMT with the super class including the conflict methods. If they are equivalent,
  // we can just use the same pointer.
  ImTable* imt = nullptr;
  ObjPtr<mirror::Class> super_class = klass->GetSuperClass();
  if (super_class != nullptr && super_class->ShouldHaveImt()) {
    ImTable* super_imt = super_class->GetImt(image_pointer_size_);
    bool same = true;
    for (size_t i = 0; same && i < ImTable::kSize; ++i) {
      ArtMethod* method = imt_data[i];
      ArtMethod* super_method = super_imt->Get(i, image_pointer_size_);
      if (method != super_method) {
        bool is_conflict_table = method->IsRuntimeMethod() &&
                                 method != unimplemented_method &&
                                 method != conflict_method;
        // Verify conflict contents.
        bool super_conflict_table = super_method->IsRuntimeMethod() &&
                                    super_method != unimplemented_method &&
                                    super_method != conflict_method;
        if (!is_conflict_table || !super_conflict_table) {
          same = false;
        } else {
          ImtConflictTable* table1 = method->GetImtConflictTable(image_pointer_size_);
          ImtConflictTable* table2 = super_method->GetImtConflictTable(image_pointer_size_);
          same = same && table1->Equals(table2, image_pointer_size_);
        }
      }
    }
    if (same) {
      imt = super_imt;
    }
  }
  if (imt == nullptr) {
    imt = klass->GetImt(image_pointer_size_);
    DCHECK(imt != nullptr);
    imt->Populate(imt_data, image_pointer_size_);
  } else {
    klass->SetImt(imt, image_pointer_size_);
  }
}

ImtConflictTable* ClassLinker::CreateImtConflictTable(size_t count,
                                                      LinearAlloc* linear_alloc,
                                                      PointerSize image_pointer_size) {
  void* data = linear_alloc->Alloc(Thread::Current(),
                                   ImtConflictTable::ComputeSize(count,
                                                                 image_pointer_size));
  return (data != nullptr) ? new (data) ImtConflictTable(count, image_pointer_size) : nullptr;
}

ImtConflictTable* ClassLinker::CreateImtConflictTable(size_t count, LinearAlloc* linear_alloc) {
  return CreateImtConflictTable(count, linear_alloc, image_pointer_size_);
}

void ClassLinker::FillIMTFromIfTable(ObjPtr<mirror::IfTable> if_table,
                                     ArtMethod* unimplemented_method,
                                     ArtMethod* imt_conflict_method,
                                     ObjPtr<mirror::Class> klass,
                                     bool create_conflict_tables,
                                     bool ignore_copied_methods,
                                     /*out*/bool* new_conflict,
                                     /*out*/ArtMethod** imt) {
  uint32_t conflict_counts[ImTable::kSize] = {};
  for (size_t i = 0, length = if_table->Count(); i < length; ++i) {
    ObjPtr<mirror::Class> interface = if_table->GetInterface(i);
    const size_t num_virtuals = interface->NumVirtualMethods();
    const size_t method_array_count = if_table->GetMethodArrayCount(i);
    // Virtual methods can be larger than the if table methods if there are default methods.
    DCHECK_GE(num_virtuals, method_array_count);
    if (kIsDebugBuild) {
      if (klass->IsInterface()) {
        DCHECK_EQ(method_array_count, 0u);
      } else {
        DCHECK_EQ(interface->NumDeclaredVirtualMethods(), method_array_count);
      }
    }
    if (method_array_count == 0) {
      continue;
    }
    ObjPtr<mirror::PointerArray> method_array = if_table->GetMethodArray(i);
    for (size_t j = 0; j < method_array_count; ++j) {
      ArtMethod* implementation_method =
          method_array->GetElementPtrSize<ArtMethod*>(j, image_pointer_size_);
      if (ignore_copied_methods && implementation_method->IsCopied()) {
        continue;
      }
      DCHECK(implementation_method != nullptr);
      // Miranda methods cannot be used to implement an interface method, but they are safe to put
      // in the IMT since their entrypoint is the interface trampoline. If we put any copied methods
      // or interface methods in the IMT here they will not create extra conflicts since we compare
      // names and signatures in SetIMTRef.
      ArtMethod* interface_method = interface->GetVirtualMethod(j, image_pointer_size_);
      const uint32_t imt_index = interface_method->GetImtIndex();

      // There is only any conflicts if all of the interface methods for an IMT slot don't have
      // the same implementation method, keep track of this to avoid creating a conflict table in
      // this case.

      // Conflict table size for each IMT slot.
      ++conflict_counts[imt_index];

      SetIMTRef(unimplemented_method,
                imt_conflict_method,
                implementation_method,
                /*out*/new_conflict,
                /*out*/&imt[imt_index]);
    }
  }

  if (create_conflict_tables) {
    // Create the conflict tables.
    LinearAlloc* linear_alloc = GetAllocatorForClassLoader(klass->GetClassLoader());
    for (size_t i = 0; i < ImTable::kSize; ++i) {
      size_t conflicts = conflict_counts[i];
      if (imt[i] == imt_conflict_method) {
        ImtConflictTable* new_table = CreateImtConflictTable(conflicts, linear_alloc);
        if (new_table != nullptr) {
          ArtMethod* new_conflict_method =
              Runtime::Current()->CreateImtConflictMethod(linear_alloc);
          new_conflict_method->SetImtConflictTable(new_table, image_pointer_size_);
          imt[i] = new_conflict_method;
        } else {
          LOG(ERROR) << "Failed to allocate conflict table";
          imt[i] = imt_conflict_method;
        }
      } else {
        DCHECK_NE(imt[i], imt_conflict_method);
      }
    }

    for (size_t i = 0, length = if_table->Count(); i < length; ++i) {
      ObjPtr<mirror::Class> interface = if_table->GetInterface(i);
      const size_t method_array_count = if_table->GetMethodArrayCount(i);
      // Virtual methods can be larger than the if table methods if there are default methods.
      if (method_array_count == 0) {
        continue;
      }
      ObjPtr<mirror::PointerArray> method_array = if_table->GetMethodArray(i);
      for (size_t j = 0; j < method_array_count; ++j) {
        ArtMethod* implementation_method =
            method_array->GetElementPtrSize<ArtMethod*>(j, image_pointer_size_);
        if (ignore_copied_methods && implementation_method->IsCopied()) {
          continue;
        }
        DCHECK(implementation_method != nullptr);
        ArtMethod* interface_method = interface->GetVirtualMethod(j, image_pointer_size_);
        const uint32_t imt_index = interface_method->GetImtIndex();
        if (!imt[imt_index]->IsRuntimeMethod() ||
            imt[imt_index] == unimplemented_method ||
            imt[imt_index] == imt_conflict_method) {
          continue;
        }
        ImtConflictTable* table = imt[imt_index]->GetImtConflictTable(image_pointer_size_);
        const size_t num_entries = table->NumEntries(image_pointer_size_);
        table->SetInterfaceMethod(num_entries, image_pointer_size_, interface_method);
        table->SetImplementationMethod(num_entries, image_pointer_size_, implementation_method);
      }
    }
  }
}

// Simple helper function that checks that no subtypes of 'val' are contained within the 'classes'
// set.
static bool NotSubinterfaceOfAny(
    const std::unordered_set<ObjPtr<mirror::Class>, HashObjPtr>& classes,
    ObjPtr<mirror::Class> val)
    REQUIRES(Roles::uninterruptible_)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  DCHECK(val != nullptr);
  for (ObjPtr<mirror::Class> c : classes) {
    if (val->IsAssignableFrom(c)) {
      return false;
    }
  }
  return true;
}

// Fills in and flattens the interface inheritance hierarchy.
//
// By the end of this function all interfaces in the transitive closure of to_process are added to
// the iftable and every interface precedes all of its sub-interfaces in this list.
//
// all I, J: Interface | I <: J implies J precedes I
//
// (note A <: B means that A is a subtype of B)
//
// This returns the total number of items in the iftable. The iftable might be resized down after
// this call.
//
// We order this backwards so that we do not need to reorder superclass interfaces when new
// interfaces are added in subclass's interface tables.
//
// Upon entry into this function iftable is a copy of the superclass's iftable with the first
// super_ifcount entries filled in with the transitive closure of the interfaces of the superclass.
// The other entries are uninitialized.  We will fill in the remaining entries in this function. The
// iftable must be large enough to hold all interfaces without changing its size.
static size_t FillIfTable(ObjPtr<mirror::IfTable> iftable,
                          size_t super_ifcount,
                          const std::vector<ObjPtr<mirror::Class>>& to_process)
    REQUIRES(Roles::uninterruptible_)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  // This is the set of all class's already in the iftable. Used to make checking if a class has
  // already been added quicker.
  std::unordered_set<ObjPtr<mirror::Class>, HashObjPtr> classes_in_iftable;
  // The first super_ifcount elements are from the superclass. We note that they are already added.
  for (size_t i = 0; i < super_ifcount; i++) {
    ObjPtr<mirror::Class> iface = iftable->GetInterface(i);
    DCHECK(NotSubinterfaceOfAny(classes_in_iftable, iface)) << "Bad ordering.";
    classes_in_iftable.insert(iface);
  }
  size_t filled_ifcount = super_ifcount;
  for (ObjPtr<mirror::Class> interface : to_process) {
    // Let us call the first filled_ifcount elements of iftable the current-iface-list.
    // At this point in the loop current-iface-list has the invariant that:
    //    for every pair of interfaces I,J within it:
    //      if index_of(I) < index_of(J) then I is not a subtype of J

    // If we have already seen this element then all of its super-interfaces must already be in the
    // current-iface-list so we can skip adding it.
    if (!ContainsElement(classes_in_iftable, interface)) {
      // We haven't seen this interface so add all of its super-interfaces onto the
      // current-iface-list, skipping those already on it.
      int32_t ifcount = interface->GetIfTableCount();
      for (int32_t j = 0; j < ifcount; j++) {
        ObjPtr<mirror::Class> super_interface = interface->GetIfTable()->GetInterface(j);
        if (!ContainsElement(classes_in_iftable, super_interface)) {
          DCHECK(NotSubinterfaceOfAny(classes_in_iftable, super_interface)) << "Bad ordering.";
          classes_in_iftable.insert(super_interface);
          iftable->SetInterface(filled_ifcount, super_interface);
          filled_ifcount++;
        }
      }
      DCHECK(NotSubinterfaceOfAny(classes_in_iftable, interface)) << "Bad ordering";
      // Place this interface onto the current-iface-list after all of its super-interfaces.
      classes_in_iftable.insert(interface);
      iftable->SetInterface(filled_ifcount, interface);
      filled_ifcount++;
    } else if (kIsDebugBuild) {
      // Check all super-interfaces are already in the list.
      int32_t ifcount = interface->GetIfTableCount();
      for (int32_t j = 0; j < ifcount; j++) {
        ObjPtr<mirror::Class> super_interface = interface->GetIfTable()->GetInterface(j);
        DCHECK(ContainsElement(classes_in_iftable, super_interface))
            << "Iftable does not contain " << mirror::Class::PrettyClass(super_interface)
            << ", a superinterface of " << interface->PrettyClass();
      }
    }
  }
  if (kIsDebugBuild) {
    // Check that the iftable is ordered correctly.
    for (size_t i = 0; i < filled_ifcount; i++) {
      ObjPtr<mirror::Class> if_a = iftable->GetInterface(i);
      for (size_t j = i + 1; j < filled_ifcount; j++) {
        ObjPtr<mirror::Class> if_b = iftable->GetInterface(j);
        // !(if_a <: if_b)
        CHECK(!if_b->IsAssignableFrom(if_a))
            << "Bad interface order: " << mirror::Class::PrettyClass(if_a) << " (index " << i
            << ") extends "
            << if_b->PrettyClass() << " (index " << j << ") and so should be after it in the "
            << "interface list.";
      }
    }
  }
  return filled_ifcount;
}

bool ClassLinker::SetupInterfaceLookupTable(Thread* self, Handle<mirror::Class> klass,
                                            Handle<mirror::ObjectArray<mirror::Class>> interfaces) {
  StackHandleScope<1> hs(self);
  const bool has_superclass = klass->HasSuperClass();
  const size_t super_ifcount = has_superclass ? klass->GetSuperClass()->GetIfTableCount() : 0U;
  const bool have_interfaces = interfaces != nullptr;
  const size_t num_interfaces =
      have_interfaces ? interfaces->GetLength() : klass->NumDirectInterfaces();
  if (num_interfaces == 0) {
    if (super_ifcount == 0) {
      if (LIKELY(has_superclass)) {
        klass->SetIfTable(klass->GetSuperClass()->GetIfTable());
      }
      // Class implements no interfaces.
      DCHECK_EQ(klass->GetIfTableCount(), 0);
      return true;
    }
    // Class implements same interfaces as parent, are any of these not marker interfaces?
    bool has_non_marker_interface = false;
    ObjPtr<mirror::IfTable> super_iftable = klass->GetSuperClass()->GetIfTable();
    for (size_t i = 0; i < super_ifcount; ++i) {
      if (super_iftable->GetMethodArrayCount(i) > 0) {
        has_non_marker_interface = true;
        break;
      }
    }
    // Class just inherits marker interfaces from parent so recycle parent's iftable.
    if (!has_non_marker_interface) {
      klass->SetIfTable(super_iftable);
      return true;
    }
  }
  size_t ifcount = super_ifcount + num_interfaces;
  // Check that every class being implemented is an interface.
  for (size_t i = 0; i < num_interfaces; i++) {
    ObjPtr<mirror::Class> interface = have_interfaces
        ? interfaces->GetWithoutChecks(i)
        : mirror::Class::GetDirectInterface(self, klass.Get(), i);
    DCHECK(interface != nullptr);
    if (UNLIKELY(!interface->IsInterface())) {
      std::string temp;
      ThrowIncompatibleClassChangeError(klass.Get(),
                                        "Class %s implements non-interface class %s",
                                        klass->PrettyDescriptor().c_str(),
                                        PrettyDescriptor(interface->GetDescriptor(&temp)).c_str());
      return false;
    }
    ifcount += interface->GetIfTableCount();
  }
  // Create the interface function table.
  MutableHandle<mirror::IfTable> iftable(hs.NewHandle(AllocIfTable(self, ifcount)));
  if (UNLIKELY(iftable == nullptr)) {
    self->AssertPendingOOMException();
    return false;
  }
  // Fill in table with superclass's iftable.
  if (super_ifcount != 0) {
    ObjPtr<mirror::IfTable> super_iftable = klass->GetSuperClass()->GetIfTable();
    for (size_t i = 0; i < super_ifcount; i++) {
      ObjPtr<mirror::Class> super_interface = super_iftable->GetInterface(i);
      iftable->SetInterface(i, super_interface);
    }
  }

  // Note that AllowThreadSuspension is to thread suspension as pthread_testcancel is to pthread
  // cancellation. That is it will suspend if one has a pending suspend request but otherwise
  // doesn't really do anything.
  self->AllowThreadSuspension();

  size_t new_ifcount;
  {
    ScopedAssertNoThreadSuspension nts("Copying mirror::Class*'s for FillIfTable");
    std::vector<ObjPtr<mirror::Class>> to_add;
    for (size_t i = 0; i < num_interfaces; i++) {
      ObjPtr<mirror::Class> interface = have_interfaces ? interfaces->Get(i) :
          mirror::Class::GetDirectInterface(self, klass.Get(), i);
      to_add.push_back(interface);
    }

    new_ifcount = FillIfTable(iftable.Get(), super_ifcount, std::move(to_add));
  }

  self->AllowThreadSuspension();

  // Shrink iftable in case duplicates were found
  if (new_ifcount < ifcount) {
    DCHECK_NE(num_interfaces, 0U);
    iftable.Assign(ObjPtr<mirror::IfTable>::DownCast(
        iftable->CopyOf(self, new_ifcount * mirror::IfTable::kMax)));
    if (UNLIKELY(iftable == nullptr)) {
      self->AssertPendingOOMException();
      return false;
    }
    ifcount = new_ifcount;
  } else {
    DCHECK_EQ(new_ifcount, ifcount);
  }
  klass->SetIfTable(iftable.Get());
  return true;
}

// Finds the method with a name/signature that matches cmp in the given lists of methods. The list
// of methods must be unique.
static ArtMethod* FindSameNameAndSignature(MethodNameAndSignatureComparator& cmp ATTRIBUTE_UNUSED) {
  return nullptr;
}

template <typename ... Types>
static ArtMethod* FindSameNameAndSignature(MethodNameAndSignatureComparator& cmp,
                                           const ScopedArenaVector<ArtMethod*>& list,
                                           const Types& ... rest)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  for (ArtMethod* method : list) {
    if (cmp.HasSameNameAndSignature(method)) {
      return method;
    }
  }
  return FindSameNameAndSignature(cmp, rest...);
}

namespace {

// Check that all vtable entries are present in this class's virtuals or are the same as a
// superclasses vtable entry.
void CheckClassOwnsVTableEntries(Thread* self,
                                 Handle<mirror::Class> klass,
                                 PointerSize pointer_size)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  StackHandleScope<2> hs(self);
  Handle<mirror::PointerArray> check_vtable(hs.NewHandle(klass->GetVTableDuringLinking()));
  ObjPtr<mirror::Class> super_temp = (klass->HasSuperClass()) ? klass->GetSuperClass() : nullptr;
  Handle<mirror::Class> superclass(hs.NewHandle(super_temp));
  int32_t super_vtable_length = (superclass != nullptr) ? superclass->GetVTableLength() : 0;
  for (int32_t i = 0; i < check_vtable->GetLength(); ++i) {
    ArtMethod* m = check_vtable->GetElementPtrSize<ArtMethod*>(i, pointer_size);
    CHECK(m != nullptr);

    if (m->GetMethodIndexDuringLinking() != i) {
      LOG(WARNING) << m->PrettyMethod()
                   << " has an unexpected method index for its spot in the vtable for class"
                   << klass->PrettyClass();
    }
    ArraySlice<ArtMethod> virtuals = klass->GetVirtualMethodsSliceUnchecked(pointer_size);
    auto is_same_method = [m] (const ArtMethod& meth) {
      return &meth == m;
    };
    if (!((super_vtable_length > i && superclass->GetVTableEntry(i, pointer_size) == m) ||
          std::find_if(virtuals.begin(), virtuals.end(), is_same_method) != virtuals.end())) {
      LOG(WARNING) << m->PrettyMethod() << " does not seem to be owned by current class "
                   << klass->PrettyClass() << " or any of its superclasses!";
    }
  }
}

// Check to make sure the vtable does not have duplicates. Duplicates could cause problems when a
// method is overridden in a subclass.
template <PointerSize kPointerSize>
void CheckVTableHasNoDuplicates(Thread* self, Handle<mirror::Class> klass)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  StackHandleScope<1> hs(self);
  Handle<mirror::PointerArray> vtable(hs.NewHandle(klass->GetVTableDuringLinking()));
  int32_t num_entries = vtable->GetLength();

  // Observations:
  //   * The older implementation was O(n^2) and got too expensive for apps with larger classes.
  //   * Many classes do not override Object functions (e.g., equals/hashCode/toString). Thus,
  //     for many classes outside of libcore a cross-dexfile check has to be run anyways.
  //   * In the cross-dexfile case, with the O(n^2), in the best case O(n) cross checks would have
  //     to be done. It is thus OK in a single-pass algorithm to read all data, anyways.
  //   * The single-pass algorithm will trade memory for speed, but that is OK.

  CHECK_GT(num_entries, 0);

  auto log_fn = [&vtable, &klass](int32_t i, int32_t j) REQUIRES_SHARED(Locks::mutator_lock_) {
    ArtMethod* m1 = vtable->GetElementPtrSize<ArtMethod*, kPointerSize>(i);
    ArtMethod* m2 = vtable->GetElementPtrSize<ArtMethod*, kPointerSize>(j);
    LOG(WARNING) << "vtable entries " << i << " and " << j << " are identical for "
                 << klass->PrettyClass() << " in method " << m1->PrettyMethod()
                << " (0x" << std::hex << reinterpret_cast<uintptr_t>(m2) << ") and "
                << m2->PrettyMethod() << "  (0x" << std::hex
                << reinterpret_cast<uintptr_t>(m2) << ")";
  };
  struct BaseHashType {
    static size_t HashCombine(size_t seed, size_t val) {
      return seed ^ (val + 0x9e3779b9 + (seed << 6) + (seed >> 2));
    }
  };

  // Check assuming all entries come from the same dex file.
  {
    // Find the first interesting method and its dex file.
    int32_t start = 0;
    for (; start < num_entries; ++start) {
      ArtMethod* vtable_entry = vtable->GetElementPtrSize<ArtMethod*, kPointerSize>(start);
      // Don't bother if we cannot 'see' the vtable entry (i.e. it is a package-private member
      // maybe).
      if (!klass->CanAccessMember(vtable_entry->GetDeclaringClass(),
                                  vtable_entry->GetAccessFlags())) {
        continue;
      }
      break;
    }
    if (start == num_entries) {
      return;
    }
    const DexFile* dex_file =
        vtable->GetElementPtrSize<ArtMethod*, kPointerSize>(start)->
            GetInterfaceMethodIfProxy(kPointerSize)->GetDexFile();

    // Helper function to avoid logging if we have to run the cross-file checks.
    auto check_fn = [&](bool log_warn) REQUIRES_SHARED(Locks::mutator_lock_) {
      // Use a map to store seen entries, as the storage space is too large for a bitvector.
      using PairType = std::pair<uint32_t, uint16_t>;
      struct PairHash : BaseHashType {
        size_t operator()(const PairType& key) const {
          return BaseHashType::HashCombine(BaseHashType::HashCombine(0, key.first), key.second);
        }
      };
      std::unordered_map<PairType, int32_t, PairHash> seen;
      seen.reserve(2 * num_entries);
      bool need_slow_path = false;
      bool found_dup = false;
      for (int i = start; i < num_entries; ++i) {
        // Can use Unchecked here as the start loop already ensured that the arrays are correct
        // wrt/ kPointerSize.
        ArtMethod* vtable_entry = vtable->GetElementPtrSizeUnchecked<ArtMethod*, kPointerSize>(i);
        if (!klass->CanAccessMember(vtable_entry->GetDeclaringClass(),
                                    vtable_entry->GetAccessFlags())) {
          continue;
        }
        ArtMethod* m = vtable_entry->GetInterfaceMethodIfProxy(kPointerSize);
        if (dex_file != m->GetDexFile()) {
          need_slow_path = true;
          break;
        }
        const dex::MethodId* m_mid = &dex_file->GetMethodId(m->GetDexMethodIndex());
        PairType pair = std::make_pair(m_mid->name_idx_.index_, m_mid->proto_idx_.index_);
        auto it = seen.find(pair);
        if (it != seen.end()) {
          found_dup = true;
          if (log_warn) {
            log_fn(it->second, i);
          }
        } else {
          seen.emplace(pair, i);
        }
      }
      return std::make_pair(need_slow_path, found_dup);
    };
    std::pair<bool, bool> result = check_fn(/* log_warn= */ false);
    if (!result.first) {
      if (result.second) {
        check_fn(/* log_warn= */ true);
      }
      return;
    }
  }

  // Need to check across dex files.
  struct Entry {
    size_t cached_hash = 0;
    const char* name = nullptr;
    Signature signature = Signature::NoSignature();
    uint32_t name_len = 0;

    Entry(const DexFile* dex_file, const dex::MethodId& mid)
        : name(dex_file->StringDataAndUtf16LengthByIdx(mid.name_idx_, &name_len)),
          signature(dex_file->GetMethodSignature(mid)) {
    }

    bool operator==(const Entry& other) const {
      if (name_len != other.name_len || strcmp(name, other.name) != 0) {
        return false;
      }
      return signature == other.signature;
    }
  };
  struct EntryHash {
    size_t operator()(const Entry& key) const {
      return key.cached_hash;
    }
  };
  std::unordered_map<Entry, int32_t, EntryHash> map;
  for (int32_t i = 0; i < num_entries; ++i) {
    // Can use Unchecked here as the first loop already ensured that the arrays are correct
    // wrt/ kPointerSize.
    ArtMethod* vtable_entry = vtable->GetElementPtrSizeUnchecked<ArtMethod*, kPointerSize>(i);
    // Don't bother if we cannot 'see' the vtable entry (i.e. it is a package-private member
    // maybe).
    if (!klass->CanAccessMember(vtable_entry->GetDeclaringClass(),
                                vtable_entry->GetAccessFlags())) {
      continue;
    }
    ArtMethod* m = vtable_entry->GetInterfaceMethodIfProxy(kPointerSize);
    const DexFile* dex_file = m->GetDexFile();
    const dex::MethodId& mid = dex_file->GetMethodId(m->GetDexMethodIndex());

    Entry e(dex_file, mid);

    size_t string_hash = std::hash<std::string_view>()(std::string_view(e.name, e.name_len));
    size_t sig_hash = std::hash<std::string>()(e.signature.ToString());
    e.cached_hash = BaseHashType::HashCombine(BaseHashType::HashCombine(0u, string_hash),
                                              sig_hash);

    auto it = map.find(e);
    if (it != map.end()) {
      log_fn(it->second, i);
    } else {
      map.emplace(e, i);
    }
  }
}

void CheckVTableHasNoDuplicates(Thread* self,
                                Handle<mirror::Class> klass,
                                PointerSize pointer_size)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  switch (pointer_size) {
    case PointerSize::k64:
      CheckVTableHasNoDuplicates<PointerSize::k64>(self, klass);
      break;
    case PointerSize::k32:
      CheckVTableHasNoDuplicates<PointerSize::k32>(self, klass);
      break;
  }
}

static void SanityCheckVTable(Thread* self, Handle<mirror::Class> klass, PointerSize pointer_size)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  CheckClassOwnsVTableEntries(self, klass, pointer_size);
  CheckVTableHasNoDuplicates(self, klass, pointer_size);
}

}  // namespace

void ClassLinker::FillImtFromSuperClass(Handle<mirror::Class> klass,
                                        ArtMethod* unimplemented_method,
                                        ArtMethod* imt_conflict_method,
                                        bool* new_conflict,
                                        ArtMethod** imt) {
  DCHECK(klass->HasSuperClass());
  ObjPtr<mirror::Class> super_class = klass->GetSuperClass();
  if (super_class->ShouldHaveImt()) {
    ImTable* super_imt = super_class->GetImt(image_pointer_size_);
    for (size_t i = 0; i < ImTable::kSize; ++i) {
      imt[i] = super_imt->Get(i, image_pointer_size_);
    }
  } else {
    // No imt in the super class, need to reconstruct from the iftable.
    ObjPtr<mirror::IfTable> if_table = super_class->GetIfTable();
    if (if_table->Count() != 0) {
      // Ignore copied methods since we will handle these in LinkInterfaceMethods.
      FillIMTFromIfTable(if_table,
                         unimplemented_method,
                         imt_conflict_method,
                         klass.Get(),
                         /*create_conflict_tables=*/false,
                         /*ignore_copied_methods=*/true,
                         /*out*/new_conflict,
                         /*out*/imt);
    }
  }
}

class ClassLinker::LinkInterfaceMethodsHelper {
 public:
  LinkInterfaceMethodsHelper(ClassLinker* class_linker,
                             Handle<mirror::Class> klass,
                             Thread* self,
                             Runtime* runtime)
      : class_linker_(class_linker),
        klass_(klass),
        method_alignment_(ArtMethod::Alignment(class_linker->GetImagePointerSize())),
        method_size_(ArtMethod::Size(class_linker->GetImagePointerSize())),
        self_(self),
        stack_(runtime->GetLinearAlloc()->GetArenaPool()),
        allocator_(&stack_),
        default_conflict_methods_(allocator_.Adapter()),
        overriding_default_conflict_methods_(allocator_.Adapter()),
        miranda_methods_(allocator_.Adapter()),
        default_methods_(allocator_.Adapter()),
        overriding_default_methods_(allocator_.Adapter()),
        move_table_(allocator_.Adapter()) {
  }

  ArtMethod* FindMethod(ArtMethod* interface_method,
                        MethodNameAndSignatureComparator& interface_name_comparator,
                        ArtMethod* vtable_impl)
      REQUIRES_SHARED(Locks::mutator_lock_);

  ArtMethod* GetOrCreateMirandaMethod(ArtMethod* interface_method,
                                      MethodNameAndSignatureComparator& interface_name_comparator)
      REQUIRES_SHARED(Locks::mutator_lock_);

  bool HasNewVirtuals() const {
    return !(miranda_methods_.empty() &&
             default_methods_.empty() &&
             overriding_default_methods_.empty() &&
             overriding_default_conflict_methods_.empty() &&
             default_conflict_methods_.empty());
  }

  void ReallocMethods() REQUIRES_SHARED(Locks::mutator_lock_);

  ObjPtr<mirror::PointerArray> UpdateVtable(
      const std::unordered_map<size_t, ClassLinker::MethodTranslation>& default_translations,
      ObjPtr<mirror::PointerArray> old_vtable) REQUIRES_SHARED(Locks::mutator_lock_);

  void UpdateIfTable(Handle<mirror::IfTable> iftable) REQUIRES_SHARED(Locks::mutator_lock_);

  void UpdateIMT(ArtMethod** out_imt);

  void CheckNoStaleMethodsInDexCache() REQUIRES_SHARED(Locks::mutator_lock_) {
    if (kIsDebugBuild) {
      PointerSize pointer_size = class_linker_->GetImagePointerSize();
      // Check that there are no stale methods are in the dex cache array.
      auto* resolved_methods = klass_->GetDexCache()->GetResolvedMethods();
      for (size_t i = 0, count = klass_->GetDexCache()->NumResolvedMethods(); i < count; ++i) {
        auto pair = mirror::DexCache::GetNativePairPtrSize(resolved_methods, i, pointer_size);
        ArtMethod* m = pair.object;
        CHECK(move_table_.find(m) == move_table_.end() ||
              // The original versions of copied methods will still be present so allow those too.
              // Note that if the first check passes this might fail to GetDeclaringClass().
              std::find_if(m->GetDeclaringClass()->GetMethods(pointer_size).begin(),
                           m->GetDeclaringClass()->GetMethods(pointer_size).end(),
                           [m] (ArtMethod& meth) {
                             return &meth == m;
                           }) != m->GetDeclaringClass()->GetMethods(pointer_size).end())
            << "Obsolete method " << m->PrettyMethod() << " is in dex cache!";
      }
    }
  }

  void ClobberOldMethods(LengthPrefixedArray<ArtMethod>* old_methods,
                         LengthPrefixedArray<ArtMethod>* methods) {
    if (kIsDebugBuild) {
      CHECK(methods != nullptr);
      // Put some random garbage in old methods to help find stale pointers.
      if (methods != old_methods && old_methods != nullptr) {
        // Need to make sure the GC is not running since it could be scanning the methods we are
        // about to overwrite.
        ScopedThreadStateChange tsc(self_, kSuspended);
        gc::ScopedGCCriticalSection gcs(self_,
                                        gc::kGcCauseClassLinker,
                                        gc::kCollectorTypeClassLinker);
        const size_t old_size = LengthPrefixedArray<ArtMethod>::ComputeSize(old_methods->size(),
                                                                            method_size_,
                                                                            method_alignment_);
        memset(old_methods, 0xFEu, old_size);
      }
    }
  }

 private:
  size_t NumberOfNewVirtuals() const {
    return miranda_methods_.size() +
           default_methods_.size() +
           overriding_default_conflict_methods_.size() +
           overriding_default_methods_.size() +
           default_conflict_methods_.size();
  }

  bool FillTables() REQUIRES_SHARED(Locks::mutator_lock_) {
    return !klass_->IsInterface();
  }

  void LogNewVirtuals() const REQUIRES_SHARED(Locks::mutator_lock_) {
    DCHECK(!klass_->IsInterface() || (default_methods_.empty() && miranda_methods_.empty()))
        << "Interfaces should only have default-conflict methods appended to them.";
    VLOG(class_linker) << mirror::Class::PrettyClass(klass_.Get()) << ": miranda_methods="
                       << miranda_methods_.size()
                       << " default_methods=" << default_methods_.size()
                       << " overriding_default_methods=" << overriding_default_methods_.size()
                       << " default_conflict_methods=" << default_conflict_methods_.size()
                       << " overriding_default_conflict_methods="
                       << overriding_default_conflict_methods_.size();
  }

  ClassLinker* class_linker_;
  Handle<mirror::Class> klass_;
  size_t method_alignment_;
  size_t method_size_;
  Thread* const self_;

  // These are allocated on the heap to begin, we then transfer to linear alloc when we re-create
  // the virtual methods array.
  // Need to use low 4GB arenas for compiler or else the pointers wont fit in 32 bit method array
  // during cross compilation.
  // Use the linear alloc pool since this one is in the low 4gb for the compiler.
  ArenaStack stack_;
  ScopedArenaAllocator allocator_;

  ScopedArenaVector<ArtMethod*> default_conflict_methods_;
  ScopedArenaVector<ArtMethod*> overriding_default_conflict_methods_;
  ScopedArenaVector<ArtMethod*> miranda_methods_;
  ScopedArenaVector<ArtMethod*> default_methods_;
  ScopedArenaVector<ArtMethod*> overriding_default_methods_;

  ScopedArenaUnorderedMap<ArtMethod*, ArtMethod*> move_table_;
};

ArtMethod* ClassLinker::LinkInterfaceMethodsHelper::FindMethod(
    ArtMethod* interface_method,
    MethodNameAndSignatureComparator& interface_name_comparator,
    ArtMethod* vtable_impl) {
  ArtMethod* current_method = nullptr;
  switch (class_linker_->FindDefaultMethodImplementation(self_,
                                                         interface_method,
                                                         klass_,
                                                         /*out*/&current_method)) {
    case DefaultMethodSearchResult::kDefaultConflict: {
      // Default method conflict.
      DCHECK(current_method == nullptr);
      ArtMethod* default_conflict_method = nullptr;
      if (vtable_impl != nullptr && vtable_impl->IsDefaultConflicting()) {
        // We can reuse the method from the superclass, don't bother adding it to virtuals.
        default_conflict_method = vtable_impl;
      } else {
        // See if we already have a conflict method for this method.
        ArtMethod* preexisting_conflict = FindSameNameAndSignature(
            interface_name_comparator,
            default_conflict_methods_,
            overriding_default_conflict_methods_);
        if (LIKELY(preexisting_conflict != nullptr)) {
          // We already have another conflict we can reuse.
          default_conflict_method = preexisting_conflict;
        } else {
          // Note that we do this even if we are an interface since we need to create this and
          // cannot reuse another classes.
          // Create a new conflict method for this to use.
          default_conflict_method = reinterpret_cast<ArtMethod*>(allocator_.Alloc(method_size_));
          new(default_conflict_method) ArtMethod(interface_method,
                                                 class_linker_->GetImagePointerSize());
          if (vtable_impl == nullptr) {
            // Save the conflict method. We need to add it to the vtable.
            default_conflict_methods_.push_back(default_conflict_method);
          } else {
            // Save the conflict method but it is already in the vtable.
            overriding_default_conflict_methods_.push_back(default_conflict_method);
          }
        }
      }
      current_method = default_conflict_method;
      break;
    }  // case kDefaultConflict
    case DefaultMethodSearchResult::kDefaultFound: {
      DCHECK(current_method != nullptr);
      // Found a default method.
      if (vtable_impl != nullptr &&
          current_method->GetDeclaringClass() == vtable_impl->GetDeclaringClass()) {
        // We found a default method but it was the same one we already have from our
        // superclass. Don't bother adding it to our vtable again.
        current_method = vtable_impl;
      } else if (LIKELY(FillTables())) {
        // Interfaces don't need to copy default methods since they don't have vtables.
        // Only record this default method if it is new to save space.
        // TODO It might be worthwhile to copy default methods on interfaces anyway since it
        //      would make lookup for interface super much faster. (We would only need to scan
        //      the iftable to find if there is a NSME or AME.)
        ArtMethod* old = FindSameNameAndSignature(interface_name_comparator,
                                                  default_methods_,
                                                  overriding_default_methods_);
        if (old == nullptr) {
          // We found a default method implementation and there were no conflicts.
          if (vtable_impl == nullptr) {
            // Save the default method. We need to add it to the vtable.
            default_methods_.push_back(current_method);
          } else {
            // Save the default method but it is already in the vtable.
            overriding_default_methods_.push_back(current_method);
          }
        } else {
          CHECK(old == current_method) << "Multiple default implementations selected!";
        }
      }
      break;
    }  // case kDefaultFound
    case DefaultMethodSearchResult::kAbstractFound: {
      DCHECK(current_method == nullptr);
      // Abstract method masks all defaults.
      if (vtable_impl != nullptr &&
          vtable_impl->IsAbstract() &&
          !vtable_impl->IsDefaultConflicting()) {
        // We need to make this an abstract method but the version in the vtable already is so
        // don't do anything.
        current_method = vtable_impl;
      }
      break;
    }  // case kAbstractFound
  }
  return current_method;
}

ArtMethod* ClassLinker::LinkInterfaceMethodsHelper::GetOrCreateMirandaMethod(
    ArtMethod* interface_method,
    MethodNameAndSignatureComparator& interface_name_comparator) {
  // Find out if there is already a miranda method we can use.
  ArtMethod* miranda_method = FindSameNameAndSignature(interface_name_comparator,
                                                       miranda_methods_);
  if (miranda_method == nullptr) {
    DCHECK(interface_method->IsAbstract()) << interface_method->PrettyMethod();
    miranda_method = reinterpret_cast<ArtMethod*>(allocator_.Alloc(method_size_));
    CHECK(miranda_method != nullptr);
    // Point the interface table at a phantom slot.
    new(miranda_method) ArtMethod(interface_method, class_linker_->GetImagePointerSize());
    miranda_methods_.push_back(miranda_method);
  }
  return miranda_method;
}

void ClassLinker::LinkInterfaceMethodsHelper::ReallocMethods() {
  LogNewVirtuals();

  const size_t old_method_count = klass_->NumMethods();
  const size_t new_method_count = old_method_count + NumberOfNewVirtuals();
  DCHECK_NE(old_method_count, new_method_count);

  // Attempt to realloc to save RAM if possible.
  LengthPrefixedArray<ArtMethod>* old_methods = klass_->GetMethodsPtr();
  // The Realloced virtual methods aren't visible from the class roots, so there is no issue
  // where GCs could attempt to mark stale pointers due to memcpy. And since we overwrite the
  // realloced memory with out->CopyFrom, we are guaranteed to have objects in the to space since
  // CopyFrom has internal read barriers.
  //
  // TODO We should maybe move some of this into mirror::Class or at least into another method.
  const size_t old_size = LengthPrefixedArray<ArtMethod>::ComputeSize(old_method_count,
                                                                      method_size_,
                                                                      method_alignment_);
  const size_t new_size = LengthPrefixedArray<ArtMethod>::ComputeSize(new_method_count,
                                                                      method_size_,
                                                                      method_alignment_);
  const size_t old_methods_ptr_size = (old_methods != nullptr) ? old_size : 0;
  auto* methods = reinterpret_cast<LengthPrefixedArray<ArtMethod>*>(
      class_linker_->GetAllocatorForClassLoader(klass_->GetClassLoader())->Realloc(
          self_, old_methods, old_methods_ptr_size, new_size));
  CHECK(methods != nullptr);  // Native allocation failure aborts.

  PointerSize pointer_size = class_linker_->GetImagePointerSize();
  if (methods != old_methods) {
    // Maps from heap allocated miranda method to linear alloc miranda method.
    StrideIterator<ArtMethod> out = methods->begin(method_size_, method_alignment_);
    // Copy over the old methods.
    for (auto& m : klass_->GetMethods(pointer_size)) {
      move_table_.emplace(&m, &*out);
      // The CopyFrom is only necessary to not miss read barriers since Realloc won't do read
      // barriers when it copies.
      out->CopyFrom(&m, pointer_size);
      ++out;
    }
  }
  StrideIterator<ArtMethod> out(methods->begin(method_size_, method_alignment_) + old_method_count);
  // Copy over miranda methods before copying vtable since CopyOf may cause thread suspension and
  // we want the roots of the miranda methods to get visited.
  for (size_t i = 0; i < miranda_methods_.size(); ++i) {
    ArtMethod* mir_method = miranda_methods_[i];
    ArtMethod& new_method = *out;
    new_method.CopyFrom(mir_method, pointer_size);
    new_method.SetAccessFlags(new_method.GetAccessFlags() | kAccMiranda | kAccCopied);
    DCHECK_NE(new_method.GetAccessFlags() & kAccAbstract, 0u)
        << "Miranda method should be abstract!";
    move_table_.emplace(mir_method, &new_method);
    // Update the entry in the method array, as the array will be used for future lookups,
    // where thread suspension is allowed.
    // As such, the array should not contain locally allocated ArtMethod, otherwise the GC
    // would not see them.
    miranda_methods_[i] = &new_method;
    ++out;
  }
  // We need to copy the default methods into our own method table since the runtime requires that
  // every method on a class's vtable be in that respective class's virtual method table.
  // NOTE This means that two classes might have the same implementation of a method from the same
  // interface but will have different ArtMethod*s for them. This also means we cannot compare a
  // default method found on a class with one found on the declaring interface directly and must
  // look at the declaring class to determine if they are the same.
  for (ScopedArenaVector<ArtMethod*>* methods_vec : {&default_methods_,
                                                     &overriding_default_methods_}) {
    for (size_t i = 0; i < methods_vec->size(); ++i) {
      ArtMethod* def_method = (*methods_vec)[i];
      ArtMethod& new_method = *out;
      new_method.CopyFrom(def_method, pointer_size);
      // Clear the kAccSkipAccessChecks flag if it is present. Since this class hasn't been
      // verified yet it shouldn't have methods that are skipping access checks.
      // TODO This is rather arbitrary. We should maybe support classes where only some of its
      // methods are skip_access_checks.
      DCHECK_EQ(new_method.GetAccessFlags() & kAccNative, 0u);
      constexpr uint32_t kSetFlags = kAccDefault | kAccCopied;
      constexpr uint32_t kMaskFlags = ~kAccSkipAccessChecks;
      new_method.SetAccessFlags((new_method.GetAccessFlags() | kSetFlags) & kMaskFlags);
      move_table_.emplace(def_method, &new_method);
      // Update the entry in the method array, as the array will be used for future lookups,
      // where thread suspension is allowed.
      // As such, the array should not contain locally allocated ArtMethod, otherwise the GC
      // would not see them.
      (*methods_vec)[i] = &new_method;
      ++out;
    }
  }
  for (ScopedArenaVector<ArtMethod*>* methods_vec : {&default_conflict_methods_,
                                                     &overriding_default_conflict_methods_}) {
    for (size_t i = 0; i < methods_vec->size(); ++i) {
      ArtMethod* conf_method = (*methods_vec)[i];
      ArtMethod& new_method = *out;
      new_method.CopyFrom(conf_method, pointer_size);
      // This is a type of default method (there are default method impls, just a conflict) so
      // mark this as a default, non-abstract method, since thats what it is. Also clear the
      // kAccSkipAccessChecks bit since this class hasn't been verified yet it shouldn't have
      // methods that are skipping access checks.
      // Also clear potential kAccSingleImplementation to avoid CHA trying to inline
      // the default method.
      DCHECK_EQ(new_method.GetAccessFlags() & kAccNative, 0u);
      constexpr uint32_t kSetFlags = kAccDefault | kAccDefaultConflict | kAccCopied;
      constexpr uint32_t kMaskFlags =
          ~(kAccAbstract | kAccSkipAccessChecks | kAccSingleImplementation);
      new_method.SetAccessFlags((new_method.GetAccessFlags() | kSetFlags) & kMaskFlags);
      DCHECK(new_method.IsDefaultConflicting());
      // The actual method might or might not be marked abstract since we just copied it from a
      // (possibly default) interface method. We need to set it entry point to be the bridge so
      // that the compiler will not invoke the implementation of whatever method we copied from.
      EnsureThrowsInvocationError(class_linker_, &new_method);
      move_table_.emplace(conf_method, &new_method);
      // Update the entry in the method array, as the array will be used for future lookups,
      // where thread suspension is allowed.
      // As such, the array should not contain locally allocated ArtMethod, otherwise the GC
      // would not see them.
      (*methods_vec)[i] = &new_method;
      ++out;
    }
  }
  methods->SetSize(new_method_count);
  class_linker_->UpdateClassMethods(klass_.Get(), methods);
}

ObjPtr<mirror::PointerArray> ClassLinker::LinkInterfaceMethodsHelper::UpdateVtable(
    const std::unordered_map<size_t, ClassLinker::MethodTranslation>& default_translations,
    ObjPtr<mirror::PointerArray> old_vtable) {
  // Update the vtable to the new method structures. We can skip this for interfaces since they
  // do not have vtables.
  const size_t old_vtable_count = old_vtable->GetLength();
  const size_t new_vtable_count = old_vtable_count +
                                  miranda_methods_.size() +
                                  default_methods_.size() +
                                  default_conflict_methods_.size();

  ObjPtr<mirror::PointerArray> vtable =
      ObjPtr<mirror::PointerArray>::DownCast(old_vtable->CopyOf(self_, new_vtable_count));
  if (UNLIKELY(vtable == nullptr)) {
    self_->AssertPendingOOMException();
    return nullptr;
  }

  size_t vtable_pos = old_vtable_count;
  PointerSize pointer_size = class_linker_->GetImagePointerSize();
  // Update all the newly copied method's indexes so they denote their placement in the vtable.
  for (const ScopedArenaVector<ArtMethod*>& methods_vec : {default_methods_,
                                                           default_conflict_methods_,
                                                           miranda_methods_}) {
    // These are the functions that are not already in the vtable!
    for (ArtMethod* new_vtable_method : methods_vec) {
      // Leave the declaring class alone the method's dex_code_item_offset_ and dex_method_index_
      // fields are references into the dex file the method was defined in. Since the ArtMethod
      // does not store that information it uses declaring_class_->dex_cache_.
      new_vtable_method->SetMethodIndex(0xFFFF & vtable_pos);
      vtable->SetElementPtrSize(vtable_pos, new_vtable_method, pointer_size);
      ++vtable_pos;
    }
  }
  DCHECK_EQ(vtable_pos, new_vtable_count);

  // Update old vtable methods. We use the default_translations map to figure out what each
  // vtable entry should be updated to, if they need to be at all.
  for (size_t i = 0; i < old_vtable_count; ++i) {
    ArtMethod* translated_method = vtable->GetElementPtrSize<ArtMethod*>(i, pointer_size);
    // Try and find what we need to change this method to.
    auto translation_it = default_translations.find(i);
    if (translation_it != default_translations.end()) {
      if (translation_it->second.IsInConflict()) {
        // Find which conflict method we are to use for this method.
        MethodNameAndSignatureComparator old_method_comparator(
            translated_method->GetInterfaceMethodIfProxy(pointer_size));
        // We only need to look through overriding_default_conflict_methods since this is an
        // overridden method we are fixing up here.
        ArtMethod* new_conflict_method = FindSameNameAndSignature(
            old_method_comparator, overriding_default_conflict_methods_);
        CHECK(new_conflict_method != nullptr) << "Expected a conflict method!";
        translated_method = new_conflict_method;
      } else if (translation_it->second.IsAbstract()) {
        // Find which miranda method we are to use for this method.
        MethodNameAndSignatureComparator old_method_comparator(
            translated_method->GetInterfaceMethodIfProxy(pointer_size));
        ArtMethod* miranda_method = FindSameNameAndSignature(old_method_comparator,
                                                             miranda_methods_);
        DCHECK(miranda_method != nullptr);
        translated_method = miranda_method;
      } else {
        // Normal default method (changed from an older default or abstract interface method).
        DCHECK(translation_it->second.IsTranslation());
        translated_method = translation_it->second.GetTranslation();
        auto it = move_table_.find(translated_method);
        DCHECK(it != move_table_.end());
        translated_method = it->second;
      }
    } else {
      auto it = move_table_.find(translated_method);
      translated_method = (it != move_table_.end()) ? it->second : nullptr;
    }

    if (translated_method != nullptr) {
      // Make sure the new_methods index is set.
      if (translated_method->GetMethodIndexDuringLinking() != i) {
        if (kIsDebugBuild) {
          auto* methods = klass_->GetMethodsPtr();
          CHECK_LE(reinterpret_cast<uintptr_t>(&*methods->begin(method_size_, method_alignment_)),
                   reinterpret_cast<uintptr_t>(translated_method));
          CHECK_LT(reinterpret_cast<uintptr_t>(translated_method),
                   reinterpret_cast<uintptr_t>(&*methods->end(method_size_, method_alignment_)));
        }
        translated_method->SetMethodIndex(0xFFFF & i);
      }
      vtable->SetElementPtrSize(i, translated_method, pointer_size);
    }
  }
  klass_->SetVTable(vtable);
  return vtable;
}

void ClassLinker::LinkInterfaceMethodsHelper::UpdateIfTable(Handle<mirror::IfTable> iftable) {
  PointerSize pointer_size = class_linker_->GetImagePointerSize();
  const size_t ifcount = klass_->GetIfTableCount();
  // Go fix up all the stale iftable pointers.
  for (size_t i = 0; i < ifcount; ++i) {
    for (size_t j = 0, count = iftable->GetMethodArrayCount(i); j < count; ++j) {
      ObjPtr<mirror::PointerArray> method_array = iftable->GetMethodArray(i);
      ArtMethod* m = method_array->GetElementPtrSize<ArtMethod*>(j, pointer_size);
      DCHECK(m != nullptr) << klass_->PrettyClass();
      auto it = move_table_.find(m);
      if (it != move_table_.end()) {
        auto* new_m = it->second;
        DCHECK(new_m != nullptr) << klass_->PrettyClass();
        method_array->SetElementPtrSize(j, new_m, pointer_size);
      }
    }
  }
}

void ClassLinker::LinkInterfaceMethodsHelper::UpdateIMT(ArtMethod** out_imt) {
  // Fix up IMT next.
  for (size_t i = 0; i < ImTable::kSize; ++i) {
    auto it = move_table_.find(out_imt[i]);
    if (it != move_table_.end()) {
      out_imt[i] = it->second;
    }
  }
}

// TODO This method needs to be split up into several smaller methods.
bool ClassLinker::LinkInterfaceMethods(
    Thread* self,
    Handle<mirror::Class> klass,
    const std::unordered_map<size_t, ClassLinker::MethodTranslation>& default_translations,
    bool* out_new_conflict,
    ArtMethod** out_imt) {
  StackHandleScope<3> hs(self);
  Runtime* const runtime = Runtime::Current();

  const bool is_interface = klass->IsInterface();
  const bool has_superclass = klass->HasSuperClass();
  const bool fill_tables = !is_interface;
  const size_t super_ifcount = has_superclass ? klass->GetSuperClass()->GetIfTableCount() : 0U;
  const size_t ifcount = klass->GetIfTableCount();

  Handle<mirror::IfTable> iftable(hs.NewHandle(klass->GetIfTable()));

  MutableHandle<mirror::PointerArray> vtable(hs.NewHandle(klass->GetVTableDuringLinking()));
  ArtMethod* const unimplemented_method = runtime->GetImtUnimplementedMethod();
  ArtMethod* const imt_conflict_method = runtime->GetImtConflictMethod();
  // Copy the IMT from the super class if possible.
  const bool extend_super_iftable = has_superclass;
  if (has_superclass && fill_tables) {
    FillImtFromSuperClass(klass,
                          unimplemented_method,
                          imt_conflict_method,
                          out_new_conflict,
                          out_imt);
  }
  // Allocate method arrays before since we don't want miss visiting miranda method roots due to
  // thread suspension.
  if (fill_tables) {
    if (!AllocateIfTableMethodArrays(self, klass, iftable)) {
      return false;
    }
  }

  LinkInterfaceMethodsHelper helper(this, klass, self, runtime);

  auto* old_cause = self->StartAssertNoThreadSuspension(
      "Copying ArtMethods for LinkInterfaceMethods");
  // Going in reverse to ensure that we will hit abstract methods that override defaults before the
  // defaults. This means we don't need to do any trickery when creating the Miranda methods, since
  // they will already be null. This has the additional benefit that the declarer of a miranda
  // method will actually declare an abstract method.
  for (size_t i = ifcount; i != 0u; ) {
    --i;
    DCHECK_LT(i, ifcount);

    size_t num_methods = iftable->GetInterface(i)->NumDeclaredVirtualMethods();
    if (num_methods > 0) {
      StackHandleScope<2> hs2(self);
      const bool is_super = i < super_ifcount;
      const bool super_interface = is_super && extend_super_iftable;
      // We don't actually create or fill these tables for interfaces, we just copy some methods for
      // conflict methods. Just set this as nullptr in those cases.
      Handle<mirror::PointerArray> method_array(fill_tables
                                                ? hs2.NewHandle(iftable->GetMethodArray(i))
                                                : hs2.NewHandle<mirror::PointerArray>(nullptr));

      ArraySlice<ArtMethod> input_virtual_methods;
      ScopedNullHandle<mirror::PointerArray> null_handle;
      Handle<mirror::PointerArray> input_vtable_array(null_handle);
      int32_t input_array_length = 0;

      // TODO Cleanup Needed: In the presence of default methods this optimization is rather dirty
      //      and confusing. Default methods should always look through all the superclasses
      //      because they are the last choice of an implementation. We get around this by looking
      //      at the super-classes iftable methods (copied into method_array previously) when we are
      //      looking for the implementation of a super-interface method but that is rather dirty.
      bool using_virtuals;
      if (super_interface || is_interface) {
        // If we are overwriting a super class interface, try to only virtual methods instead of the
        // whole vtable.
        using_virtuals = true;
        input_virtual_methods = klass->GetDeclaredMethodsSlice(image_pointer_size_);
        input_array_length = input_virtual_methods.size();
      } else {
        // For a new interface, however, we need the whole vtable in case a new
        // interface method is implemented in the whole superclass.
        using_virtuals = false;
        DCHECK(vtable != nullptr);
        input_vtable_array = vtable;
        input_array_length = input_vtable_array->GetLength();
      }

      // For each method in interface
      for (size_t j = 0; j < num_methods; ++j) {
        auto* interface_method = iftable->GetInterface(i)->GetVirtualMethod(j, image_pointer_size_);
        MethodNameAndSignatureComparator interface_name_comparator(
            interface_method->GetInterfaceMethodIfProxy(image_pointer_size_));
        uint32_t imt_index = interface_method->GetImtIndex();
        ArtMethod** imt_ptr = &out_imt[imt_index];
        // For each method listed in the interface's method list, find the
        // matching method in our class's method list.  We want to favor the
        // subclass over the superclass, which just requires walking
        // back from the end of the vtable.  (This only matters if the
        // superclass defines a private method and this class redefines
        // it -- otherwise it would use the same vtable slot.  In .dex files
        // those don't end up in the virtual method table, so it shouldn't
        // matter which direction we go.  We walk it backward anyway.)
        //
        // To find defaults we need to do the same but also go over interfaces.
        bool found_impl = false;
        ArtMethod* vtable_impl = nullptr;
        for (int32_t k = input_array_length - 1; k >= 0; --k) {
          ArtMethod* vtable_method = using_virtuals ?
              &input_virtual_methods[k] :
              input_vtable_array->GetElementPtrSize<ArtMethod*>(k, image_pointer_size_);
          ArtMethod* vtable_method_for_name_comparison =
              vtable_method->GetInterfaceMethodIfProxy(image_pointer_size_);
          if (interface_name_comparator.HasSameNameAndSignature(
              vtable_method_for_name_comparison)) {
            if (!vtable_method->IsAbstract() && !vtable_method->IsPublic()) {
              // Must do EndAssertNoThreadSuspension before throw since the throw can cause
              // allocations.
              self->EndAssertNoThreadSuspension(old_cause);
              ThrowIllegalAccessError(klass.Get(),
                  "Method '%s' implementing interface method '%s' is not public",
                  vtable_method->PrettyMethod().c_str(),
                  interface_method->PrettyMethod().c_str());
              return false;
            } else if (UNLIKELY(vtable_method->IsOverridableByDefaultMethod())) {
              // We might have a newer, better, default method for this, so we just skip it. If we
              // are still using this we will select it again when scanning for default methods. To
              // obviate the need to copy the method again we will make a note that we already found
              // a default here.
              // TODO This should be much cleaner.
              vtable_impl = vtable_method;
              break;
            } else {
              found_impl = true;
              if (LIKELY(fill_tables)) {
                method_array->SetElementPtrSize(j, vtable_method, image_pointer_size_);
                // Place method in imt if entry is empty, place conflict otherwise.
                SetIMTRef(unimplemented_method,
                          imt_conflict_method,
                          vtable_method,
                          /*out*/out_new_conflict,
                          /*out*/imt_ptr);
              }
              break;
            }
          }
        }
        // Continue on to the next method if we are done.
        if (LIKELY(found_impl)) {
          continue;
        } else if (LIKELY(super_interface)) {
          // Don't look for a default implementation when the super-method is implemented directly
          // by the class.
          //
          // See if we can use the superclasses method and skip searching everything else.
          // Note: !found_impl && super_interface
          CHECK(extend_super_iftable);
          // If this is a super_interface method it is possible we shouldn't override it because a
          // superclass could have implemented it directly.  We get the method the superclass used
          // to implement this to know if we can override it with a default method. Doing this is
          // safe since we know that the super_iftable is filled in so we can simply pull it from
          // there. We don't bother if this is not a super-classes interface since in that case we
          // have scanned the entire vtable anyway and would have found it.
          // TODO This is rather dirty but it is faster than searching through the entire vtable
          //      every time.
          ArtMethod* supers_method =
              method_array->GetElementPtrSize<ArtMethod*>(j, image_pointer_size_);
          DCHECK(supers_method != nullptr);
          DCHECK(interface_name_comparator.HasSameNameAndSignature(supers_method));
          if (LIKELY(!supers_method->IsOverridableByDefaultMethod())) {
            // The method is not overridable by a default method (i.e. it is directly implemented
            // in some class). Therefore move onto the next interface method.
            continue;
          } else {
            // If the super-classes method is override-able by a default method we need to keep
            // track of it since though it is override-able it is not guaranteed to be 'overridden'.
            // If it turns out not to be overridden and we did not keep track of it we might add it
            // to the vtable twice, causing corruption (vtable entries having inconsistent and
            // illegal states, incorrect vtable size, and incorrect or inconsistent iftable entries)
            // in this class and any subclasses.
            DCHECK(vtable_impl == nullptr || vtable_impl == supers_method)
                << "vtable_impl was " << ArtMethod::PrettyMethod(vtable_impl)
                << " and not 'nullptr' or "
                << supers_method->PrettyMethod()
                << " as expected. IFTable appears to be corrupt!";
            vtable_impl = supers_method;
          }
        }
        // If we haven't found it yet we should search through the interfaces for default methods.
        ArtMethod* current_method = helper.FindMethod(interface_method,
                                                      interface_name_comparator,
                                                      vtable_impl);
        if (LIKELY(fill_tables)) {
          if (current_method == nullptr && !super_interface) {
            // We could not find an implementation for this method and since it is a brand new
            // interface we searched the entire vtable (and all default methods) for an
            // implementation but couldn't find one. We therefore need to make a miranda method.
            current_method = helper.GetOrCreateMirandaMethod(interface_method,
                                                             interface_name_comparator);
          }

          if (current_method != nullptr) {
            // We found a default method implementation. Record it in the iftable and IMT.
            method_array->SetElementPtrSize(j, current_method, image_pointer_size_);
            SetIMTRef(unimplemented_method,
                      imt_conflict_method,
                      current_method,
                      /*out*/out_new_conflict,
                      /*out*/imt_ptr);
          }
        }
      }  // For each method in interface end.
    }  // if (num_methods > 0)
  }  // For each interface.
  // TODO don't extend virtuals of interface unless necessary (when is it?).
  if (helper.HasNewVirtuals()) {
    LengthPrefixedArray<ArtMethod>* old_methods = kIsDebugBuild ? klass->GetMethodsPtr() : nullptr;
    helper.ReallocMethods();  // No return value to check. Native allocation failure aborts.
    LengthPrefixedArray<ArtMethod>* methods = kIsDebugBuild ? klass->GetMethodsPtr() : nullptr;

    // Done copying methods, they are all roots in the class now, so we can end the no thread
    // suspension assert.
    self->EndAssertNoThreadSuspension(old_cause);

    if (fill_tables) {
      vtable.Assign(helper.UpdateVtable(default_translations, vtable.Get()));
      if (UNLIKELY(vtable == nullptr)) {
        // The helper has already called self->AssertPendingOOMException();
        return false;
      }
      helper.UpdateIfTable(iftable);
      helper.UpdateIMT(out_imt);
    }

    helper.CheckNoStaleMethodsInDexCache();
    helper.ClobberOldMethods(old_methods, methods);
  } else {
    self->EndAssertNoThreadSuspension(old_cause);
  }
  if (kIsDebugBuild && !is_interface) {
    SanityCheckVTable(self, klass, image_pointer_size_);
  }
  return true;
}

bool ClassLinker::LinkInstanceFields(Thread* self, Handle<mirror::Class> klass) {
  CHECK(klass != nullptr);
  return LinkFields(self, klass, false, nullptr);
}

bool ClassLinker::LinkStaticFields(Thread* self, Handle<mirror::Class> klass, size_t* class_size) {
  CHECK(klass != nullptr);
  return LinkFields(self, klass, true, class_size);
}

struct LinkFieldsComparator {
  LinkFieldsComparator() REQUIRES_SHARED(Locks::mutator_lock_) {
  }
  // No thread safety analysis as will be called from STL. Checked lock held in constructor.
  bool operator()(ArtField* field1, ArtField* field2)
      NO_THREAD_SAFETY_ANALYSIS {
    // First come reference fields, then 64-bit, then 32-bit, and then 16-bit, then finally 8-bit.
    Primitive::Type type1 = field1->GetTypeAsPrimitiveType();
    Primitive::Type type2 = field2->GetTypeAsPrimitiveType();
    if (type1 != type2) {
      if (type1 == Primitive::kPrimNot) {
        // Reference always goes first.
        return true;
      }
      if (type2 == Primitive::kPrimNot) {
        // Reference always goes first.
        return false;
      }
      size_t size1 = Primitive::ComponentSize(type1);
      size_t size2 = Primitive::ComponentSize(type2);
      if (size1 != size2) {
        // Larger primitive types go first.
        return size1 > size2;
      }
      // Primitive types differ but sizes match. Arbitrarily order by primitive type.
      return type1 < type2;
    }
    // Same basic group? Then sort by dex field index. This is guaranteed to be sorted
    // by name and for equal names by type id index.
    // NOTE: This works also for proxies. Their static fields are assigned appropriate indexes.
    return field1->GetDexFieldIndex() < field2->GetDexFieldIndex();
  }
};

bool ClassLinker::LinkFields(Thread* self,
                             Handle<mirror::Class> klass,
                             bool is_static,
                             size_t* class_size) {
  self->AllowThreadSuspension();
  const size_t num_fields = is_static ? klass->NumStaticFields() : klass->NumInstanceFields();
  LengthPrefixedArray<ArtField>* const fields = is_static ? klass->GetSFieldsPtr() :
      klass->GetIFieldsPtr();

  // Initialize field_offset
  MemberOffset field_offset(0);
  if (is_static) {
    field_offset = klass->GetFirstReferenceStaticFieldOffsetDuringLinking(image_pointer_size_);
  } else {
    ObjPtr<mirror::Class> super_class = klass->GetSuperClass();
    if (super_class != nullptr) {
      CHECK(super_class->IsResolved())
          << klass->PrettyClass() << " " << super_class->PrettyClass();
      field_offset = MemberOffset(super_class->GetObjectSize());
    }
  }

  CHECK_EQ(num_fields == 0, fields == nullptr) << klass->PrettyClass();

  // we want a relatively stable order so that adding new fields
  // minimizes disruption of C++ version such as Class and Method.
  //
  // The overall sort order order is:
  // 1) All object reference fields, sorted alphabetically.
  // 2) All java long (64-bit) integer fields, sorted alphabetically.
  // 3) All java double (64-bit) floating point fields, sorted alphabetically.
  // 4) All java int (32-bit) integer fields, sorted alphabetically.
  // 5) All java float (32-bit) floating point fields, sorted alphabetically.
  // 6) All java char (16-bit) integer fields, sorted alphabetically.
  // 7) All java short (16-bit) integer fields, sorted alphabetically.
  // 8) All java boolean (8-bit) integer fields, sorted alphabetically.
  // 9) All java byte (8-bit) integer fields, sorted alphabetically.
  //
  // Once the fields are sorted in this order we will attempt to fill any gaps that might be present
  // in the memory layout of the structure. See ShuffleForward for how this is done.
  std::deque<ArtField*> grouped_and_sorted_fields;
  const char* old_no_suspend_cause = self->StartAssertNoThreadSuspension(
      "Naked ArtField references in deque");
  for (size_t i = 0; i < num_fields; i++) {
    grouped_and_sorted_fields.push_back(&fields->At(i));
  }
  std::sort(grouped_and_sorted_fields.begin(), grouped_and_sorted_fields.end(),
            LinkFieldsComparator());

  // References should be at the front.
  size_t current_field = 0;
  size_t num_reference_fields = 0;
  FieldGaps gaps;

  for (; current_field < num_fields; current_field++) {
    ArtField* field = grouped_and_sorted_fields.front();
    Primitive::Type type = field->GetTypeAsPrimitiveType();
    bool isPrimitive = type != Primitive::kPrimNot;
    if (isPrimitive) {
      break;  // past last reference, move on to the next phase
    }
    if (UNLIKELY(!IsAligned<sizeof(mirror::HeapReference<mirror::Object>)>(
        field_offset.Uint32Value()))) {
      MemberOffset old_offset = field_offset;
      field_offset = MemberOffset(RoundUp(field_offset.Uint32Value(), 4));
      AddFieldGap(old_offset.Uint32Value(), field_offset.Uint32Value(), &gaps);
    }
    DCHECK_ALIGNED(field_offset.Uint32Value(), sizeof(mirror::HeapReference<mirror::Object>));
    grouped_and_sorted_fields.pop_front();
    num_reference_fields++;
    field->SetOffset(field_offset);
    field_offset = MemberOffset(field_offset.Uint32Value() +
                                sizeof(mirror::HeapReference<mirror::Object>));
  }
  // Gaps are stored as a max heap which means that we must shuffle from largest to smallest
  // otherwise we could end up with suboptimal gap fills.
  ShuffleForward<8>(&current_field, &field_offset, &grouped_and_sorted_fields, &gaps);
  ShuffleForward<4>(&current_field, &field_offset, &grouped_and_sorted_fields, &gaps);
  ShuffleForward<2>(&current_field, &field_offset, &grouped_and_sorted_fields, &gaps);
  ShuffleForward<1>(&current_field, &field_offset, &grouped_and_sorted_fields, &gaps);
  CHECK(grouped_and_sorted_fields.empty()) << "Missed " << grouped_and_sorted_fields.size() <<
      " fields.";
  self->EndAssertNoThreadSuspension(old_no_suspend_cause);

  // We lie to the GC about the java.lang.ref.Reference.referent field, so it doesn't scan it.
  if (!is_static && klass->DescriptorEquals("Ljava/lang/ref/Reference;")) {
    // We know there are no non-reference fields in the Reference classes, and we know
    // that 'referent' is alphabetically last, so this is easy...
    CHECK_EQ(num_reference_fields, num_fields) << klass->PrettyClass();
    CHECK_STREQ(fields->At(num_fields - 1).GetName(), "referent")
        << klass->PrettyClass();
    --num_reference_fields;
  }

  size_t size = field_offset.Uint32Value();
  // Update klass
  if (is_static) {
    klass->SetNumReferenceStaticFields(num_reference_fields);
    *class_size = size;
  } else {
    klass->SetNumReferenceInstanceFields(num_reference_fields);
    ObjPtr<mirror::Class> super_class = klass->GetSuperClass();
    if (num_reference_fields == 0 || super_class == nullptr) {
      // object has one reference field, klass, but we ignore it since we always visit the class.
      // super_class is null iff the class is java.lang.Object.
      if (super_class == nullptr ||
          (super_class->GetClassFlags() & mirror::kClassFlagNoReferenceFields) != 0) {
        klass->SetClassFlags(klass->GetClassFlags() | mirror::kClassFlagNoReferenceFields);
      }
    }
    if (kIsDebugBuild) {
      DCHECK_EQ(super_class == nullptr, klass->DescriptorEquals("Ljava/lang/Object;"));
      size_t total_reference_instance_fields = 0;
      ObjPtr<mirror::Class> cur_super = klass.Get();
      while (cur_super != nullptr) {
        total_reference_instance_fields += cur_super->NumReferenceInstanceFieldsDuringLinking();
        cur_super = cur_super->GetSuperClass();
      }
      if (super_class == nullptr) {
        CHECK_EQ(total_reference_instance_fields, 1u) << klass->PrettyDescriptor();
      } else {
        // Check that there is at least num_reference_fields other than Object.class.
        CHECK_GE(total_reference_instance_fields, 1u + num_reference_fields)
            << klass->PrettyClass();
      }
    }
    if (!klass->IsVariableSize()) {
      std::string temp;
      DCHECK_GE(size, sizeof(mirror::Object)) << klass->GetDescriptor(&temp);
      size_t previous_size = klass->GetObjectSize();
      if (previous_size != 0) {
        // Make sure that we didn't originally have an incorrect size.
        CHECK_EQ(previous_size, size) << klass->GetDescriptor(&temp);
      }
      klass->SetObjectSize(size);
    }
  }

  if (kIsDebugBuild) {
    // Make sure that the fields array is ordered by name but all reference
    // offsets are at the beginning as far as alignment allows.
    MemberOffset start_ref_offset = is_static
        ? klass->GetFirstReferenceStaticFieldOffsetDuringLinking(image_pointer_size_)
        : klass->GetFirstReferenceInstanceFieldOffset();
    MemberOffset end_ref_offset(start_ref_offset.Uint32Value() +
                                num_reference_fields *
                                    sizeof(mirror::HeapReference<mirror::Object>));
    MemberOffset current_ref_offset = start_ref_offset;
    for (size_t i = 0; i < num_fields; i++) {
      ArtField* field = &fields->At(i);
      VLOG(class_linker) << "LinkFields: " << (is_static ? "static" : "instance")
          << " class=" << klass->PrettyClass() << " field=" << field->PrettyField()
          << " offset=" << field->GetOffsetDuringLinking();
      if (i != 0) {
        ArtField* const prev_field = &fields->At(i - 1);
        // NOTE: The field names can be the same. This is not possible in the Java language
        // but it's valid Java/dex bytecode and for example proguard can generate such bytecode.
        DCHECK_LE(strcmp(prev_field->GetName(), field->GetName()), 0);
      }
      Primitive::Type type = field->GetTypeAsPrimitiveType();
      bool is_primitive = type != Primitive::kPrimNot;
      if (klass->DescriptorEquals("Ljava/lang/ref/Reference;") &&
          strcmp("referent", field->GetName()) == 0) {
        is_primitive = true;  // We lied above, so we have to expect a lie here.
      }
      MemberOffset offset = field->GetOffsetDuringLinking();
      if (is_primitive) {
        if (offset.Uint32Value() < end_ref_offset.Uint32Value()) {
          // Shuffled before references.
          size_t type_size = Primitive::ComponentSize(type);
          CHECK_LT(type_size, sizeof(mirror::HeapReference<mirror::Object>));
          CHECK_LT(offset.Uint32Value(), start_ref_offset.Uint32Value());
          CHECK_LE(offset.Uint32Value() + type_size, start_ref_offset.Uint32Value());
          CHECK(!IsAligned<sizeof(mirror::HeapReference<mirror::Object>)>(offset.Uint32Value()));
        }
      } else {
        CHECK_EQ(current_ref_offset.Uint32Value(), offset.Uint32Value());
        current_ref_offset = MemberOffset(current_ref_offset.Uint32Value() +
                                          sizeof(mirror::HeapReference<mirror::Object>));
      }
    }
    CHECK_EQ(current_ref_offset.Uint32Value(), end_ref_offset.Uint32Value());
  }
  return true;
}

//  Set the bitmap of reference instance field offsets.
void ClassLinker::CreateReferenceInstanceOffsets(Handle<mirror::Class> klass) {
  uint32_t reference_offsets = 0;
  ObjPtr<mirror::Class> super_class = klass->GetSuperClass();
  // Leave the reference offsets as 0 for mirror::Object (the class field is handled specially).
  if (super_class != nullptr) {
    reference_offsets = super_class->GetReferenceInstanceOffsets();
    // Compute reference offsets unless our superclass overflowed.
    if (reference_offsets != mirror::Class::kClassWalkSuper) {
      size_t num_reference_fields = klass->NumReferenceInstanceFieldsDuringLinking();
      if (num_reference_fields != 0u) {
        // All of the fields that contain object references are guaranteed be grouped in memory
        // starting at an appropriately aligned address after super class object data.
        uint32_t start_offset = RoundUp(super_class->GetObjectSize(),
                                        sizeof(mirror::HeapReference<mirror::Object>));
        uint32_t start_bit = (start_offset - mirror::kObjectHeaderSize) /
            sizeof(mirror::HeapReference<mirror::Object>);
        if (start_bit + num_reference_fields > 32) {
          reference_offsets = mirror::Class::kClassWalkSuper;
        } else {
          reference_offsets |= (0xffffffffu << start_bit) &
                               (0xffffffffu >> (32 - (start_bit + num_reference_fields)));
        }
      }
    }
  }
  klass->SetReferenceInstanceOffsets(reference_offsets);
}

ObjPtr<mirror::String> ClassLinker::DoResolveString(dex::StringIndex string_idx,
                                                    ObjPtr<mirror::DexCache> dex_cache) {
  StackHandleScope<1> hs(Thread::Current());
  Handle<mirror::DexCache> h_dex_cache(hs.NewHandle(dex_cache));
  return DoResolveString(string_idx, h_dex_cache);
}

ObjPtr<mirror::String> ClassLinker::DoResolveString(dex::StringIndex string_idx,
                                                    Handle<mirror::DexCache> dex_cache) {
  const DexFile& dex_file = *dex_cache->GetDexFile();
  uint32_t utf16_length;
  const char* utf8_data = dex_file.StringDataAndUtf16LengthByIdx(string_idx, &utf16_length);
  ObjPtr<mirror::String> string = intern_table_->InternStrong(utf16_length, utf8_data);
  if (string != nullptr) {
    dex_cache->SetResolvedString(string_idx, string);
  }
  return string;
}

ObjPtr<mirror::String> ClassLinker::DoLookupString(dex::StringIndex string_idx,
                                                   ObjPtr<mirror::DexCache> dex_cache) {
  DCHECK(dex_cache != nullptr);
  const DexFile& dex_file = *dex_cache->GetDexFile();
  uint32_t utf16_length;
  const char* utf8_data = dex_file.StringDataAndUtf16LengthByIdx(string_idx, &utf16_length);
  ObjPtr<mirror::String> string =
      intern_table_->LookupStrong(Thread::Current(), utf16_length, utf8_data);
  if (string != nullptr) {
    dex_cache->SetResolvedString(string_idx, string);
  }
  return string;
}

ObjPtr<mirror::Class> ClassLinker::DoLookupResolvedType(dex::TypeIndex type_idx,
                                                        ObjPtr<mirror::Class> referrer) {
  return DoLookupResolvedType(type_idx, referrer->GetDexCache(), referrer->GetClassLoader());
}

ObjPtr<mirror::Class> ClassLinker::DoLookupResolvedType(dex::TypeIndex type_idx,
                                                        ObjPtr<mirror::DexCache> dex_cache,
                                                        ObjPtr<mirror::ClassLoader> class_loader) {
  const DexFile& dex_file = *dex_cache->GetDexFile();
  const char* descriptor = dex_file.StringByTypeIdx(type_idx);
  DCHECK_NE(*descriptor, '\0') << "descriptor is empty string";
  ObjPtr<mirror::Class> type = nullptr;
  if (descriptor[1] == '\0') {
    // only the descriptors of primitive types should be 1 character long, also avoid class lookup
    // for primitive classes that aren't backed by dex files.
    type = LookupPrimitiveClass(descriptor[0]);
  } else {
    Thread* const self = Thread::Current();
    DCHECK(self != nullptr);
    const size_t hash = ComputeModifiedUtf8Hash(descriptor);
    // Find the class in the loaded classes table.
    type = LookupClass(self, descriptor, hash, class_loader);
  }
  if (type != nullptr) {
    if (type->IsResolved()) {
      dex_cache->SetResolvedType(type_idx, type);
    } else {
      type = nullptr;
    }
  }
  return type;
}

template <typename T>
ObjPtr<mirror::Class> ClassLinker::DoResolveType(dex::TypeIndex type_idx, T referrer) {
  StackHandleScope<2> hs(Thread::Current());
  Handle<mirror::DexCache> dex_cache(hs.NewHandle(referrer->GetDexCache()));
  Handle<mirror::ClassLoader> class_loader(hs.NewHandle(referrer->GetClassLoader()));
  return DoResolveType(type_idx, dex_cache, class_loader);
}

// Instantiate the above.
template ObjPtr<mirror::Class> ClassLinker::DoResolveType(dex::TypeIndex type_idx,
                                                          ArtField* referrer);
template ObjPtr<mirror::Class> ClassLinker::DoResolveType(dex::TypeIndex type_idx,
                                                          ArtMethod* referrer);
template ObjPtr<mirror::Class> ClassLinker::DoResolveType(dex::TypeIndex type_idx,
                                                          ObjPtr<mirror::Class> referrer);

ObjPtr<mirror::Class> ClassLinker::DoResolveType(dex::TypeIndex type_idx,
                                                 Handle<mirror::DexCache> dex_cache,
                                                 Handle<mirror::ClassLoader> class_loader) {
  Thread* self = Thread::Current();
  const char* descriptor = dex_cache->GetDexFile()->StringByTypeIdx(type_idx);
  ObjPtr<mirror::Class> resolved = FindClass(self, descriptor, class_loader);
  if (resolved != nullptr) {
    // TODO: we used to throw here if resolved's class loader was not the
    //       boot class loader. This was to permit different classes with the
    //       same name to be loaded simultaneously by different loaders
    dex_cache->SetResolvedType(type_idx, resolved);
  } else {
    CHECK(self->IsExceptionPending())
        << "Expected pending exception for failed resolution of: " << descriptor;
    // Convert a ClassNotFoundException to a NoClassDefFoundError.
    StackHandleScope<1> hs(self);
    Handle<mirror::Throwable> cause(hs.NewHandle(self->GetException()));
    if (cause->InstanceOf(GetClassRoot(ClassRoot::kJavaLangClassNotFoundException, this))) {
      DCHECK(resolved == nullptr);  // No Handle needed to preserve resolved.
      self->ClearException();
      ThrowNoClassDefFoundError("Failed resolution of: %s", descriptor);
      self->GetException()->SetCause(cause.Get());
    }
  }
  DCHECK((resolved == nullptr) || resolved->IsResolved())
      << resolved->PrettyDescriptor() << " " << resolved->GetStatus();
  return resolved;
}

ArtMethod* ClassLinker::FindResolvedMethod(ObjPtr<mirror::Class> klass,
                                           ObjPtr<mirror::DexCache> dex_cache,
                                           ObjPtr<mirror::ClassLoader> class_loader,
                                           uint32_t method_idx) {
  // Search for the method using dex_cache and method_idx. The Class::Find*Method()
  // functions can optimize the search if the dex_cache is the same as the DexCache
  // of the class, with fall-back to name and signature search otherwise.
  ArtMethod* resolved = nullptr;
  if (klass->IsInterface()) {
    resolved = klass->FindInterfaceMethod(dex_cache, method_idx, image_pointer_size_);
  } else {
    resolved = klass->FindClassMethod(dex_cache, method_idx, image_pointer_size_);
  }
  DCHECK(resolved == nullptr || resolved->GetDeclaringClassUnchecked() != nullptr);
  if (resolved != nullptr &&
      hiddenapi::ShouldDenyAccessToMember(resolved,
                                          hiddenapi::AccessContext(class_loader, dex_cache),
                                          hiddenapi::AccessMethod::kLinking)) {
    resolved = nullptr;
  }
  if (resolved != nullptr) {
    // In case of jmvti, the dex file gets verified before being registered, so first
    // check if it's registered before checking class tables.
    const DexFile& dex_file = *dex_cache->GetDexFile();
    DCHECK(!IsDexFileRegistered(Thread::Current(), dex_file) ||
           FindClassTable(Thread::Current(), dex_cache) == ClassTableForClassLoader(class_loader))
        << "DexFile referrer: " << dex_file.GetLocation()
        << " ClassLoader: " << DescribeLoaders(class_loader, "");
    // Be a good citizen and update the dex cache to speed subsequent calls.
    dex_cache->SetResolvedMethod(method_idx, resolved, image_pointer_size_);
    // Disable the following invariant check as the verifier breaks it. b/73760543
    // const DexFile::MethodId& method_id = dex_file.GetMethodId(method_idx);
    // DCHECK(LookupResolvedType(method_id.class_idx_, dex_cache, class_loader) != nullptr)
    //    << "Method: " << resolved->PrettyMethod() << ", "
    //    << "Class: " << klass->PrettyClass() << " (" << klass->GetStatus() << "), "
    //    << "DexFile referrer: " << dex_file.GetLocation();
  }
  return resolved;
}

// Returns true if `method` is either null or hidden.
// Does not print any warnings if it is hidden.
static bool CheckNoSuchMethod(ArtMethod* method,
                              ObjPtr<mirror::DexCache> dex_cache,
                              ObjPtr<mirror::ClassLoader> class_loader)
      REQUIRES_SHARED(Locks::mutator_lock_) {
  return method == nullptr ||
         hiddenapi::ShouldDenyAccessToMember(method,
                                             hiddenapi::AccessContext(class_loader, dex_cache),
                                             hiddenapi::AccessMethod::kNone);  // no warnings
}

ArtMethod* ClassLinker::FindIncompatibleMethod(ObjPtr<mirror::Class> klass,
                                               ObjPtr<mirror::DexCache> dex_cache,
                                               ObjPtr<mirror::ClassLoader> class_loader,
                                               uint32_t method_idx) {
  if (klass->IsInterface()) {
    ArtMethod* method = klass->FindClassMethod(dex_cache, method_idx, image_pointer_size_);
    return CheckNoSuchMethod(method, dex_cache, class_loader) ? nullptr : method;
  } else {
    // If there was an interface method with the same signature, we would have
    // found it in the "copied" methods. Only DCHECK that the interface method
    // really does not exist.
    if (kIsDebugBuild) {
      ArtMethod* method =
          klass->FindInterfaceMethod(dex_cache, method_idx, image_pointer_size_);
      DCHECK(CheckNoSuchMethod(method, dex_cache, class_loader));
    }
    return nullptr;
  }
}

template <ClassLinker::ResolveMode kResolveMode>
ArtMethod* ClassLinker::ResolveMethod(uint32_t method_idx,
                                      Handle<mirror::DexCache> dex_cache,
                                      Handle<mirror::ClassLoader> class_loader,
                                      ArtMethod* referrer,
                                      InvokeType type) {
  DCHECK(dex_cache != nullptr);
  DCHECK(referrer == nullptr || !referrer->IsProxyMethod());
  // Check for hit in the dex cache.
  PointerSize pointer_size = image_pointer_size_;
  ArtMethod* resolved = dex_cache->GetResolvedMethod(method_idx, pointer_size);
  Thread::PoisonObjectPointersIfDebug();
  DCHECK(resolved == nullptr || !resolved->IsRuntimeMethod());
  bool valid_dex_cache_method = resolved != nullptr;
  if (kResolveMode == ResolveMode::kNoChecks && valid_dex_cache_method) {
    // We have a valid method from the DexCache and no checks to perform.
    DCHECK(resolved->GetDeclaringClassUnchecked() != nullptr) << resolved->GetDexMethodIndex();
    return resolved;
  }
  const DexFile& dex_file = *dex_cache->GetDexFile();
  const dex::MethodId& method_id = dex_file.GetMethodId(method_idx);
  ObjPtr<mirror::Class> klass = nullptr;
  if (valid_dex_cache_method) {
    // We have a valid method from the DexCache but we need to perform ICCE and IAE checks.
    DCHECK(resolved->GetDeclaringClassUnchecked() != nullptr) << resolved->GetDexMethodIndex();
    klass = LookupResolvedType(method_id.class_idx_, dex_cache.Get(), class_loader.Get());
    if (UNLIKELY(klass == nullptr)) {
      // We normaly should not end up here. However the verifier currently doesn't guarantee
      // the invariant of having the klass in the class table. b/73760543
      klass = ResolveType(method_id.class_idx_, dex_cache, class_loader);
    }
  } else {
    // The method was not in the DexCache, resolve the declaring class.
    klass = ResolveType(method_id.class_idx_, dex_cache, class_loader);
    if (klass == nullptr) {
      DCHECK(Thread::Current()->IsExceptionPending());
      return nullptr;
    }
  }

  // Check if the invoke type matches the class type.
  if (kResolveMode == ResolveMode::kCheckICCEAndIAE &&
      CheckInvokeClassMismatch</* kThrow= */ true>(
          dex_cache.Get(), type, [klass]() { return klass; })) {
    DCHECK(Thread::Current()->IsExceptionPending());
    return nullptr;
  }

  if (!valid_dex_cache_method) {
    resolved = FindResolvedMethod(klass, dex_cache.Get(), class_loader.Get(), method_idx);
  }

  // Note: We can check for IllegalAccessError only if we have a referrer.
  if (kResolveMode == ResolveMode::kCheckICCEAndIAE && resolved != nullptr && referrer != nullptr) {
    ObjPtr<mirror::Class> methods_class = resolved->GetDeclaringClass();
    ObjPtr<mirror::Class> referring_class = referrer->GetDeclaringClass();
    if (!referring_class->CheckResolvedMethodAccess(methods_class,
                                                    resolved,
                                                    dex_cache.Get(),
                                                    method_idx,
                                                    type)) {
      DCHECK(Thread::Current()->IsExceptionPending());
      return nullptr;
    }
  }

  // If we found a method, check for incompatible class changes.
  if (LIKELY(resolved != nullptr) &&
      LIKELY(kResolveMode == ResolveMode::kNoChecks ||
             !resolved->CheckIncompatibleClassChange(type))) {
    return resolved;
  } else {
    // If we had a method, or if we can find one with another lookup type,
    // it's an incompatible-class-change error.
    if (resolved == nullptr) {
      resolved = FindIncompatibleMethod(klass, dex_cache.Get(), class_loader.Get(), method_idx);
    }
    if (resolved != nullptr) {
      ThrowIncompatibleClassChangeError(type, resolved->GetInvokeType(), resolved, referrer);
    } else {
      // We failed to find the method (using all lookup types), so throw a NoSuchMethodError.
      const char* name = dex_file.StringDataByIdx(method_id.name_idx_);
      const Signature signature = dex_file.GetMethodSignature(method_id);
      ThrowNoSuchMethodError(type, klass, name, signature);
    }
    Thread::Current()->AssertPendingException();
    return nullptr;
  }
}

ArtMethod* ClassLinker::ResolveMethodWithoutInvokeType(uint32_t method_idx,
                                                       Handle<mirror::DexCache> dex_cache,
                                                       Handle<mirror::ClassLoader> class_loader) {
  ArtMethod* resolved = dex_cache->GetResolvedMethod(method_idx, image_pointer_size_);
  Thread::PoisonObjectPointersIfDebug();
  if (resolved != nullptr) {
    DCHECK(!resolved->IsRuntimeMethod());
    DCHECK(resolved->GetDeclaringClassUnchecked() != nullptr) << resolved->GetDexMethodIndex();
    return resolved;
  }
  // Fail, get the declaring class.
  const dex::MethodId& method_id = dex_cache->GetDexFile()->GetMethodId(method_idx);
  ObjPtr<mirror::Class> klass = ResolveType(method_id.class_idx_, dex_cache, class_loader);
  if (klass == nullptr) {
    Thread::Current()->AssertPendingException();
    return nullptr;
  }
  if (klass->IsInterface()) {
    resolved = klass->FindInterfaceMethod(dex_cache.Get(), method_idx, image_pointer_size_);
  } else {
    resolved = klass->FindClassMethod(dex_cache.Get(), method_idx, image_pointer_size_);
  }
  if (resolved != nullptr &&
      hiddenapi::ShouldDenyAccessToMember(
          resolved,
          hiddenapi::AccessContext(class_loader.Get(), dex_cache.Get()),
          hiddenapi::AccessMethod::kLinking)) {
    resolved = nullptr;
  }
  return resolved;
}

ArtField* ClassLinker::LookupResolvedField(uint32_t field_idx,
                                           ObjPtr<mirror::DexCache> dex_cache,
                                           ObjPtr<mirror::ClassLoader> class_loader,
                                           bool is_static) {
  const DexFile& dex_file = *dex_cache->GetDexFile();
  const dex::FieldId& field_id = dex_file.GetFieldId(field_idx);
  ObjPtr<mirror::Class> klass = dex_cache->GetResolvedType(field_id.class_idx_);
  if (klass == nullptr) {
    klass = LookupResolvedType(field_id.class_idx_, dex_cache, class_loader);
  }
  if (klass == nullptr) {
    // The class has not been resolved yet, so the field is also unresolved.
    return nullptr;
  }
  DCHECK(klass->IsResolved());

  return FindResolvedField(klass, dex_cache, class_loader, field_idx, is_static);
}

ArtField* ClassLinker::ResolveField(uint32_t field_idx,
                                    Handle<mirror::DexCache> dex_cache,
                                    Handle<mirror::ClassLoader> class_loader,
                                    bool is_static) {
  DCHECK(dex_cache != nullptr);
  ArtField* resolved = dex_cache->GetResolvedField(field_idx, image_pointer_size_);
  Thread::PoisonObjectPointersIfDebug();
  if (resolved != nullptr) {
    return resolved;
  }
  const DexFile& dex_file = *dex_cache->GetDexFile();
  const dex::FieldId& field_id = dex_file.GetFieldId(field_idx);
  ObjPtr<mirror::Class> klass = ResolveType(field_id.class_idx_, dex_cache, class_loader);
  if (klass == nullptr) {
    DCHECK(Thread::Current()->IsExceptionPending());
    return nullptr;
  }

  resolved = FindResolvedField(klass, dex_cache.Get(), class_loader.Get(), field_idx, is_static);
  if (resolved == nullptr) {
    const char* name = dex_file.GetFieldName(field_id);
    const char* type = dex_file.GetFieldTypeDescriptor(field_id);
    ThrowNoSuchFieldError(is_static ? "static " : "instance ", klass, type, name);
  }
  return resolved;
}

ArtField* ClassLinker::ResolveFieldJLS(uint32_t field_idx,
                                       Handle<mirror::DexCache> dex_cache,
                                       Handle<mirror::ClassLoader> class_loader) {
  DCHECK(dex_cache != nullptr);
  ArtField* resolved = dex_cache->GetResolvedField(field_idx, image_pointer_size_);
  Thread::PoisonObjectPointersIfDebug();
  if (resolved != nullptr) {
    return resolved;
  }
  const DexFile& dex_file = *dex_cache->GetDexFile();
  const dex::FieldId& field_id = dex_file.GetFieldId(field_idx);
  ObjPtr<mirror::Class> klass = ResolveType(field_id.class_idx_, dex_cache, class_loader);
  if (klass == nullptr) {
    DCHECK(Thread::Current()->IsExceptionPending());
    return nullptr;
  }

  resolved = FindResolvedFieldJLS(klass, dex_cache.Get(), class_loader.Get(), field_idx);
  if (resolved == nullptr) {
    const char* name = dex_file.GetFieldName(field_id);
    const char* type = dex_file.GetFieldTypeDescriptor(field_id);
    ThrowNoSuchFieldError("", klass, type, name);
  }
  return resolved;
}

ArtField* ClassLinker::FindResolvedField(ObjPtr<mirror::Class> klass,
                                         ObjPtr<mirror::DexCache> dex_cache,
                                         ObjPtr<mirror::ClassLoader> class_loader,
                                         uint32_t field_idx,
                                         bool is_static) {
  ArtField* resolved = nullptr;
  Thread* self = is_static ? Thread::Current() : nullptr;
  const DexFile& dex_file = *dex_cache->GetDexFile();

  resolved = is_static ? mirror::Class::FindStaticField(self, klass, dex_cache, field_idx)
                       : klass->FindInstanceField(dex_cache, field_idx);

  if (resolved == nullptr) {
    const dex::FieldId& field_id = dex_file.GetFieldId(field_idx);
    const char* name = dex_file.GetFieldName(field_id);
    const char* type = dex_file.GetFieldTypeDescriptor(field_id);
    resolved = is_static ? mirror::Class::FindStaticField(self, klass, name, type)
                         : klass->FindInstanceField(name, type);
  }

  if (resolved != nullptr &&
      hiddenapi::ShouldDenyAccessToMember(resolved,
                                          hiddenapi::AccessContext(class_loader, dex_cache),
                                          hiddenapi::AccessMethod::kLinking)) {
    resolved = nullptr;
  }

  if (resolved != nullptr) {
    dex_cache->SetResolvedField(field_idx, resolved, image_pointer_size_);
  }

  return resolved;
}

ArtField* ClassLinker::FindResolvedFieldJLS(ObjPtr<mirror::Class> klass,
                                            ObjPtr<mirror::DexCache> dex_cache,
                                            ObjPtr<mirror::ClassLoader> class_loader,
                                            uint32_t field_idx) {
  ArtField* resolved = nullptr;
  Thread* self = Thread::Current();
  const DexFile& dex_file = *dex_cache->GetDexFile();
  const dex::FieldId& field_id = dex_file.GetFieldId(field_idx);

  const char* name = dex_file.GetFieldName(field_id);
  const char* type = dex_file.GetFieldTypeDescriptor(field_id);
  resolved = mirror::Class::FindField(self, klass, name, type);

  if (resolved != nullptr &&
      hiddenapi::ShouldDenyAccessToMember(resolved,
                                          hiddenapi::AccessContext(class_loader, dex_cache),
                                          hiddenapi::AccessMethod::kLinking)) {
    resolved = nullptr;
  }

  if (resolved != nullptr) {
    dex_cache->SetResolvedField(field_idx, resolved, image_pointer_size_);
  }

  return resolved;
}

ObjPtr<mirror::MethodType> ClassLinker::ResolveMethodType(
    Thread* self,
    dex::ProtoIndex proto_idx,
    Handle<mirror::DexCache> dex_cache,
    Handle<mirror::ClassLoader> class_loader) {
  DCHECK(Runtime::Current()->IsMethodHandlesEnabled());
  DCHECK(dex_cache != nullptr);

  ObjPtr<mirror::MethodType> resolved = dex_cache->GetResolvedMethodType(proto_idx);
  if (resolved != nullptr) {
    return resolved;
  }

  StackHandleScope<4> hs(self);

  // First resolve the return type.
  const DexFile& dex_file = *dex_cache->GetDexFile();
  const dex::ProtoId& proto_id = dex_file.GetProtoId(proto_idx);
  Handle<mirror::Class> return_type(hs.NewHandle(
      ResolveType(proto_id.return_type_idx_, dex_cache, class_loader)));
  if (return_type == nullptr) {
    DCHECK(self->IsExceptionPending());
    return nullptr;
  }

  // Then resolve the argument types.
  //
  // TODO: Is there a better way to figure out the number of method arguments
  // other than by looking at the shorty ?
  const size_t num_method_args = strlen(dex_file.StringDataByIdx(proto_id.shorty_idx_)) - 1;

  ObjPtr<mirror::Class> array_of_class = GetClassRoot<mirror::ObjectArray<mirror::Class>>(this);
  Handle<mirror::ObjectArray<mirror::Class>> method_params(hs.NewHandle(
      mirror::ObjectArray<mirror::Class>::Alloc(self, array_of_class, num_method_args)));
  if (method_params == nullptr) {
    DCHECK(self->IsExceptionPending());
    return nullptr;
  }

  DexFileParameterIterator it(dex_file, proto_id);
  int32_t i = 0;
  MutableHandle<mirror::Class> param_class = hs.NewHandle<mirror::Class>(nullptr);
  for (; it.HasNext(); it.Next()) {
    const dex::TypeIndex type_idx = it.GetTypeIdx();
    param_class.Assign(ResolveType(type_idx, dex_cache, class_loader));
    if (param_class == nullptr) {
      DCHECK(self->IsExceptionPending());
      return nullptr;
    }

    method_params->Set(i++, param_class.Get());
  }

  DCHECK(!it.HasNext());

  Handle<mirror::MethodType> type = hs.NewHandle(
      mirror::MethodType::Create(self, return_type, method_params));
  dex_cache->SetResolvedMethodType(proto_idx, type.Get());

  return type.Get();
}

ObjPtr<mirror::MethodType> ClassLinker::ResolveMethodType(Thread* self,
                                                          dex::ProtoIndex proto_idx,
                                                          ArtMethod* referrer) {
  StackHandleScope<2> hs(self);
  Handle<mirror::DexCache> dex_cache(hs.NewHandle(referrer->GetDexCache()));
  Handle<mirror::ClassLoader> class_loader(hs.NewHandle(referrer->GetClassLoader()));
  return ResolveMethodType(self, proto_idx, dex_cache, class_loader);
}

ObjPtr<mirror::MethodHandle> ClassLinker::ResolveMethodHandleForField(
    Thread* self,
    const dex::MethodHandleItem& method_handle,
    ArtMethod* referrer) {
  DexFile::MethodHandleType handle_type =
      static_cast<DexFile::MethodHandleType>(method_handle.method_handle_type_);
  mirror::MethodHandle::Kind kind;
  bool is_put;
  bool is_static;
  int32_t num_params;
  switch (handle_type) {
    case DexFile::MethodHandleType::kStaticPut: {
      kind = mirror::MethodHandle::Kind::kStaticPut;
      is_put = true;
      is_static = true;
      num_params = 1;
      break;
    }
    case DexFile::MethodHandleType::kStaticGet: {
      kind = mirror::MethodHandle::Kind::kStaticGet;
      is_put = false;
      is_static = true;
      num_params = 0;
      break;
    }
    case DexFile::MethodHandleType::kInstancePut: {
      kind = mirror::MethodHandle::Kind::kInstancePut;
      is_put = true;
      is_static = false;
      num_params = 2;
      break;
    }
    case DexFile::MethodHandleType::kInstanceGet: {
      kind = mirror::MethodHandle::Kind::kInstanceGet;
      is_put = false;
      is_static = false;
      num_params = 1;
      break;
    }
    case DexFile::MethodHandleType::kInvokeStatic:
    case DexFile::MethodHandleType::kInvokeInstance:
    case DexFile::MethodHandleType::kInvokeConstructor:
    case DexFile::MethodHandleType::kInvokeDirect:
    case DexFile::MethodHandleType::kInvokeInterface:
      UNREACHABLE();
  }

  ArtField* target_field =
      ResolveField(method_handle.field_or_method_idx_, referrer, is_static);
  if (LIKELY(target_field != nullptr)) {
    ObjPtr<mirror::Class> target_class = target_field->GetDeclaringClass();
    ObjPtr<mirror::Class> referring_class = referrer->GetDeclaringClass();
    if (UNLIKELY(!referring_class->CanAccessMember(target_class, target_field->GetAccessFlags()))) {
      ThrowIllegalAccessErrorField(referring_class, target_field);
      return nullptr;
    }
    if (UNLIKELY(is_put && target_field->IsFinal())) {
      ThrowIllegalAccessErrorField(referring_class, target_field);
      return nullptr;
    }
  } else {
    DCHECK(Thread::Current()->IsExceptionPending());
    return nullptr;
  }

  StackHandleScope<4> hs(self);
  ObjPtr<mirror::Class> array_of_class = GetClassRoot<mirror::ObjectArray<mirror::Class>>(this);
  Handle<mirror::ObjectArray<mirror::Class>> method_params(hs.NewHandle(
      mirror::ObjectArray<mirror::Class>::Alloc(self, array_of_class, num_params)));
  if (UNLIKELY(method_params == nullptr)) {
    DCHECK(self->IsExceptionPending());
    return nullptr;
  }

  Handle<mirror::Class> constructor_class;
  Handle<mirror::Class> return_type;
  switch (handle_type) {
    case DexFile::MethodHandleType::kStaticPut: {
      method_params->Set(0, target_field->ResolveType());
      return_type = hs.NewHandle(GetClassRoot(ClassRoot::kPrimitiveVoid, this));
      break;
    }
    case DexFile::MethodHandleType::kStaticGet: {
      return_type = hs.NewHandle(target_field->ResolveType());
      break;
    }
    case DexFile::MethodHandleType::kInstancePut: {
      method_params->Set(0, target_field->GetDeclaringClass());
      method_params->Set(1, target_field->ResolveType());
      return_type = hs.NewHandle(GetClassRoot(ClassRoot::kPrimitiveVoid, this));
      break;
    }
    case DexFile::MethodHandleType::kInstanceGet: {
      method_params->Set(0, target_field->GetDeclaringClass());
      return_type = hs.NewHandle(target_field->ResolveType());
      break;
    }
    case DexFile::MethodHandleType::kInvokeStatic:
    case DexFile::MethodHandleType::kInvokeInstance:
    case DexFile::MethodHandleType::kInvokeConstructor:
    case DexFile::MethodHandleType::kInvokeDirect:
    case DexFile::MethodHandleType::kInvokeInterface:
      UNREACHABLE();
  }

  for (int32_t i = 0; i < num_params; ++i) {
    if (UNLIKELY(method_params->Get(i) == nullptr)) {
      DCHECK(self->IsExceptionPending());
      return nullptr;
    }
  }

  if (UNLIKELY(return_type.IsNull())) {
    DCHECK(self->IsExceptionPending());
    return nullptr;
  }

  Handle<mirror::MethodType>
      method_type(hs.NewHandle(mirror::MethodType::Create(self, return_type, method_params)));
  if (UNLIKELY(method_type.IsNull())) {
    DCHECK(self->IsExceptionPending());
    return nullptr;
  }

  uintptr_t target = reinterpret_cast<uintptr_t>(target_field);
  return mirror::MethodHandleImpl::Create(self, target, kind, method_type);
}

ObjPtr<mirror::MethodHandle> ClassLinker::ResolveMethodHandleForMethod(
    Thread* self,
    const dex::MethodHandleItem& method_handle,
    ArtMethod* referrer) {
  DexFile::MethodHandleType handle_type =
      static_cast<DexFile::MethodHandleType>(method_handle.method_handle_type_);
  mirror::MethodHandle::Kind kind;
  uint32_t receiver_count = 0;
  ArtMethod* target_method = nullptr;
  switch (handle_type) {
    case DexFile::MethodHandleType::kStaticPut:
    case DexFile::MethodHandleType::kStaticGet:
    case DexFile::MethodHandleType::kInstancePut:
    case DexFile::MethodHandleType::kInstanceGet:
      UNREACHABLE();
    case DexFile::MethodHandleType::kInvokeStatic: {
      kind = mirror::MethodHandle::Kind::kInvokeStatic;
      receiver_count = 0;
      target_method = ResolveMethod<ResolveMode::kNoChecks>(self,
                                                            method_handle.field_or_method_idx_,
                                                            referrer,
                                                            InvokeType::kStatic);
      break;
    }
    case DexFile::MethodHandleType::kInvokeInstance: {
      kind = mirror::MethodHandle::Kind::kInvokeVirtual;
      receiver_count = 1;
      target_method = ResolveMethod<ResolveMode::kNoChecks>(self,
                                                            method_handle.field_or_method_idx_,
                                                            referrer,
                                                            InvokeType::kVirtual);
      break;
    }
    case DexFile::MethodHandleType::kInvokeConstructor: {
      // Constructors are currently implemented as a transform. They
      // are special cased later in this method.
      kind = mirror::MethodHandle::Kind::kInvokeTransform;
      receiver_count = 0;
      target_method = ResolveMethod<ResolveMode::kNoChecks>(self,
                                                            method_handle.field_or_method_idx_,
                                                            referrer,
                                                            InvokeType::kDirect);
      break;
    }
    case DexFile::MethodHandleType::kInvokeDirect: {
      kind = mirror::MethodHandle::Kind::kInvokeDirect;
      receiver_count = 1;
      StackHandleScope<2> hs(self);
      // A constant method handle with type kInvokeDirect can refer to
      // a method that is private or to a method in a super class. To
      // disambiguate the two options, we resolve the method ignoring
      // the invocation type to determine if the method is private. We
      // then resolve again specifying the intended invocation type to
      // force the appropriate checks.
      target_method = ResolveMethodWithoutInvokeType(method_handle.field_or_method_idx_,
                                                     hs.NewHandle(referrer->GetDexCache()),
                                                     hs.NewHandle(referrer->GetClassLoader()));
      if (UNLIKELY(target_method == nullptr)) {
        break;
      }

      if (target_method->IsPrivate()) {
        kind = mirror::MethodHandle::Kind::kInvokeDirect;
        target_method = ResolveMethod<ResolveMode::kNoChecks>(self,
                                                              method_handle.field_or_method_idx_,
                                                              referrer,
                                                              InvokeType::kDirect);
      } else {
        kind = mirror::MethodHandle::Kind::kInvokeSuper;
        target_method = ResolveMethod<ResolveMode::kNoChecks>(self,
                                                              method_handle.field_or_method_idx_,
                                                              referrer,
                                                              InvokeType::kSuper);
        if (UNLIKELY(target_method == nullptr)) {
          break;
        }
        // Find the method specified in the parent in referring class
        // so invoke-super invokes the method in the parent of the
        // referrer.
        target_method =
            referrer->GetDeclaringClass()->FindVirtualMethodForVirtual(target_method,
                                                                       kRuntimePointerSize);
      }
      break;
    }
    case DexFile::MethodHandleType::kInvokeInterface: {
      kind = mirror::MethodHandle::Kind::kInvokeInterface;
      receiver_count = 1;
      target_method = ResolveMethod<ResolveMode::kNoChecks>(self,
                                                            method_handle.field_or_method_idx_,
                                                            referrer,
                                                            InvokeType::kInterface);
      break;
    }
  }

  if (UNLIKELY(target_method == nullptr)) {
    DCHECK(Thread::Current()->IsExceptionPending());
    return nullptr;
  }

  ObjPtr<mirror::Class> target_class = target_method->GetDeclaringClass();
  ObjPtr<mirror::Class> referring_class = referrer->GetDeclaringClass();
  uint32_t access_flags = target_method->GetAccessFlags();
  if (UNLIKELY(!referring_class->CanAccessMember(target_class, access_flags))) {
    ThrowIllegalAccessErrorMethod(referring_class, target_method);
    return nullptr;
  }

  // Calculate the number of parameters from the method shorty. We add the
  // receiver count (0 or 1) and deduct one for the return value.
  uint32_t shorty_length;
  target_method->GetShorty(&shorty_length);
  int32_t num_params = static_cast<int32_t>(shorty_length + receiver_count - 1);

  StackHandleScope<5> hs(self);
  ObjPtr<mirror::Class> array_of_class = GetClassRoot<mirror::ObjectArray<mirror::Class>>(this);
  Handle<mirror::ObjectArray<mirror::Class>> method_params(hs.NewHandle(
      mirror::ObjectArray<mirror::Class>::Alloc(self, array_of_class, num_params)));
  if (method_params.Get() == nullptr) {
    DCHECK(self->IsExceptionPending());
    return nullptr;
  }

  const DexFile* dex_file = referrer->GetDexFile();
  const dex::MethodId& method_id = dex_file->GetMethodId(method_handle.field_or_method_idx_);
  int32_t index = 0;
  if (receiver_count != 0) {
    // Insert receiver. Use the class identified in the method handle rather than the declaring
    // class of the resolved method which may be super class or default interface method
    // (b/115964401).
    ObjPtr<mirror::Class> receiver_class = LookupResolvedType(method_id.class_idx_, referrer);
    // receiver_class should have been resolved when resolving the target method.
    DCHECK(receiver_class != nullptr);
    method_params->Set(index++, receiver_class);
  }

  const dex::ProtoId& proto_id = dex_file->GetProtoId(method_id.proto_idx_);
  DexFileParameterIterator it(*dex_file, proto_id);
  while (it.HasNext()) {
    DCHECK_LT(index, num_params);
    const dex::TypeIndex type_idx = it.GetTypeIdx();
    ObjPtr<mirror::Class> klass = ResolveType(type_idx, referrer);
    if (nullptr == klass) {
      DCHECK(self->IsExceptionPending());
      return nullptr;
    }
    method_params->Set(index++, klass);
    it.Next();
  }

  Handle<mirror::Class> return_type =
      hs.NewHandle(ResolveType(proto_id.return_type_idx_, referrer));
  if (UNLIKELY(return_type.IsNull())) {
    DCHECK(self->IsExceptionPending());
    return nullptr;
  }

  Handle<mirror::MethodType>
      method_type(hs.NewHandle(mirror::MethodType::Create(self, return_type, method_params)));
  if (UNLIKELY(method_type.IsNull())) {
    DCHECK(self->IsExceptionPending());
    return nullptr;
  }

  if (UNLIKELY(handle_type == DexFile::MethodHandleType::kInvokeConstructor)) {
    Handle<mirror::Class> constructor_class = hs.NewHandle(target_method->GetDeclaringClass());
    Handle<mirror::MethodHandlesLookup> lookup =
        hs.NewHandle(mirror::MethodHandlesLookup::GetDefault(self));
    return lookup->FindConstructor(self, constructor_class, method_type);
  }

  uintptr_t target = reinterpret_cast<uintptr_t>(target_method);
  return mirror::MethodHandleImpl::Create(self, target, kind, method_type);
}

ObjPtr<mirror::MethodHandle> ClassLinker::ResolveMethodHandle(Thread* self,
                                                              uint32_t method_handle_idx,
                                                              ArtMethod* referrer)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  const DexFile* const dex_file = referrer->GetDexFile();
  const dex::MethodHandleItem& method_handle = dex_file->GetMethodHandle(method_handle_idx);
  switch (static_cast<DexFile::MethodHandleType>(method_handle.method_handle_type_)) {
    case DexFile::MethodHandleType::kStaticPut:
    case DexFile::MethodHandleType::kStaticGet:
    case DexFile::MethodHandleType::kInstancePut:
    case DexFile::MethodHandleType::kInstanceGet:
      return ResolveMethodHandleForField(self, method_handle, referrer);
    case DexFile::MethodHandleType::kInvokeStatic:
    case DexFile::MethodHandleType::kInvokeInstance:
    case DexFile::MethodHandleType::kInvokeConstructor:
    case DexFile::MethodHandleType::kInvokeDirect:
    case DexFile::MethodHandleType::kInvokeInterface:
      return ResolveMethodHandleForMethod(self, method_handle, referrer);
  }
}

bool ClassLinker::IsQuickResolutionStub(const void* entry_point) const {
  return (entry_point == GetQuickResolutionStub()) ||
      (quick_resolution_trampoline_ == entry_point);
}

bool ClassLinker::IsQuickToInterpreterBridge(const void* entry_point) const {
  return (entry_point == GetQuickToInterpreterBridge()) ||
      (quick_to_interpreter_bridge_trampoline_ == entry_point);
}

bool ClassLinker::IsQuickGenericJniStub(const void* entry_point) const {
  return (entry_point == GetQuickGenericJniStub()) ||
      (quick_generic_jni_trampoline_ == entry_point);
}

bool ClassLinker::IsJniDlsymLookupStub(const void* entry_point) const {
  return entry_point == GetJniDlsymLookupStub();
}

const void* ClassLinker::GetRuntimeQuickGenericJniStub() const {
  return GetQuickGenericJniStub();
}

void ClassLinker::SetEntryPointsToInterpreter(ArtMethod* method) const {
  if (!method->IsNative()) {
    method->SetEntryPointFromQuickCompiledCode(GetQuickToInterpreterBridge());
  } else {
    method->SetEntryPointFromQuickCompiledCode(GetQuickGenericJniStub());
  }
}

void ClassLinker::SetEntryPointsForObsoleteMethod(ArtMethod* method) const {
  DCHECK(method->IsObsolete());
  // We cannot mess with the entrypoints of native methods because they are used to determine how
  // large the method's quick stack frame is. Without this information we cannot walk the stacks.
  if (!method->IsNative()) {
    method->SetEntryPointFromQuickCompiledCode(GetInvokeObsoleteMethodStub());
  }
}

void ClassLinker::DumpForSigQuit(std::ostream& os) {
  ScopedObjectAccess soa(Thread::Current());
  ReaderMutexLock mu(soa.Self(), *Locks::classlinker_classes_lock_);
  os << "Zygote loaded classes=" << NumZygoteClasses() << " post zygote classes="
     << NumNonZygoteClasses() << "\n";
  ReaderMutexLock mu2(soa.Self(), *Locks::dex_lock_);
  os << "Dumping registered class loaders\n";
  size_t class_loader_index = 0;
  for (const ClassLoaderData& class_loader : class_loaders_) {
    ObjPtr<mirror::ClassLoader> loader =
        ObjPtr<mirror::ClassLoader>::DownCast(soa.Self()->DecodeJObject(class_loader.weak_root));
    if (loader != nullptr) {
      os << "#" << class_loader_index++ << " " << loader->GetClass()->PrettyDescriptor() << ": [";
      bool saw_one_dex_file = false;
      for (const DexCacheData& dex_cache : dex_caches_) {
        if (dex_cache.IsValid() && dex_cache.class_table == class_loader.class_table) {
          if (saw_one_dex_file) {
            os << ":";
          }
          saw_one_dex_file = true;
          os << dex_cache.dex_file->GetLocation();
        }
      }
      os << "]";
      bool found_parent = false;
      if (loader->GetParent() != nullptr) {
        size_t parent_index = 0;
        for (const ClassLoaderData& class_loader2 : class_loaders_) {
          ObjPtr<mirror::ClassLoader> loader2 = ObjPtr<mirror::ClassLoader>::DownCast(
              soa.Self()->DecodeJObject(class_loader2.weak_root));
          if (loader2 == loader->GetParent()) {
            os << ", parent #" << parent_index;
            found_parent = true;
            break;
          }
          parent_index++;
        }
        if (!found_parent) {
          os << ", unregistered parent of type "
             << loader->GetParent()->GetClass()->PrettyDescriptor();
        }
      } else {
        os << ", no parent";
      }
      os << "\n";
    }
  }
  os << "Done dumping class loaders\n";
}

class CountClassesVisitor : public ClassLoaderVisitor {
 public:
  CountClassesVisitor() : num_zygote_classes(0), num_non_zygote_classes(0) {}

  void Visit(ObjPtr<mirror::ClassLoader> class_loader)
      REQUIRES_SHARED(Locks::classlinker_classes_lock_, Locks::mutator_lock_) override {
    ClassTable* const class_table = class_loader->GetClassTable();
    if (class_table != nullptr) {
      num_zygote_classes += class_table->NumZygoteClasses(class_loader);
      num_non_zygote_classes += class_table->NumNonZygoteClasses(class_loader);
    }
  }

  size_t num_zygote_classes;
  size_t num_non_zygote_classes;
};

size_t ClassLinker::NumZygoteClasses() const {
  CountClassesVisitor visitor;
  VisitClassLoaders(&visitor);
  return visitor.num_zygote_classes + boot_class_table_->NumZygoteClasses(nullptr);
}

size_t ClassLinker::NumNonZygoteClasses() const {
  CountClassesVisitor visitor;
  VisitClassLoaders(&visitor);
  return visitor.num_non_zygote_classes + boot_class_table_->NumNonZygoteClasses(nullptr);
}

size_t ClassLinker::NumLoadedClasses() {
  ReaderMutexLock mu(Thread::Current(), *Locks::classlinker_classes_lock_);
  // Only return non zygote classes since these are the ones which apps which care about.
  return NumNonZygoteClasses();
}

pid_t ClassLinker::GetClassesLockOwner() {
  return Locks::classlinker_classes_lock_->GetExclusiveOwnerTid();
}

pid_t ClassLinker::GetDexLockOwner() {
  return Locks::dex_lock_->GetExclusiveOwnerTid();
}

void ClassLinker::SetClassRoot(ClassRoot class_root, ObjPtr<mirror::Class> klass) {
  DCHECK(!init_done_);

  DCHECK(klass != nullptr);
  DCHECK(klass->GetClassLoader() == nullptr);

  mirror::ObjectArray<mirror::Class>* class_roots = class_roots_.Read();
  DCHECK(class_roots != nullptr);
  DCHECK_LT(static_cast<uint32_t>(class_root), static_cast<uint32_t>(ClassRoot::kMax));
  int32_t index = static_cast<int32_t>(class_root);
  DCHECK(class_roots->Get(index) == nullptr);
  class_roots->Set<false>(index, klass);
}

void ClassLinker::AllocAndSetPrimitiveArrayClassRoot(Thread* self,
                                                     ObjPtr<mirror::Class> java_lang_Class,
                                                     ClassRoot primitive_array_class_root,
                                                     ClassRoot primitive_class_root,
                                                     const char* descriptor) {
  StackHandleScope<1> hs(self);
  Handle<mirror::Class> primitive_array_class(hs.NewHandle(
      AllocPrimitiveArrayClass(self, java_lang_Class)));
  primitive_array_class->SetComponentType(GetClassRoot(primitive_class_root, this));
  SetClassRoot(primitive_array_class_root, primitive_array_class.Get());
  CheckSystemClass(self, primitive_array_class, descriptor);
}

ObjPtr<mirror::ClassLoader> ClassLinker::CreateWellKnownClassLoader(
    Thread* self,
    const std::vector<const DexFile*>& dex_files,
    Handle<mirror::Class> loader_class,
    Handle<mirror::ClassLoader> parent_loader,
    Handle<mirror::ObjectArray<mirror::ClassLoader>> shared_libraries) {

  StackHandleScope<5> hs(self);

  ArtField* dex_elements_field =
      jni::DecodeArtField(WellKnownClasses::dalvik_system_DexPathList_dexElements);

  Handle<mirror::Class> dex_elements_class(hs.NewHandle(dex_elements_field->ResolveType()));
  DCHECK(dex_elements_class != nullptr);
  DCHECK(dex_elements_class->IsArrayClass());
  Handle<mirror::ObjectArray<mirror::Object>> h_dex_elements(hs.NewHandle(
      mirror::ObjectArray<mirror::Object>::Alloc(self,
                                                 dex_elements_class.Get(),
                                                 dex_files.size())));
  Handle<mirror::Class> h_dex_element_class =
      hs.NewHandle(dex_elements_class->GetComponentType());

  ArtField* element_file_field =
      jni::DecodeArtField(WellKnownClasses::dalvik_system_DexPathList__Element_dexFile);
  DCHECK_EQ(h_dex_element_class.Get(), element_file_field->GetDeclaringClass());

  ArtField* cookie_field = jni::DecodeArtField(WellKnownClasses::dalvik_system_DexFile_cookie);
  DCHECK_EQ(cookie_field->GetDeclaringClass(), element_file_field->LookupResolvedType());

  ArtField* file_name_field = jni::DecodeArtField(WellKnownClasses::dalvik_system_DexFile_fileName);
  DCHECK_EQ(file_name_field->GetDeclaringClass(), element_file_field->LookupResolvedType());

  // Fill the elements array.
  int32_t index = 0;
  for (const DexFile* dex_file : dex_files) {
    StackHandleScope<4> hs2(self);

    // CreateWellKnownClassLoader is only used by gtests and compiler.
    // Index 0 of h_long_array is supposed to be the oat file but we can leave it null.
    Handle<mirror::LongArray> h_long_array = hs2.NewHandle(mirror::LongArray::Alloc(
        self,
        kDexFileIndexStart + 1));
    DCHECK(h_long_array != nullptr);
    h_long_array->Set(kDexFileIndexStart, reinterpret_cast64<int64_t>(dex_file));

    // Note that this creates a finalizable dalvik.system.DexFile object and a corresponding
    // FinalizerReference which will never get cleaned up without a started runtime.
    Handle<mirror::Object> h_dex_file = hs2.NewHandle(
        cookie_field->GetDeclaringClass()->AllocObject(self));
    DCHECK(h_dex_file != nullptr);
    cookie_field->SetObject<false>(h_dex_file.Get(), h_long_array.Get());

    Handle<mirror::String> h_file_name = hs2.NewHandle(
        mirror::String::AllocFromModifiedUtf8(self, dex_file->GetLocation().c_str()));
    DCHECK(h_file_name != nullptr);
    file_name_field->SetObject<false>(h_dex_file.Get(), h_file_name.Get());

    Handle<mirror::Object> h_element = hs2.NewHandle(h_dex_element_class->AllocObject(self));
    DCHECK(h_element != nullptr);
    element_file_field->SetObject<false>(h_element.Get(), h_dex_file.Get());

    h_dex_elements->Set(index, h_element.Get());
    index++;
  }
  DCHECK_EQ(index, h_dex_elements->GetLength());

  // Create DexPathList.
  Handle<mirror::Object> h_dex_path_list = hs.NewHandle(
      dex_elements_field->GetDeclaringClass()->AllocObject(self));
  DCHECK(h_dex_path_list != nullptr);
  // Set elements.
  dex_elements_field->SetObject<false>(h_dex_path_list.Get(), h_dex_elements.Get());
  // Create an empty List for the "nativeLibraryDirectories," required for native tests.
  // Note: this code is uncommon(oatdump)/testing-only, so don't add further WellKnownClasses
  //       elements.
  {
    ArtField* native_lib_dirs = dex_elements_field->GetDeclaringClass()->
        FindDeclaredInstanceField("nativeLibraryDirectories", "Ljava/util/List;");
    DCHECK(native_lib_dirs != nullptr);
    ObjPtr<mirror::Class> list_class = FindSystemClass(self, "Ljava/util/ArrayList;");
    DCHECK(list_class != nullptr);
    {
      StackHandleScope<1> h_list_scope(self);
      Handle<mirror::Class> h_list_class(h_list_scope.NewHandle<mirror::Class>(list_class));
      bool list_init = EnsureInitialized(self, h_list_class, true, true);
      DCHECK(list_init);
      list_class = h_list_class.Get();
    }
    ObjPtr<mirror::Object> list_object = list_class->AllocObject(self);
    // Note: we leave the object uninitialized. This must never leak into any non-testing code, but
    //       is fine for testing. While it violates a Java-code invariant (the elementData field is
    //       normally never null), as long as one does not try to add elements, this will still
    //       work.
    native_lib_dirs->SetObject<false>(h_dex_path_list.Get(), list_object);
  }

  // Create the class loader..
  Handle<mirror::ClassLoader> h_class_loader = hs.NewHandle<mirror::ClassLoader>(
      ObjPtr<mirror::ClassLoader>::DownCast(loader_class->AllocObject(self)));
  DCHECK(h_class_loader != nullptr);
  // Set DexPathList.
  ArtField* path_list_field =
      jni::DecodeArtField(WellKnownClasses::dalvik_system_BaseDexClassLoader_pathList);
  DCHECK(path_list_field != nullptr);
  path_list_field->SetObject<false>(h_class_loader.Get(), h_dex_path_list.Get());

  // Make a pretend boot-classpath.
  // TODO: Should we scan the image?
  ArtField* const parent_field =
      mirror::Class::FindField(self,
                               h_class_loader->GetClass(),
                               "parent",
                               "Ljava/lang/ClassLoader;");
  DCHECK(parent_field != nullptr);
  if (parent_loader.Get() == nullptr) {
    ScopedObjectAccessUnchecked soa(self);
    ObjPtr<mirror::Object> boot_loader(soa.Decode<mirror::Class>(
        WellKnownClasses::java_lang_BootClassLoader)->AllocObject(self));
    parent_field->SetObject<false>(h_class_loader.Get(), boot_loader);
  } else {
    parent_field->SetObject<false>(h_class_loader.Get(), parent_loader.Get());
  }

  ArtField* shared_libraries_field =
      jni::DecodeArtField(WellKnownClasses::dalvik_system_BaseDexClassLoader_sharedLibraryLoaders);
  DCHECK(shared_libraries_field != nullptr);
  shared_libraries_field->SetObject<false>(h_class_loader.Get(), shared_libraries.Get());

  return h_class_loader.Get();
}

jobject ClassLinker::CreateWellKnownClassLoader(Thread* self,
                                                const std::vector<const DexFile*>& dex_files,
                                                jclass loader_class,
                                                jobject parent_loader,
                                                jobject shared_libraries) {
  CHECK(self->GetJniEnv()->IsSameObject(loader_class,
                                        WellKnownClasses::dalvik_system_PathClassLoader) ||
        self->GetJniEnv()->IsSameObject(loader_class,
                                        WellKnownClasses::dalvik_system_DelegateLastClassLoader) ||
        self->GetJniEnv()->IsSameObject(loader_class,
                                        WellKnownClasses::dalvik_system_InMemoryDexClassLoader));

  // SOAAlreadyRunnable is protected, and we need something to add a global reference.
  // We could move the jobject to the callers, but all call-sites do this...
  ScopedObjectAccessUnchecked soa(self);

  // For now, create a libcore-level DexFile for each ART DexFile. This "explodes" multidex.
  StackHandleScope<4> hs(self);

  Handle<mirror::Class> h_loader_class =
      hs.NewHandle<mirror::Class>(soa.Decode<mirror::Class>(loader_class));
  Handle<mirror::ClassLoader> h_parent =
      hs.NewHandle<mirror::ClassLoader>(soa.Decode<mirror::ClassLoader>(parent_loader));
  Handle<mirror::ObjectArray<mirror::ClassLoader>> h_shared_libraries =
      hs.NewHandle(soa.Decode<mirror::ObjectArray<mirror::ClassLoader>>(shared_libraries));

  ObjPtr<mirror::ClassLoader> loader = CreateWellKnownClassLoader(
      self,
      dex_files,
      h_loader_class,
      h_parent,
      h_shared_libraries);

  // Make it a global ref and return.
  ScopedLocalRef<jobject> local_ref(
      soa.Env(), soa.Env()->AddLocalReference<jobject>(loader));
  return soa.Env()->NewGlobalRef(local_ref.get());
}

jobject ClassLinker::CreatePathClassLoader(Thread* self,
                                           const std::vector<const DexFile*>& dex_files) {
  return CreateWellKnownClassLoader(self,
                                    dex_files,
                                    WellKnownClasses::dalvik_system_PathClassLoader,
                                    nullptr);
}

void ClassLinker::DropFindArrayClassCache() {
  std::fill_n(find_array_class_cache_, kFindArrayCacheSize, GcRoot<mirror::Class>(nullptr));
  find_array_class_cache_next_victim_ = 0;
}

void ClassLinker::VisitClassLoaders(ClassLoaderVisitor* visitor) const {
  Thread* const self = Thread::Current();
  for (const ClassLoaderData& data : class_loaders_) {
    // Need to use DecodeJObject so that we get null for cleared JNI weak globals.
    ObjPtr<mirror::ClassLoader> class_loader = ObjPtr<mirror::ClassLoader>::DownCast(
        self->DecodeJObject(data.weak_root));
    if (class_loader != nullptr) {
      visitor->Visit(class_loader);
    }
  }
}

void ClassLinker::VisitAllocators(AllocatorVisitor* visitor) const {
  for (const ClassLoaderData& data : class_loaders_) {
    LinearAlloc* alloc = data.allocator;
    if (alloc != nullptr && !visitor->Visit(alloc)) {
        break;
    }
  }
}

void ClassLinker::InsertDexFileInToClassLoader(ObjPtr<mirror::Object> dex_file,
                                               ObjPtr<mirror::ClassLoader> class_loader) {
  DCHECK(dex_file != nullptr);
  Thread* const self = Thread::Current();
  WriterMutexLock mu(self, *Locks::classlinker_classes_lock_);
  ClassTable* const table = ClassTableForClassLoader(class_loader);
  DCHECK(table != nullptr);
  if (table->InsertStrongRoot(dex_file) && class_loader != nullptr) {
    // It was not already inserted, perform the write barrier to let the GC know the class loader's
    // class table was modified.
    WriteBarrier::ForEveryFieldWrite(class_loader);
  }
}

void ClassLinker::CleanupClassLoaders() {
  Thread* const self = Thread::Current();
  std::vector<ClassLoaderData> to_delete;
  // Do the delete outside the lock to avoid lock violation in jit code cache.
  {
    WriterMutexLock mu(self, *Locks::classlinker_classes_lock_);
    for (auto it = class_loaders_.begin(); it != class_loaders_.end(); ) {
      const ClassLoaderData& data = *it;
      // Need to use DecodeJObject so that we get null for cleared JNI weak globals.
      ObjPtr<mirror::ClassLoader> class_loader =
          ObjPtr<mirror::ClassLoader>::DownCast(self->DecodeJObject(data.weak_root));
      if (class_loader != nullptr) {
        ++it;
      } else {
        VLOG(class_linker) << "Freeing class loader";
        to_delete.push_back(data);
        it = class_loaders_.erase(it);
      }
    }
  }
  for (ClassLoaderData& data : to_delete) {
    // CHA unloading analysis and SingleImplementaion cleanups are required.
    DeleteClassLoader(self, data, /*cleanup_cha=*/ true);
  }
}

class GetResolvedClassesVisitor : public ClassVisitor {
 public:
  GetResolvedClassesVisitor(std::set<DexCacheResolvedClasses>* result, bool ignore_boot_classes)
      : result_(result),
        ignore_boot_classes_(ignore_boot_classes),
        last_resolved_classes_(result->end()),
        last_dex_file_(nullptr),
        vlog_is_on_(VLOG_IS_ON(class_linker)),
        extra_stats_(),
        last_extra_stats_(extra_stats_.end()) { }

  bool operator()(ObjPtr<mirror::Class> klass) override REQUIRES_SHARED(Locks::mutator_lock_) {
    if (!klass->IsProxyClass() &&
        !klass->IsArrayClass() &&
        klass->IsResolved() &&
        !klass->IsErroneousResolved() &&
        (!ignore_boot_classes_ || klass->GetClassLoader() != nullptr)) {
      const DexFile& dex_file = klass->GetDexFile();
      if (&dex_file != last_dex_file_) {
        last_dex_file_ = &dex_file;
        DexCacheResolvedClasses resolved_classes(
            dex_file.GetLocation(),
            DexFileLoader::GetBaseLocation(dex_file.GetLocation()),
            dex_file.GetLocationChecksum(),
            dex_file.NumMethodIds());
        last_resolved_classes_ = result_->find(resolved_classes);
        if (last_resolved_classes_ == result_->end()) {
          last_resolved_classes_ = result_->insert(resolved_classes).first;
        }
      }
      bool added = last_resolved_classes_->AddClass(klass->GetDexTypeIndex());
      if (UNLIKELY(vlog_is_on_) && added) {
        const DexCacheResolvedClasses* resolved_classes = std::addressof(*last_resolved_classes_);
        if (last_extra_stats_ == extra_stats_.end() ||
            last_extra_stats_->first != resolved_classes) {
          last_extra_stats_ = extra_stats_.find(resolved_classes);
          if (last_extra_stats_ == extra_stats_.end()) {
            last_extra_stats_ =
                extra_stats_.emplace(resolved_classes, ExtraStats(dex_file.NumClassDefs())).first;
          }
        }
      }
    }
    return true;
  }

  void PrintStatistics() const {
    if (vlog_is_on_) {
      for (const DexCacheResolvedClasses& resolved_classes : *result_) {
        auto it = extra_stats_.find(std::addressof(resolved_classes));
        DCHECK(it != extra_stats_.end());
        const ExtraStats& extra_stats = it->second;
        LOG(INFO) << "Dex location " << resolved_classes.GetDexLocation()
                  << " has " << resolved_classes.GetClasses().size() << " / "
                  << extra_stats.number_of_class_defs_ << " resolved classes";
      }
    }
  }

 private:
  struct ExtraStats {
    explicit ExtraStats(uint32_t number_of_class_defs)
        : number_of_class_defs_(number_of_class_defs) {}
    uint32_t number_of_class_defs_;
  };

  std::set<DexCacheResolvedClasses>* result_;
  bool ignore_boot_classes_;
  std::set<DexCacheResolvedClasses>::iterator last_resolved_classes_;
  const DexFile* last_dex_file_;

  // Statistics.
  bool vlog_is_on_;
  std::map<const DexCacheResolvedClasses*, ExtraStats> extra_stats_;
  std::map<const DexCacheResolvedClasses*, ExtraStats>::iterator last_extra_stats_;
};

std::set<DexCacheResolvedClasses> ClassLinker::GetResolvedClasses(bool ignore_boot_classes) {
  ScopedTrace trace(__PRETTY_FUNCTION__);
  ScopedObjectAccess soa(Thread::Current());
  ScopedAssertNoThreadSuspension ants(__FUNCTION__);
  std::set<DexCacheResolvedClasses> ret;
  VLOG(class_linker) << "Collecting resolved classes";
  const uint64_t start_time = NanoTime();
  GetResolvedClassesVisitor visitor(&ret, ignore_boot_classes);
  VisitClasses(&visitor);
  if (VLOG_IS_ON(class_linker)) {
    visitor.PrintStatistics();
    LOG(INFO) << "Collecting class profile took " << PrettyDuration(NanoTime() - start_time);
  }
  return ret;
}

class ClassLinker::FindVirtualMethodHolderVisitor : public ClassVisitor {
 public:
  FindVirtualMethodHolderVisitor(const ArtMethod* method, PointerSize pointer_size)
      : method_(method),
        pointer_size_(pointer_size) {}

  bool operator()(ObjPtr<mirror::Class> klass) REQUIRES_SHARED(Locks::mutator_lock_) override {
    if (klass->GetVirtualMethodsSliceUnchecked(pointer_size_).Contains(method_)) {
      holder_ = klass;
    }
    // Return false to stop searching if holder_ is not null.
    return holder_ == nullptr;
  }

  ObjPtr<mirror::Class> holder_ = nullptr;
  const ArtMethod* const method_;
  const PointerSize pointer_size_;
};

ObjPtr<mirror::Class> ClassLinker::GetHoldingClassOfCopiedMethod(ArtMethod* method) {
  ScopedTrace trace(__FUNCTION__);  // Since this function is slow, have a trace to notify people.
  CHECK(method->IsCopied());
  FindVirtualMethodHolderVisitor visitor(method, image_pointer_size_);
  VisitClasses(&visitor);
  return visitor.holder_;
}

ObjPtr<mirror::IfTable> ClassLinker::AllocIfTable(Thread* self, size_t ifcount) {
  return ObjPtr<mirror::IfTable>::DownCast(ObjPtr<mirror::ObjectArray<mirror::Object>>(
      mirror::IfTable::Alloc(self,
                             GetClassRoot<mirror::ObjectArray<mirror::Object>>(this),
                             ifcount * mirror::IfTable::kMax)));
}

// Instantiate ClassLinker::ResolveMethod.
template ArtMethod* ClassLinker::ResolveMethod<ClassLinker::ResolveMode::kCheckICCEAndIAE>(
    uint32_t method_idx,
    Handle<mirror::DexCache> dex_cache,
    Handle<mirror::ClassLoader> class_loader,
    ArtMethod* referrer,
    InvokeType type);
template ArtMethod* ClassLinker::ResolveMethod<ClassLinker::ResolveMode::kNoChecks>(
    uint32_t method_idx,
    Handle<mirror::DexCache> dex_cache,
    Handle<mirror::ClassLoader> class_loader,
    ArtMethod* referrer,
    InvokeType type);

// Instantiate ClassLinker::AllocClass.
template ObjPtr<mirror::Class> ClassLinker::AllocClass</* kMovable= */ true>(
    Thread* self,
    ObjPtr<mirror::Class> java_lang_Class,
    uint32_t class_size);
template ObjPtr<mirror::Class> ClassLinker::AllocClass</* kMovable= */ false>(
    Thread* self,
    ObjPtr<mirror::Class> java_lang_Class,
    uint32_t class_size);

}  // namespace art
