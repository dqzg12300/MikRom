/*
 * Copyright (C) 2008 The Android Open Source Project
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

#include "java_lang_reflect_Method.h"

#include "nativehelper/jni_macros.h"

#include "art_method-inl.h"
#include "base/enums.h"
#include "class_linker-inl.h"
#include "class_linker.h"
#include "class_root.h"
#include "dex/dex_file_annotations.h"
#include "jni/jni_internal.h"
#include "mirror/class-inl.h"
#include "mirror/object-inl.h"
#include "mirror/object_array-alloc-inl.h"
#include "native_util.h"
#include "reflection.h"
#include "scoped_fast_native_object_access-inl.h"
#include "well_known_classes.h"

namespace art {

static jobject Method_getDefaultValue(JNIEnv* env, jobject javaMethod) {
  ScopedFastNativeObjectAccess soa(env);
  ArtMethod* method = ArtMethod::FromReflectedMethod(soa, javaMethod);
  if (!method->GetDeclaringClass()->IsAnnotation()) {
    return nullptr;
  }
  return soa.AddLocalReference<jobject>(annotations::GetAnnotationDefaultValue(method));
}

static jobjectArray Method_getExceptionTypes(JNIEnv* env, jobject javaMethod) {
  ScopedFastNativeObjectAccess soa(env);
  ArtMethod* method = ArtMethod::FromReflectedMethod(soa, javaMethod);
  if (method->GetDeclaringClass()->IsProxyClass()) {
    ObjPtr<mirror::Class> klass = method->GetDeclaringClass();
    int throws_index = -1;
    size_t i = 0;
    for (const auto& m : klass->GetDeclaredVirtualMethods(kRuntimePointerSize)) {
      if (&m == method) {
        throws_index = i;
        break;
      }
      ++i;
    }
    CHECK_NE(throws_index, -1);
    ObjPtr<mirror::ObjectArray<mirror::Class>> declared_exceptions =
        klass->GetProxyThrows()->Get(throws_index);
    return soa.AddLocalReference<jobjectArray>(declared_exceptions->Clone(soa.Self()));
  } else {
    ObjPtr<mirror::ObjectArray<mirror::Class>> result_array =
        annotations::GetExceptionTypesForMethod(method);
    if (result_array == nullptr) {
      // Return an empty array instead of a null pointer
      ObjPtr<mirror::Class> class_array_class = GetClassRoot<mirror::ObjectArray<mirror::Class>>();
      DCHECK(class_array_class != nullptr);
      ObjPtr<mirror::ObjectArray<mirror::Class>> empty_array =
          mirror::ObjectArray<mirror::Class>::Alloc(soa.Self(), class_array_class, 0);
      return soa.AddLocalReference<jobjectArray>(empty_array);
    } else {
      return soa.AddLocalReference<jobjectArray>(result_array);
    }
  }
}

static jobject Method_invoke(JNIEnv* env, jobject javaMethod, jobject javaReceiver,
                             jobjectArray javaArgs) {
  ScopedFastNativeObjectAccess soa(env);
  return InvokeMethod(soa, javaMethod, javaReceiver, javaArgs);
}

static JNINativeMethod gMethods[] = {
  FAST_NATIVE_METHOD(Method, getDefaultValue, "()Ljava/lang/Object;"),
  FAST_NATIVE_METHOD(Method, getExceptionTypes, "()[Ljava/lang/Class;"),
  FAST_NATIVE_METHOD(Method, invoke, "(Ljava/lang/Object;[Ljava/lang/Object;)Ljava/lang/Object;"),
};

void register_java_lang_reflect_Method(JNIEnv* env) {
  REGISTER_NATIVE_METHODS("java/lang/reflect/Method");
}

}  // namespace art
