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

// change mikrom
#include "art_method.h"

#include <cstddef>

#include "android-base/stringprintf.h"

#include "arch/context.h"
#include "art_method-inl.h"
#include "class_linker-inl.h"
#include "class_root.h"
#include "debugger.h"
#include "dex/class_accessor-inl.h"
#include "dex/descriptors_names.h"
#include "dex/dex_file-inl.h"
#include "dex/dex_file_exception_helpers.h"
#include "dex/dex_instruction.h"
#include "dex/signature-inl.h"
#include "entrypoints/runtime_asm_entrypoints.h"
#include "gc/accounting/card_table-inl.h"
#include "hidden_api.h"
#include "interpreter/interpreter.h"
#include "jit/jit.h"
#include "jit/jit_code_cache.h"
#include "jit/profiling_info.h"
#include "jni/jni_internal.h"
#include "mirror/class-inl.h"
#include "mirror/class_ext-inl.h"
#include "mirror/executable.h"
#include "mirror/object-inl.h"
#include "mirror/object_array-inl.h"
#include "mirror/string.h"
#include "oat_file-inl.h"
#include "quicken_info.h"
#include "runtime_callbacks.h"
#include "scoped_thread_state_change-inl.h"
#include "vdex_file.h"
//added code

#include <sys/syscall.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include "runtime.h"
#include <android/log.h>
#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <pthread.h>
#include <stdarg.h>
#include <stddef.h>
#include <stdlib.h>
#include <fstream>
#include <iostream>
#include <string>
#include <sys/mman.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <sys/uio.h>
#include <sys/un.h>
#include <time.h>
#include <unistd.h>
#include <map>

#define gettidv1() syscall(__NR_gettid)
#define LOG_TAG "ActivityThread"
#define ALOGI(...) __android_log_print(ANDROID_LOG_INFO, LOG_TAG, __VA_ARGS__)
//add end

namespace art {


using android::base::StringPrintf;

extern "C" void art_quick_invoke_stub(ArtMethod*, uint32_t*, uint32_t, Thread*, JValue*,
                                      const char*);
extern "C" void art_quick_invoke_static_stub(ArtMethod*, uint32_t*, uint32_t, Thread*, JValue*,
                                             const char*);

// Enforce that we he have the right index for runtime methods.
static_assert(ArtMethod::kRuntimeMethodDexMethodIndex == dex::kDexNoIndex,
              "Wrong runtime-method dex method index");

typedef struct{
    char packageName[128];
    char appName[128];
    char traceMethod[1024];
    char debugMethod[1024];
    bool isTuoke;
    bool isDeep;
    bool isInvokePrint;
    bool isRegisterNativePrint;
    bool isJNIMethodPrint;
    int  pid;
    bool init;
}PackageItem;

static PackageItem packageConfig;

static std::map<void*,size_t> dex_map;


const char* ArtMethod::GetTraceMethod(){
    return packageConfig.traceMethod;

}

const char* ArtMethod::GetDebugMethod(){

    return packageConfig.debugMethod;
}

bool ArtMethod::IsTuoke(){
    return packageConfig.isTuoke;
}

bool ArtMethod::IsDeep(){
    return packageConfig.isDeep;
}

bool ArtMethod::IsRegisterNativePrint(){
    return packageConfig.isRegisterNativePrint;
}

bool ArtMethod::IsJNIMethodPrint(){
    return packageConfig.isJNIMethodPrint;
}

bool ArtMethod::IsInvokePrint(){
    return packageConfig.isInvokePrint;
}

char* ArtMethod::GetPackageName(){
    return packageConfig.packageName;
}


void ArtMethod::SetPackageItem(JNIEnv* env,jobject config){
    LOG(ERROR)<< "mikrom ArtMethod SetPackageItem enter";
    //获取Java中的实例类ParamInfo
    jclass jcInfo = env->FindClass("cn/mik/PackageItem");
    //获取类中每一个变量的定义
    //boolean boolValue
    jfieldID jPackageName = env->GetFieldID(jcInfo, "packageName", "Ljava/lang/String;");
    jfieldID jAppName = env->GetFieldID(jcInfo, "appName", "Ljava/lang/String;");
    jfieldID jTraceMethod = env->GetFieldID(jcInfo, "traceMethod", "Ljava/lang/String;");
    jfieldID jSleepNativeMethod = env->GetFieldID(jcInfo, "sleepNativeMethod", "Ljava/lang/String;");
    jfieldID jIsTuoke = env->GetFieldID(jcInfo, "isTuoke", "Z");
    jfieldID jIsDeep = env->GetFieldID(jcInfo, "isDeep", "Z");

    jstring jstrPackageName = (jstring)env->GetObjectField(config, jPackageName);
    const char* pPackageName = (char*)env->GetStringUTFChars(jstrPackageName, 0);
    strcpy(packageConfig.packageName, pPackageName);

    jstring jstrAppName = (jstring)env->GetObjectField(config, jAppName);
    const char* pAppName = (char*)env->GetStringUTFChars(jstrAppName, 0);
    strcpy(packageConfig.appName, pAppName);

    jstring jstrTraceMethod = (jstring)env->GetObjectField(config, jTraceMethod);
    const char* pTraceMethod = (char*)env->GetStringUTFChars(jstrTraceMethod, 0);
    strcpy(packageConfig.traceMethod, pTraceMethod);

    jstring jstrSleepNativeMethod = (jstring)env->GetObjectField(config, jSleepNativeMethod);
    const char* pSleepNativeMethod = (char*)env->GetStringUTFChars(jstrSleepNativeMethod, 0);
    strcpy(packageConfig.debugMethod, pSleepNativeMethod);

    packageConfig.isTuoke = env->GetBooleanField(config, jIsTuoke);
    packageConfig.isDeep = env->GetBooleanField(config, jIsDeep);
    packageConfig.init=true;
    packageConfig.isRegisterNativePrint=env->GetBooleanField(config, env->GetFieldID(jcInfo, "isRegisterNativePrint", "Z"));
    packageConfig.isInvokePrint=env->GetBooleanField(config, env->GetFieldID(jcInfo, "isInvokePrint", "Z"));
    packageConfig.isJNIMethodPrint=env->GetBooleanField(config, env->GetFieldID(jcInfo, "isJNIMethodPrint", "Z"));
		std::ostringstream oss;
    oss << "mikrom SetPackageItem isDeep:"<<packageConfig.isDeep<<" debugMethod:"<<packageConfig.debugMethod<<
    " traceMethod:"<<packageConfig.traceMethod <<" isJNIMethodPrint:"<<packageConfig.isJNIMethodPrint<<" isRegisterNativePrint:"<<packageConfig.isRegisterNativePrint ;
    LOG(ERROR)<< oss.str();
}

ArtMethod* ArtMethod::GetCanonicalMethod(PointerSize pointer_size) {
  if (LIKELY(!IsDefault())) {
    return this;
  } else {
    ObjPtr<mirror::Class> declaring_class = GetDeclaringClass();
    DCHECK(declaring_class->IsInterface());
    ArtMethod* ret = declaring_class->FindInterfaceMethod(GetDexCache(),
                                                          GetDexMethodIndex(),
                                                          pointer_size);
    DCHECK(ret != nullptr);
    return ret;
  }
}

//add
uint8_t* codeitem_end(const uint8_t **pData)
{
    uint32_t num_of_list = DecodeUnsignedLeb128(pData);
    for (;num_of_list>0;num_of_list--) {
        int32_t num_of_handlers=DecodeSignedLeb128(pData);
        int num=num_of_handlers;
        if (num_of_handlers<=0) {
            num=-num_of_handlers;
        }
        for (; num > 0; num--) {
            DecodeUnsignedLeb128(pData);
            DecodeUnsignedLeb128(pData);
        }
        if (num_of_handlers<=0) {
            DecodeUnsignedLeb128(pData);
        }
    }
    return (uint8_t*)(*pData);
}



extern "C" char *base64_encode(char *str,long str_len,long* outlen){
	long len;
    char *res;
    int i,j;
    const char *base64_table="ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    if(str_len % 3 == 0)
        len=str_len/3*4;
    else
        len=(str_len/3+1)*4;

    res=(char*)malloc(sizeof(char)*(len+1));
    res[len]='\0';
    *outlen=len;
    for(i=0,j=0;i<len-2;j+=3,i+=4)
    {
        res[i]=base64_table[str[j]>>2];
        res[i+1]=base64_table[(str[j]&0x3)<<4 | (str[j+1]>>4)];
        res[i+2]=base64_table[(str[j+1]&0xf)<<2 | (str[j+2]>>6)];
        res[i+3]=base64_table[str[j+2]&0x3f];
    }

    switch(str_len % 3)
    {
        case 1:
            res[i-2]='=';
            res[i-1]='=';
            break;
        case 2:
            res[i-1]='=';
            break;
    }

    return res;
	}
//dumpdexfilebyCookie
extern "C" void dumpDexOver()  REQUIRES_SHARED(Locks::mutator_lock_) {
    if(dex_map.size()<=0){
    		LOG(ERROR) << "mikrom dumpDexOver dex_map.size()<=0";
        return;
    }
    char *dexfilepath=(char*)malloc(sizeof(char)*1000);
    LOG(ERROR) << "mikrom ArtMethod::dumpDexOver";
    int result=0;
    char* packageName=ArtMethod::GetPackageName();
    std::map<void*, size_t>::iterator iter;
    for(iter = dex_map.begin(); iter != dex_map.end(); iter++) {
        void* begin_=iter->first;
        size_t size_=iter->second;
        int size_int_=(int)size_;
        memset(dexfilepath,0,1000);
        sprintf(dexfilepath,"/sdcard/Android/data/%s/files/dump",packageName);
        mkdir(dexfilepath,0777);
        memset(dexfilepath,0,1000);
        sprintf(dexfilepath,"/sdcard/Android/data/%s/files/dump/%d_dexfile_repair.dex",packageName,size_int_);
        int dexfilefp=open(dexfilepath,O_RDONLY,0666);
        if(dexfilefp>0){
          close(dexfilefp);
          dexfilefp=0;

        }else{
          int fp=open(dexfilepath,O_CREAT|O_APPEND|O_RDWR,0666);
          if(fp>0)
          {
              result=write(fp,(void*)begin_,size_);
              if(result<0)
              {
                  LOG(ERROR) << "mikrom ArtMethod::dumpDexOver,open dexfilepath error";
              }
              fsync(fp);
              close(fp);
              memset(dexfilepath,0,1000);
          }
        }
    }
    if(dexfilepath!=nullptr)
    {
        free(dexfilepath);
        dexfilepath=nullptr;
    }
}
	//在函数即将调用解释器执行前进行dump。
extern "C" void dumpdexfilebyExecute(ArtMethod* artmethod)  REQUIRES_SHARED(Locks::mutator_lock_) {
    if(artmethod==nullptr){
        LOG(ERROR)<< "mikrom ArtMethod::dumpdexfilebyExecute artmethod is null";
        return;
    }
    char *dexfilepath=(char*)malloc(sizeof(char)*1000);
    if(dexfilepath==nullptr)
    {
    		std::ostringstream oss;
    		oss<<"mikrom ArtMethod::dumpdexfilebyArtMethod,methodname:"<<artmethod->PrettyMethod().c_str()<<"malloc 1000 byte failed";
        LOG(ERROR)<< oss.str();
        return;
    }
    int result=0;
    char* packageName=ArtMethod::GetPackageName();
    const DexFile* dex_file = artmethod->GetDexFile();
    if(dex_file==nullptr){
        LOG(ERROR)<< "mikrom ArtMethod::dumpdexfilebyExecute dex_file is null";
        return;
    }
    const uint8_t* begin_=dex_file->Begin();  // Start of data.
    size_t size_=dex_file->Size();  // Length of data.

    memset(dexfilepath,0,1000);
    int size_int_=(int)size_;

    memset(dexfilepath,0,1000);
    sprintf(dexfilepath,"/sdcard/Android/data/%s/files/dump",packageName);
    mkdir(dexfilepath,0777);
    memset(dexfilepath,0,1000);
    sprintf(dexfilepath,"/sdcard/Android/data/%s/files/dump/%d_dexfile_execute.dex",packageName,size_int_);
    int dexfilefp=open(dexfilepath,O_RDONLY,0666);
    if(dexfilefp>0){
      close(dexfilefp);
      dexfilefp=0;

      }else{
              int fp=open(dexfilepath,O_CREAT|O_APPEND|O_RDWR,0666);
              if(fp>0)
              {
                  result=write(fp,(void*)begin_,size_);
                  if(result<0)
                  {
                    LOG(ERROR) << "mikrom ArtMethod::dumpdexfilebyArtMethod,open dexfilepath error";
                  }
                  fsync(fp);
                  close(fp);
                  memset(dexfilepath,0,1000);
                  sprintf(dexfilepath,"/sdcard/Android/data/%s/files/dump/%d_classlist_execute.txt",packageName,size_int_);
                  int classlistfile=open(dexfilepath,O_CREAT|O_APPEND|O_RDWR,0666);
                  if(classlistfile>0)
                  {
                        for (size_t ii= 0; ii< dex_file->NumClassDefs(); ++ii)
                        {
                            const dex::ClassDef& class_def = dex_file->GetClassDef(ii);
                            const char* descriptor = dex_file->GetClassDescriptor(class_def);
                            result=write(classlistfile,(void*)descriptor,strlen(descriptor));
                            if(result<0)
                            {
                                LOG(ERROR) << "mikrom ArtMethod::dumpdexfilebyExecute,write classlistfile file error";
                            }
                            const char* temp="\n";
                            result=write(classlistfile,(void*)temp,1);
                            if(result<0)
                            {
                                LOG(ERROR) << "mikrom ArtMethod::dumpdexfilebyExecute,write classlistfile file error";
                            }
                            fsync(classlistfile);
                            close(classlistfile);

                        }
                  }
              }
      }
      if(dexfilepath!=nullptr)
      {
          free(dexfilepath);
          dexfilepath=nullptr;
      }
}

//主动调用函数的dump处理
extern "C" void dumpArtMethod(ArtMethod* artmethod)  REQUIRES_SHARED(Locks::mutator_lock_) {
            //LOG(ERROR) << "mikrom ArtMethod::dumpArtMethod "<<artmethod->PrettyMethod().c_str();
			char *dexfilepath=(char*)malloc(sizeof(char)*1000);
			if(dexfilepath==nullptr)
			{
				std::ostringstream oss;
				oss<<"mikrom ArtMethod::dumpArtMethodinvoked,methodname:"<<artmethod->PrettyMethod().c_str()<<"malloc 1000 byte failed";
				LOG(ERROR) << oss.str();
				return;
			}
			int result=0;
			char* packageName=ArtMethod::GetPackageName();
				const DexFile* dex_file = artmethod->GetDexFile();
				const uint8_t* begin_=dex_file->Begin();  // Start of data.
				size_t size_=dex_file->Size();  // Length of data.

				memset(dexfilepath,0,1000);
				int size_int_=(int)size_;

				memset(dexfilepath,0,1000);
				sprintf(dexfilepath,"/sdcard/Android/data/%s/files/dump",packageName);
				mkdir(dexfilepath,0777);
				memset(dexfilepath,0,1000);
				const char* deepstr="";
				if(ArtMethod::IsDeep()){
					 deepstr="_deep";
				}
				sprintf(dexfilepath,"/sdcard/Android/data/%s/files/dump/%d%s_dexfile.dex",packageName,size_int_,deepstr);
				int dexfilefp=open(dexfilepath,O_RDONLY,0666);
				if(dexfilefp>0){
					close(dexfilefp);
					dexfilefp=0;
				}else{
					LOG(ERROR) << "mikrom ArtMethod::dumpdexfilebyArtMethod save dex_map";
					dex_map.insert(std::pair<void*,size_t>((void*)begin_,size_));
					int fp=open(dexfilepath,O_CREAT|O_APPEND|O_RDWR,0666);
					if(fp>0)
					{
							result=write(fp,(void*)begin_,size_);
							if(result<0)
							{
								 LOG(ERROR) << "mikrom ArtMethod::dumpdexfilebyArtMethod,open dexfilepath file error";
							}
							fsync(fp);
							close(fp);
							memset(dexfilepath,0,1000);
							sprintf(dexfilepath,"/sdcard/Android/data/%s/files/dump/%d%s_classlist.txt",packageName,size_int_,deepstr);
							int classlistfile=open(dexfilepath,O_CREAT|O_APPEND|O_RDWR,0666);
							if(classlistfile>0)
							{
										for (size_t ii= 0; ii< dex_file->NumClassDefs(); ++ii)
										{
												const dex::ClassDef& class_def = dex_file->GetClassDef(ii);
												const char* descriptor = dex_file->GetClassDescriptor(class_def);
												result=write(classlistfile,(void*)descriptor,strlen(descriptor));
												if(result<0)
												{
														LOG(ERROR) << "mikrom ArtMethod::dumpdexfilebyArtMethod,write classlistfile file error";

														}
												const char* temp="\n";
												result=write(classlistfile,(void*)temp,1);
												if(result<0)
												{
														LOG(ERROR) << "mikrom ArtMethod::dumpdexfilebyArtMethod,write classlistfile file error";

												}
										}
										fsync(classlistfile);
										close(classlistfile);
							}
					}
				}

				const dex::CodeItem* code_item = artmethod->GetCodeItem();
				const DexFile* dex_=artmethod->GetDexFile();
				CodeItemDataAccessor accessor(*dex_, dex_->GetCodeItem(artmethod->GetCodeItemOffset()));
				if (LIKELY(code_item != nullptr))
				{
							//LOG(ERROR) << "mikrom dumpArtMethodinvoked,methodname:"<<artmethod->PrettyMethod().c_str()<<" write bin";
							int code_item_len = 0;
							uint8_t *item=(uint8_t *) code_item;
							if (accessor.TriesSize()>0) {
									const uint8_t *handler_data = accessor.GetCatchHandlerData();
									uint8_t * tail = codeitem_end(&handler_data);
									code_item_len = (int)(tail - item);
							}else{
									code_item_len = 16+accessor.InsnsSizeInCodeUnits()*2;
							}
							memset(dexfilepath,0,1000);
							int size_int=(int)dex_file->Size();
							uint32_t method_idx=artmethod->GetDexMethodIndex();
							sprintf(dexfilepath,"/sdcard/Android/data/%s/files/dump/%d%s_ins_%d.bin",packageName,size_int,deepstr,(int)gettidv1());
							int fp2=open(dexfilepath,O_CREAT|O_APPEND|O_RDWR,0666);
							if(fp2>0){
									lseek(fp2,0,SEEK_END);
									memset(dexfilepath,0,1000);
									int offset=(int)(item - begin_);
									sprintf(dexfilepath,"{name:%s,method_idx:%d,offset:%d,code_item_len:%d,ins:",artmethod->PrettyMethod().c_str(),method_idx,offset,code_item_len);
									int contentlength=0;
									while(dexfilepath[contentlength]!=0) contentlength++;
									result=write(fp2,(void*)dexfilepath,contentlength);
									if(result<0)
									{
											LOG(ERROR) << "mikrom ArtMethod::dumpdexfilebyArtMethod,write ins file error";
									}
									long outlen=0;
									char* base64result=base64_encode((char*)item,(long)code_item_len,&outlen);
									result=write(fp2,base64result,outlen);
									if(result<0){
											LOG(ERROR) << "mikrom ArtMethod::dumpdexfilebyArtMethod,write ins file error";
									}
									result=write(fp2,"};",2);
									if(result<0){
										 LOG(ERROR) << "mikrom ArtMethod::dumpdexfilebyArtMethod,write ins file error";
									}
									fsync(fp2);
									close(fp2);
									if(base64result!=nullptr){
											free(base64result);
											base64result=nullptr;
									}
							}
				}
			if(dexfilepath!=nullptr)
			{
				free(dexfilepath);
				dexfilepath=nullptr;
			}
			//LOG(ERROR) << "mikrom ArtMethod::dumpArtMethod over "<<artmethod->PrettyMethod().c_str();
}
extern "C" void fartextInvoke(ArtMethod* artmethod)  REQUIRES_SHARED(Locks::mutator_lock_) {
    if(artmethod->IsNative()||artmethod->IsAbstract()){
        return;
    }
	JValue result;
	Thread *self=Thread::Current();
	uint32_t temp[100]={0};
	uint32_t* args=temp;
	uint32_t args_size = (uint32_t)ArtMethod::NumArgRegisters(artmethod->GetShorty());
    if (!artmethod->IsStatic()) {
      args_size += 1;
    }
    result.SetI(111111);
	artmethod->Invoke(self, args, args_size, &result,artmethod->GetShorty());
}




//addend

ArtMethod* ArtMethod::GetNonObsoleteMethod() {
  if (LIKELY(!IsObsolete())) {
    return this;
  }
  DCHECK_EQ(kRuntimePointerSize, Runtime::Current()->GetClassLinker()->GetImagePointerSize());
  if (IsDirect()) {
    return &GetDeclaringClass()->GetDirectMethodsSlice(kRuntimePointerSize)[GetMethodIndex()];
  } else {
    return GetDeclaringClass()->GetVTableEntry(GetMethodIndex(), kRuntimePointerSize);
  }
}

ArtMethod* ArtMethod::GetSingleImplementation(PointerSize pointer_size) {
  if (!IsAbstract()) {
    // A non-abstract's single implementation is itself.
    return this;
  }
  return reinterpret_cast<ArtMethod*>(GetDataPtrSize(pointer_size));
}

ArtMethod* ArtMethod::FromReflectedMethod(const ScopedObjectAccessAlreadyRunnable& soa,
                                          jobject jlr_method) {
  ObjPtr<mirror::Executable> executable = soa.Decode<mirror::Executable>(jlr_method);
  DCHECK(executable != nullptr);
  return executable->GetArtMethod();
}

ObjPtr<mirror::DexCache> ArtMethod::GetObsoleteDexCache() {
  DCHECK(!Runtime::Current()->IsAotCompiler()) << PrettyMethod();
  DCHECK(IsObsolete());
  ObjPtr<mirror::ClassExt> ext(GetDeclaringClass()->GetExtData());
  CHECK(!ext.IsNull());
  ObjPtr<mirror::PointerArray> obsolete_methods(ext->GetObsoleteMethods());
  CHECK(!obsolete_methods.IsNull());
  DCHECK(ext->GetObsoleteDexCaches() != nullptr);
  int32_t len = obsolete_methods->GetLength();
  DCHECK_EQ(len, ext->GetObsoleteDexCaches()->GetLength());
  // Using kRuntimePointerSize (instead of using the image's pointer size) is fine since images
  // should never have obsolete methods in them so they should always be the same.
  PointerSize pointer_size = kRuntimePointerSize;
  DCHECK_EQ(kRuntimePointerSize, Runtime::Current()->GetClassLinker()->GetImagePointerSize());
  for (int32_t i = 0; i < len; i++) {
    if (this == obsolete_methods->GetElementPtrSize<ArtMethod*>(i, pointer_size)) {
      return ext->GetObsoleteDexCaches()->Get(i);
    }
  }
  LOG(FATAL) << "This method does not appear in the obsolete map of its class!";
  UNREACHABLE();
}

uint16_t ArtMethod::FindObsoleteDexClassDefIndex() {
  DCHECK(!Runtime::Current()->IsAotCompiler()) << PrettyMethod();
  DCHECK(IsObsolete());
  const DexFile* dex_file = GetDexFile();
  const dex::TypeIndex declaring_class_type = dex_file->GetMethodId(GetDexMethodIndex()).class_idx_;
  const dex::ClassDef* class_def = dex_file->FindClassDef(declaring_class_type);
  CHECK(class_def != nullptr);
  return dex_file->GetIndexForClassDef(*class_def);
}

void ArtMethod::ThrowInvocationTimeError() {
  DCHECK(!IsInvokable());
  // NOTE: IsDefaultConflicting must be first since the actual method might or might not be abstract
  //       due to the way we select it.
  if (IsDefaultConflicting()) {
    ThrowIncompatibleClassChangeErrorForMethodConflict(this);
  } else {
    DCHECK(IsAbstract());
    ThrowAbstractMethodError(this);
  }
}

InvokeType ArtMethod::GetInvokeType() {
  // TODO: kSuper?
  if (IsStatic()) {
    return kStatic;
  } else if (GetDeclaringClass()->IsInterface()) {
    return kInterface;
  } else if (IsDirect()) {
    return kDirect;
  } else if (IsPolymorphicSignature()) {
    return kPolymorphic;
  } else {
    return kVirtual;
  }
}

size_t ArtMethod::NumArgRegisters(const char* shorty) {
  CHECK_NE(shorty[0], '\0');
  uint32_t num_registers = 0;
  for (const char* s = shorty + 1; *s != '\0'; ++s) {
    if (*s == 'D' || *s == 'J') {
      num_registers += 2;
    } else {
      num_registers += 1;
    }
  }
  return num_registers;
}

bool ArtMethod::HasSameNameAndSignature(ArtMethod* other) {
  ScopedAssertNoThreadSuspension ants("HasSameNameAndSignature");
  const DexFile* dex_file = GetDexFile();
  const dex::MethodId& mid = dex_file->GetMethodId(GetDexMethodIndex());
  if (GetDexCache() == other->GetDexCache()) {
    const dex::MethodId& mid2 = dex_file->GetMethodId(other->GetDexMethodIndex());
    return mid.name_idx_ == mid2.name_idx_ && mid.proto_idx_ == mid2.proto_idx_;
  }
  const DexFile* dex_file2 = other->GetDexFile();
  const dex::MethodId& mid2 = dex_file2->GetMethodId(other->GetDexMethodIndex());
  if (!DexFile::StringEquals(dex_file, mid.name_idx_, dex_file2, mid2.name_idx_)) {
    return false;  // Name mismatch.
  }
  return dex_file->GetMethodSignature(mid) == dex_file2->GetMethodSignature(mid2);
}

ArtMethod* ArtMethod::FindOverriddenMethod(PointerSize pointer_size) {
  if (IsStatic()) {
    return nullptr;
  }
  ObjPtr<mirror::Class> declaring_class = GetDeclaringClass();
  ObjPtr<mirror::Class> super_class = declaring_class->GetSuperClass();
  uint16_t method_index = GetMethodIndex();
  ArtMethod* result = nullptr;
  // Did this method override a super class method? If so load the result from the super class'
  // vtable
  if (super_class->HasVTable() && method_index < super_class->GetVTableLength()) {
    result = super_class->GetVTableEntry(method_index, pointer_size);
  } else {
    // Method didn't override superclass method so search interfaces
    if (IsProxyMethod()) {
      result = GetInterfaceMethodIfProxy(pointer_size);
      DCHECK(result != nullptr);
    } else {
      ObjPtr<mirror::IfTable> iftable = GetDeclaringClass()->GetIfTable();
      for (size_t i = 0; i < iftable->Count() && result == nullptr; i++) {
        ObjPtr<mirror::Class> interface = iftable->GetInterface(i);
        for (ArtMethod& interface_method : interface->GetVirtualMethods(pointer_size)) {
          if (HasSameNameAndSignature(interface_method.GetInterfaceMethodIfProxy(pointer_size))) {
            result = &interface_method;
            break;
          }
        }
      }
    }
  }
  DCHECK(result == nullptr ||
         GetInterfaceMethodIfProxy(pointer_size)->HasSameNameAndSignature(
             result->GetInterfaceMethodIfProxy(pointer_size)));
  return result;
}

uint32_t ArtMethod::FindDexMethodIndexInOtherDexFile(const DexFile& other_dexfile,
                                                     uint32_t name_and_signature_idx) {
  const DexFile* dexfile = GetDexFile();
  const uint32_t dex_method_idx = GetDexMethodIndex();
  const dex::MethodId& mid = dexfile->GetMethodId(dex_method_idx);
  const dex::MethodId& name_and_sig_mid = other_dexfile.GetMethodId(name_and_signature_idx);
  DCHECK_STREQ(dexfile->GetMethodName(mid), other_dexfile.GetMethodName(name_and_sig_mid));
  DCHECK_EQ(dexfile->GetMethodSignature(mid), other_dexfile.GetMethodSignature(name_and_sig_mid));
  if (dexfile == &other_dexfile) {
    return dex_method_idx;
  }
  const char* mid_declaring_class_descriptor = dexfile->StringByTypeIdx(mid.class_idx_);
  const dex::TypeId* other_type_id = other_dexfile.FindTypeId(mid_declaring_class_descriptor);
  if (other_type_id != nullptr) {
    const dex::MethodId* other_mid = other_dexfile.FindMethodId(
        *other_type_id, other_dexfile.GetStringId(name_and_sig_mid.name_idx_),
        other_dexfile.GetProtoId(name_and_sig_mid.proto_idx_));
    if (other_mid != nullptr) {
      return other_dexfile.GetIndexForMethodId(*other_mid);
    }
  }
  return dex::kDexNoIndex;
}

uint32_t ArtMethod::FindCatchBlock(Handle<mirror::Class> exception_type,
                                   uint32_t dex_pc, bool* has_no_move_exception) {
  // Set aside the exception while we resolve its type.
  Thread* self = Thread::Current();
  StackHandleScope<1> hs(self);
  Handle<mirror::Throwable> exception(hs.NewHandle(self->GetException()));
  self->ClearException();
  // Default to handler not found.
  uint32_t found_dex_pc = dex::kDexNoIndex;
  // Iterate over the catch handlers associated with dex_pc.
  CodeItemDataAccessor accessor(DexInstructionData());
  for (CatchHandlerIterator it(accessor, dex_pc); it.HasNext(); it.Next()) {
    dex::TypeIndex iter_type_idx = it.GetHandlerTypeIndex();
    // Catch all case
    if (!iter_type_idx.IsValid()) {
      found_dex_pc = it.GetHandlerAddress();
      break;
    }
    // Does this catch exception type apply?
    ObjPtr<mirror::Class> iter_exception_type = ResolveClassFromTypeIndex(iter_type_idx);
    if (UNLIKELY(iter_exception_type == nullptr)) {
      // Now have a NoClassDefFoundError as exception. Ignore in case the exception class was
      // removed by a pro-guard like tool.
      // Note: this is not RI behavior. RI would have failed when loading the class.
      self->ClearException();
      // Delete any long jump context as this routine is called during a stack walk which will
      // release its in use context at the end.
      delete self->GetLongJumpContext();
      LOG(WARNING) << "Unresolved exception class when finding catch block: "
        << DescriptorToDot(GetTypeDescriptorFromTypeIdx(iter_type_idx));
    } else if (iter_exception_type->IsAssignableFrom(exception_type.Get())) {
      found_dex_pc = it.GetHandlerAddress();
      break;
    }
  }
  if (found_dex_pc != dex::kDexNoIndex) {
    const Instruction& first_catch_instr = accessor.InstructionAt(found_dex_pc);
    *has_no_move_exception = (first_catch_instr.Opcode() != Instruction::MOVE_EXCEPTION);
  }
  // Put the exception back.
  if (exception != nullptr) {
    self->SetException(exception.Get());
  }
  return found_dex_pc;
}

void ArtMethod::Invoke(Thread* self, uint32_t* args, uint32_t args_size, JValue* result,
                       const char* shorty) {
  if (UNLIKELY(__builtin_frame_address(0) < self->GetStackEnd())) {
    ThrowStackOverflowError(self);
    return;
  }
  //add
		if ((result!=nullptr && result->GetI()==111111)){
			if(!ArtMethod::IsDeep()){
					dumpArtMethod(this);
					return;
			}

		}
		//else{
		//	if(ArtMethod::IsInvokePrint()){
		//				std::ostringstream oss;
		//				oss<<"mikrom art invoke "<<this->PrettyMethod().c_str();
		//				LOG(ERROR) <<oss.str();
		//		}
		//}
	//add end
  if (kIsDebugBuild) {
    self->AssertThreadSuspensionIsAllowable();
    CHECK_EQ(kRunnable, self->GetState());
    CHECK_STREQ(GetInterfaceMethodIfProxy(kRuntimePointerSize)->GetShorty(), shorty);
  }

  // Push a transition back into managed code onto the linked list in thread.
  ManagedStack fragment;
  self->PushManagedStackFragment(&fragment);

  Runtime* runtime = Runtime::Current();
  // Call the invoke stub, passing everything as arguments.
  // If the runtime is not yet started or it is required by the debugger, then perform the
  // Invocation by the interpreter, explicitly forcing interpretation over JIT to prevent
  // cycling around the various JIT/Interpreter methods that handle method invocation.

  //add

  if ((result!=nullptr && result->GetI()==111111)&&!IsNative()){
		const dex::CodeItem* code_item =this->GetCodeItem();
		if(LIKELY(code_item!=nullptr)){
				if (IsStatic()) {
					art::interpreter::EnterInterpreterFromInvoke(
													self, this, nullptr, args, result, /*stay_in_interpreter=*/ true);
				}else{
					art::interpreter::EnterInterpreterFromInvoke(
										self, this, nullptr, args + 1, result, /*stay_in_interpreter=*/ true);
				}
				self->PopManagedStackFragment(fragment);
		}
		return;
  }
  //add end

  if (UNLIKELY(!runtime->IsStarted() ||
               (self->IsForceInterpreter() && !IsNative() && !IsProxyMethod() && IsInvokable()) ||
               Dbg::IsForcedInterpreterNeededForCalling(self, this))) {

    if (IsStatic()) {
      art::interpreter::EnterInterpreterFromInvoke(
          self, this, nullptr, args, result, /*stay_in_interpreter=*/ true);
    } else {
      mirror::Object* receiver =
          reinterpret_cast<StackReference<mirror::Object>*>(&args[0])->AsMirrorPtr();
      art::interpreter::EnterInterpreterFromInvoke(
          self, this, receiver, args + 1, result, /*stay_in_interpreter=*/ true);
    }
  } else {
  	if (result!=nullptr && result->GetI()==111111){
  			std::ostringstream oss;
				oss<< "mikrom artMethod::Invoke return Native Method "<<this->PrettyMethod().c_str();
				LOG(ERROR) <<oss.str();
				return;
		}
    DCHECK_EQ(runtime->GetClassLinker()->GetImagePointerSize(), kRuntimePointerSize);
    constexpr bool kLogInvocationStartAndReturn = false;
    bool have_quick_code = GetEntryPointFromQuickCompiledCode() != nullptr;
    if (LIKELY(have_quick_code)) {
      if (kLogInvocationStartAndReturn) {
        LOG(INFO) << StringPrintf(
            "Invoking '%s' quick code=%p static=%d", PrettyMethod().c_str(),
            GetEntryPointFromQuickCompiledCode(), static_cast<int>(IsStatic() ? 1 : 0));
      }

      // Ensure that we won't be accidentally calling quick compiled code when -Xint.
      if (kIsDebugBuild && runtime->GetInstrumentation()->IsForcedInterpretOnly()) {
        CHECK(!runtime->UseJitCompilation());
        const void* oat_quick_code =
            (IsNative() || !IsInvokable() || IsProxyMethod() || IsObsolete())
            ? nullptr
            : GetOatMethodQuickCode(runtime->GetClassLinker()->GetImagePointerSize());
        CHECK(oat_quick_code == nullptr || oat_quick_code != GetEntryPointFromQuickCompiledCode())
            << "Don't call compiled code when -Xint " << PrettyMethod();
      }
      if (!IsStatic()) {
        (*art_quick_invoke_stub)(this, args, args_size, self, result, shorty);
      } else {
        (*art_quick_invoke_static_stub)(this, args, args_size, self, result, shorty);
      }
      if (UNLIKELY(self->GetException() == Thread::GetDeoptimizationException())) {
        // Unusual case where we were running generated code and an
        // exception was thrown to force the activations to be removed from the
        // stack. Continue execution in the interpreter.
        self->DeoptimizeWithDeoptimizationException(result);
      }
      if (kLogInvocationStartAndReturn) {
        LOG(INFO) << StringPrintf("Returned '%s' quick code=%p", PrettyMethod().c_str(),
                                  GetEntryPointFromQuickCompiledCode());
      }
    } else {
      LOG(INFO) << "Not invoking '" << PrettyMethod() << "' code=null";
      if (result != nullptr) {
        result->SetJ(0);
      }
    }
  }

  // Pop transition.
  self->PopManagedStackFragment(fragment);
}

const void* ArtMethod::RegisterNative(const void* native_method) {
  CHECK(IsNative()) << PrettyMethod();
  CHECK(native_method != nullptr) << PrettyMethod();
  void* new_native_method = nullptr;
  Runtime::Current()->GetRuntimeCallbacks()->RegisterNativeMethod(this,
                                                                  native_method,
                                                                  /*out*/&new_native_method);
  if(ArtMethod::IsRegisterNativePrint()){
        std::ostringstream oss;
        oss << "mikrom RomPrint RegisterNative name:"<<this->PrettyMethod().c_str()<<" native_ptr:"<<native_method<<" method_idx:"<<this->method_index_;
    		LOG(ERROR)<<oss.str();
    }
  SetEntryPointFromJni(new_native_method);
  return new_native_method;
}

void ArtMethod::UnregisterNative() {
  CHECK(IsNative()) << PrettyMethod();
  // restore stub to lookup native pointer via dlsym
  SetEntryPointFromJni(GetJniDlsymLookupStub());
}

bool ArtMethod::IsOverridableByDefaultMethod() {
  return GetDeclaringClass()->IsInterface();
}

bool ArtMethod::IsPolymorphicSignature() {
  // Methods with a polymorphic signature have constraints that they
  // are native and varargs and belong to either MethodHandle or VarHandle.
  if (!IsNative() || !IsVarargs()) {
    return false;
  }
  ObjPtr<mirror::ObjectArray<mirror::Class>> class_roots =
      Runtime::Current()->GetClassLinker()->GetClassRoots();
  ObjPtr<mirror::Class> cls = GetDeclaringClass();
  return (cls == GetClassRoot<mirror::MethodHandle>(class_roots) ||
          cls == GetClassRoot<mirror::VarHandle>(class_roots));
}

static uint32_t GetOatMethodIndexFromMethodIndex(const DexFile& dex_file,
                                                 uint16_t class_def_idx,
                                                 uint32_t method_idx) {
  ClassAccessor accessor(dex_file, class_def_idx);
  uint32_t class_def_method_index = 0u;
  for (const ClassAccessor::Method& method : accessor.GetMethods()) {
    if (method.GetIndex() == method_idx) {
      return class_def_method_index;
    }
    class_def_method_index++;
  }
  LOG(FATAL) << "Failed to find method index " << method_idx << " in " << dex_file.GetLocation();
  UNREACHABLE();
}

// We use the method's DexFile and declaring class name to find the OatMethod for an obsolete
// method.  This is extremely slow but we need it if we want to be able to have obsolete native
// methods since we need this to find the size of its stack frames.
//
// NB We could (potentially) do this differently and rely on the way the transformation is applied
// in order to use the entrypoint to find this information. However, for debugging reasons (most
// notably making sure that new invokes of obsolete methods fail) we choose to instead get the data
// directly from the dex file.
static const OatFile::OatMethod FindOatMethodFromDexFileFor(ArtMethod* method, bool* found)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  DCHECK(method->IsObsolete() && method->IsNative());
  const DexFile* dex_file = method->GetDexFile();

  // recreate the class_def_index from the descriptor.
  std::string descriptor_storage;
  const dex::TypeId* declaring_class_type_id =
      dex_file->FindTypeId(method->GetDeclaringClass()->GetDescriptor(&descriptor_storage));
  CHECK(declaring_class_type_id != nullptr);
  dex::TypeIndex declaring_class_type_index = dex_file->GetIndexForTypeId(*declaring_class_type_id);
  const dex::ClassDef* declaring_class_type_def =
      dex_file->FindClassDef(declaring_class_type_index);
  CHECK(declaring_class_type_def != nullptr);
  uint16_t declaring_class_def_index = dex_file->GetIndexForClassDef(*declaring_class_type_def);

  size_t oat_method_index = GetOatMethodIndexFromMethodIndex(*dex_file,
                                                             declaring_class_def_index,
                                                             method->GetDexMethodIndex());

  OatFile::OatClass oat_class = OatFile::FindOatClass(*dex_file,
                                                      declaring_class_def_index,
                                                      found);
  if (!(*found)) {
    return OatFile::OatMethod::Invalid();
  }
  return oat_class.GetOatMethod(oat_method_index);
}

static const OatFile::OatMethod FindOatMethodFor(ArtMethod* method,
                                                 PointerSize pointer_size,
                                                 bool* found)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  if (UNLIKELY(method->IsObsolete())) {
    // We shouldn't be calling this with obsolete methods except for native obsolete methods for
    // which we need to use the oat method to figure out how large the quick frame is.
    DCHECK(method->IsNative()) << "We should only be finding the OatMethod of obsolete methods in "
                               << "order to allow stack walking. Other obsolete methods should "
                               << "never need to access this information.";
    DCHECK_EQ(pointer_size, kRuntimePointerSize) << "Obsolete method in compiler!";
    return FindOatMethodFromDexFileFor(method, found);
  }
  // Although we overwrite the trampoline of non-static methods, we may get here via the resolution
  // method for direct methods (or virtual methods made direct).
  ObjPtr<mirror::Class> declaring_class = method->GetDeclaringClass();
  size_t oat_method_index;
  if (method->IsStatic() || method->IsDirect()) {
    // Simple case where the oat method index was stashed at load time.
    oat_method_index = method->GetMethodIndex();
  } else {
    // Compute the oat_method_index by search for its position in the declared virtual methods.
    oat_method_index = declaring_class->NumDirectMethods();
    bool found_virtual = false;
    for (ArtMethod& art_method : declaring_class->GetVirtualMethods(pointer_size)) {
      // Check method index instead of identity in case of duplicate method definitions.
      if (method->GetDexMethodIndex() == art_method.GetDexMethodIndex()) {
        found_virtual = true;
        break;
      }
      oat_method_index++;
    }
    CHECK(found_virtual) << "Didn't find oat method index for virtual method: "
                         << method->PrettyMethod();
  }
  DCHECK_EQ(oat_method_index,
            GetOatMethodIndexFromMethodIndex(declaring_class->GetDexFile(),
                                             method->GetDeclaringClass()->GetDexClassDefIndex(),
                                             method->GetDexMethodIndex()));
  OatFile::OatClass oat_class = OatFile::FindOatClass(declaring_class->GetDexFile(),
                                                      declaring_class->GetDexClassDefIndex(),
                                                      found);
  if (!(*found)) {
    return OatFile::OatMethod::Invalid();
  }
  return oat_class.GetOatMethod(oat_method_index);
}

bool ArtMethod::EqualParameters(Handle<mirror::ObjectArray<mirror::Class>> params) {
  const DexFile* dex_file = GetDexFile();
  const auto& method_id = dex_file->GetMethodId(GetDexMethodIndex());
  const auto& proto_id = dex_file->GetMethodPrototype(method_id);
  const dex::TypeList* proto_params = dex_file->GetProtoParameters(proto_id);
  auto count = proto_params != nullptr ? proto_params->Size() : 0u;
  auto param_len = params != nullptr ? params->GetLength() : 0u;
  if (param_len != count) {
    return false;
  }
  auto* cl = Runtime::Current()->GetClassLinker();
  for (size_t i = 0; i < count; ++i) {
    dex::TypeIndex type_idx = proto_params->GetTypeItem(i).type_idx_;
    ObjPtr<mirror::Class> type = cl->ResolveType(type_idx, this);
    if (type == nullptr) {
      Thread::Current()->AssertPendingException();
      return false;
    }
    if (type != params->GetWithoutChecks(i)) {
      return false;
    }
  }
  return true;
}

ArrayRef<const uint8_t> ArtMethod::GetQuickenedInfo() {
  const DexFile& dex_file = *GetDexFile();
  const OatDexFile* oat_dex_file = dex_file.GetOatDexFile();
  if (oat_dex_file == nullptr) {
    return ArrayRef<const uint8_t>();
  }
  return oat_dex_file->GetQuickenedInfoOf(dex_file, GetDexMethodIndex());
}

uint16_t ArtMethod::GetIndexFromQuickening(uint32_t dex_pc) {
  ArrayRef<const uint8_t> data = GetQuickenedInfo();
  if (data.empty()) {
    return DexFile::kDexNoIndex16;
  }
  QuickenInfoTable table(data);
  uint32_t quicken_index = 0;
  for (const DexInstructionPcPair& pair : DexInstructions()) {
    if (pair.DexPc() == dex_pc) {
      return table.GetData(quicken_index);
    }
    if (QuickenInfoTable::NeedsIndexForInstruction(&pair.Inst())) {
      ++quicken_index;
    }
  }
  return DexFile::kDexNoIndex16;
}

const OatQuickMethodHeader* ArtMethod::GetOatQuickMethodHeader(uintptr_t pc) {
  // Our callers should make sure they don't pass the instrumentation exit pc,
  // as this method does not look at the side instrumentation stack.
  DCHECK_NE(pc, reinterpret_cast<uintptr_t>(GetQuickInstrumentationExitPc()));

  if (IsRuntimeMethod()) {
    return nullptr;
  }

  Runtime* runtime = Runtime::Current();
  const void* existing_entry_point = GetEntryPointFromQuickCompiledCode();
  CHECK(existing_entry_point != nullptr) << PrettyMethod() << "@" << this;
  ClassLinker* class_linker = runtime->GetClassLinker();

  if (existing_entry_point == GetQuickProxyInvokeHandler()) {
    DCHECK(IsProxyMethod() && !IsConstructor());
    // The proxy entry point does not have any method header.
    return nullptr;
  }

  // Check whether the current entry point contains this pc.
  if (!class_linker->IsQuickGenericJniStub(existing_entry_point) &&
      !class_linker->IsQuickResolutionStub(existing_entry_point) &&
      !class_linker->IsQuickToInterpreterBridge(existing_entry_point) &&
      existing_entry_point != GetQuickInstrumentationEntryPoint()) {
    OatQuickMethodHeader* method_header =
        OatQuickMethodHeader::FromEntryPoint(existing_entry_point);

    if (method_header->Contains(pc)) {
      return method_header;
    }
  }

  // Check whether the pc is in the JIT code cache.
  jit::Jit* jit = runtime->GetJit();
  if (jit != nullptr) {
    jit::JitCodeCache* code_cache = jit->GetCodeCache();
    OatQuickMethodHeader* method_header = code_cache->LookupMethodHeader(pc, this);
    if (method_header != nullptr) {
      DCHECK(method_header->Contains(pc));
      return method_header;
    } else {
      DCHECK(!code_cache->ContainsPc(reinterpret_cast<const void*>(pc)))
          << PrettyMethod()
          << ", pc=" << std::hex << pc
          << ", entry_point=" << std::hex << reinterpret_cast<uintptr_t>(existing_entry_point)
          << ", copy=" << std::boolalpha << IsCopied()
          << ", proxy=" << std::boolalpha << IsProxyMethod();
    }
  }

  // The code has to be in an oat file.
  bool found;
  OatFile::OatMethod oat_method =
      FindOatMethodFor(this, class_linker->GetImagePointerSize(), &found);
  if (!found) {
    if (IsNative()) {
      // We are running the GenericJNI stub. The entrypoint may point
      // to different entrypoints or to a JIT-compiled JNI stub.
      DCHECK(class_linker->IsQuickGenericJniStub(existing_entry_point) ||
             class_linker->IsQuickResolutionStub(existing_entry_point) ||
             existing_entry_point == GetQuickInstrumentationEntryPoint() ||
             (jit != nullptr && jit->GetCodeCache()->ContainsPc(existing_entry_point)));
      return nullptr;
    }
    // Only for unit tests.
    // TODO(ngeoffray): Update these tests to pass the right pc?
    return OatQuickMethodHeader::FromEntryPoint(existing_entry_point);
  }
  const void* oat_entry_point = oat_method.GetQuickCode();
  if (oat_entry_point == nullptr || class_linker->IsQuickGenericJniStub(oat_entry_point)) {
    DCHECK(IsNative()) << PrettyMethod();
    return nullptr;
  }

  OatQuickMethodHeader* method_header = OatQuickMethodHeader::FromEntryPoint(oat_entry_point);
  if (pc == 0) {
    // This is a downcall, it can only happen for a native method.
    DCHECK(IsNative());
    return method_header;
  }

  DCHECK(method_header->Contains(pc))
      << PrettyMethod()
      << " " << std::hex << pc << " " << oat_entry_point
      << " " << (uintptr_t)(method_header->GetCode() + method_header->GetCodeSize());
  return method_header;
}

const void* ArtMethod::GetOatMethodQuickCode(PointerSize pointer_size) {
  bool found;
  OatFile::OatMethod oat_method = FindOatMethodFor(this, pointer_size, &found);
  if (found) {
    return oat_method.GetQuickCode();
  }
  return nullptr;
}

bool ArtMethod::HasAnyCompiledCode() {
  if (IsNative() || !IsInvokable() || IsProxyMethod()) {
    return false;
  }

  // Check whether the JIT has compiled it.
  Runtime* runtime = Runtime::Current();
  jit::Jit* jit = runtime->GetJit();
  if (jit != nullptr && jit->GetCodeCache()->ContainsMethod(this)) {
    return true;
  }

  // Check whether we have AOT code.
  return GetOatMethodQuickCode(runtime->GetClassLinker()->GetImagePointerSize()) != nullptr;
}

void ArtMethod::SetIntrinsic(uint32_t intrinsic) {
  // Currently we only do intrinsics for static/final methods or methods of final
  // classes. We don't set kHasSingleImplementation for those methods.
  DCHECK(IsStatic() || IsFinal() || GetDeclaringClass()->IsFinal()) <<
      "Potential conflict with kAccSingleImplementation";
  static const int kAccFlagsShift = CTZ(kAccIntrinsicBits);
  DCHECK_LE(intrinsic, kAccIntrinsicBits >> kAccFlagsShift);
  uint32_t intrinsic_bits = intrinsic << kAccFlagsShift;
  uint32_t new_value = (GetAccessFlags() & ~kAccIntrinsicBits) | kAccIntrinsic | intrinsic_bits;
  if (kIsDebugBuild) {
    uint32_t java_flags = (GetAccessFlags() & kAccJavaFlagsMask);
    bool is_constructor = IsConstructor();
    bool is_synchronized = IsSynchronized();
    bool skip_access_checks = SkipAccessChecks();
    bool is_fast_native = IsFastNative();
    bool is_critical_native = IsCriticalNative();
    bool is_copied = IsCopied();
    bool is_miranda = IsMiranda();
    bool is_default = IsDefault();
    bool is_default_conflict = IsDefaultConflicting();
    bool is_compilable = IsCompilable();
    bool must_count_locks = MustCountLocks();
    // Recompute flags instead of getting them from the current access flags because
    // access flags may have been changed to deduplicate warning messages (b/129063331).
    uint32_t hiddenapi_flags = hiddenapi::CreateRuntimeFlags(this);
    SetAccessFlags(new_value);
    DCHECK_EQ(java_flags, (GetAccessFlags() & kAccJavaFlagsMask));
    DCHECK_EQ(is_constructor, IsConstructor());
    DCHECK_EQ(is_synchronized, IsSynchronized());
    DCHECK_EQ(skip_access_checks, SkipAccessChecks());
    DCHECK_EQ(is_fast_native, IsFastNative());
    DCHECK_EQ(is_critical_native, IsCriticalNative());
    DCHECK_EQ(is_copied, IsCopied());
    DCHECK_EQ(is_miranda, IsMiranda());
    DCHECK_EQ(is_default, IsDefault());
    DCHECK_EQ(is_default_conflict, IsDefaultConflicting());
    DCHECK_EQ(is_compilable, IsCompilable());
    DCHECK_EQ(must_count_locks, MustCountLocks());
    // Only DCHECK that we have preserved the hidden API access flags if the
    // original method was not on the whitelist. This is because the core image
    // does not have the access flags set (b/77733081).
    if ((hiddenapi_flags & kAccHiddenapiBits) != kAccPublicApi) {
      DCHECK_EQ(hiddenapi_flags, hiddenapi::GetRuntimeFlags(this)) << PrettyMethod();
    }
  } else {
    SetAccessFlags(new_value);
  }
}

void ArtMethod::SetNotIntrinsic() {
  if (!IsIntrinsic()) {
    return;
  }

  // Read the existing hiddenapi flags.
  uint32_t hiddenapi_runtime_flags = hiddenapi::GetRuntimeFlags(this);

  // Clear intrinsic-related access flags.
  ClearAccessFlags(kAccIntrinsic | kAccIntrinsicBits);

  // Re-apply hidden API access flags now that the method is not an intrinsic.
  SetAccessFlags(GetAccessFlags() | hiddenapi_runtime_flags);
  DCHECK_EQ(hiddenapi_runtime_flags, hiddenapi::GetRuntimeFlags(this));
}

void ArtMethod::CopyFrom(ArtMethod* src, PointerSize image_pointer_size) {
  memcpy(reinterpret_cast<void*>(this), reinterpret_cast<const void*>(src),
         Size(image_pointer_size));
  declaring_class_ = GcRoot<mirror::Class>(const_cast<ArtMethod*>(src)->GetDeclaringClass());

  // If the entry point of the method we are copying from is from JIT code, we just
  // put the entry point of the new method to interpreter or GenericJNI. We could set
  // the entry point to the JIT code, but this would require taking the JIT code cache
  // lock to notify it, which we do not want at this level.
  Runtime* runtime = Runtime::Current();
  if (runtime->UseJitCompilation()) {
    if (runtime->GetJit()->GetCodeCache()->ContainsPc(GetEntryPointFromQuickCompiledCode())) {
      SetEntryPointFromQuickCompiledCodePtrSize(
          src->IsNative() ? GetQuickGenericJniStub() : GetQuickToInterpreterBridge(),
          image_pointer_size);
    }
  }
  // Clear the profiling info for the same reasons as the JIT code.
  if (!src->IsNative()) {
    SetProfilingInfoPtrSize(nullptr, image_pointer_size);
  }
  // Clear hotness to let the JIT properly decide when to compile this method.
  hotness_count_ = 0;
}

bool ArtMethod::IsImagePointerSize(PointerSize pointer_size) {
  // Hijack this function to get access to PtrSizedFieldsOffset.
  //
  // Ensure that PrtSizedFieldsOffset is correct. We rely here on usually having both 32-bit and
  // 64-bit builds.
  static_assert(std::is_standard_layout<ArtMethod>::value, "ArtMethod is not standard layout.");
  static_assert(
      (sizeof(void*) != 4) ||
          (offsetof(ArtMethod, ptr_sized_fields_) == PtrSizedFieldsOffset(PointerSize::k32)),
      "Unexpected 32-bit class layout.");
  static_assert(
      (sizeof(void*) != 8) ||
          (offsetof(ArtMethod, ptr_sized_fields_) == PtrSizedFieldsOffset(PointerSize::k64)),
      "Unexpected 64-bit class layout.");

  Runtime* runtime = Runtime::Current();
  if (runtime == nullptr) {
    return true;
  }
  return runtime->GetClassLinker()->GetImagePointerSize() == pointer_size;
}

std::string ArtMethod::PrettyMethod(ArtMethod* m, bool with_signature) {
  if (m == nullptr) {
    return "null";
  }
  return m->PrettyMethod(with_signature);
}

std::string ArtMethod::PrettyMethod(bool with_signature) {
  if (UNLIKELY(IsRuntimeMethod())) {
    std::string result = GetDeclaringClassDescriptor();
    result += '.';
    result += GetName();
    // Do not add "<no signature>" even if `with_signature` is true.
    return result;
  }
  ArtMethod* m =
      GetInterfaceMethodIfProxy(Runtime::Current()->GetClassLinker()->GetImagePointerSize());
  std::string res(m->GetDexFile()->PrettyMethod(m->GetDexMethodIndex(), with_signature));
  if (with_signature && m->IsObsolete()) {
    return "<OBSOLETE> " + res;
  } else {
    return res;
  }
}

std::string ArtMethod::JniShortName() {
  return GetJniShortName(GetDeclaringClassDescriptor(), GetName());
}

std::string ArtMethod::JniLongName() {
  std::string long_name;
  long_name += JniShortName();
  long_name += "__";

  std::string signature(GetSignature().ToString());
  signature.erase(0, 1);
  signature.erase(signature.begin() + signature.find(')'), signature.end());

  long_name += MangleForJni(signature);

  return long_name;
}

const char* ArtMethod::GetRuntimeMethodName() {
  Runtime* const runtime = Runtime::Current();
  if (this == runtime->GetResolutionMethod()) {
    return "<runtime internal resolution method>";
  } else if (this == runtime->GetImtConflictMethod()) {
    return "<runtime internal imt conflict method>";
  } else if (this == runtime->GetCalleeSaveMethod(CalleeSaveType::kSaveAllCalleeSaves)) {
    return "<runtime internal callee-save all registers method>";
  } else if (this == runtime->GetCalleeSaveMethod(CalleeSaveType::kSaveRefsOnly)) {
    return "<runtime internal callee-save reference registers method>";
  } else if (this == runtime->GetCalleeSaveMethod(CalleeSaveType::kSaveRefsAndArgs)) {
    return "<runtime internal callee-save reference and argument registers method>";
  } else if (this == runtime->GetCalleeSaveMethod(CalleeSaveType::kSaveEverything)) {
    return "<runtime internal save-every-register method>";
  } else if (this == runtime->GetCalleeSaveMethod(CalleeSaveType::kSaveEverythingForClinit)) {
    return "<runtime internal save-every-register method for clinit>";
  } else if (this == runtime->GetCalleeSaveMethod(CalleeSaveType::kSaveEverythingForSuspendCheck)) {
    return "<runtime internal save-every-register method for suspend check>";
  } else {
    return "<unknown runtime internal method>";
  }
}

// AssertSharedHeld doesn't work in GetAccessFlags, so use a NO_THREAD_SAFETY_ANALYSIS helper.
// TODO: Figure out why ASSERT_SHARED_CAPABILITY doesn't work.
template <ReadBarrierOption kReadBarrierOption>
ALWAYS_INLINE static inline void DoGetAccessFlagsHelper(ArtMethod* method)
    NO_THREAD_SAFETY_ANALYSIS {
  CHECK(method->IsRuntimeMethod() ||
        method->GetDeclaringClass<kReadBarrierOption>()->IsIdxLoaded() ||
        method->GetDeclaringClass<kReadBarrierOption>()->IsErroneous());
}

}  // namespace art
