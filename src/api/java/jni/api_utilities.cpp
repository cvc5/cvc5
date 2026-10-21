/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 Java API.
 */

#include "api_utilities.h"

#include <string>
#include <vector>

jobjectArray getStringArrayFromStringVector(
    JNIEnv* env, const std::vector<std::string>& cStrings)
{
  jclass stringClass = env->FindClass("java/lang/String");
  jobjectArray ret =
      env->NewObjectArray(cStrings.size(), stringClass, env->NewStringUTF(""));
  for (size_t i = 0; i < cStrings.size(); i++)
  {
    jstring jString = env->NewStringUTF(cStrings[i].c_str());
    env->SetObjectArrayElement(ret, i, jString);
  }
  return ret;
}

jobject getDoubleObject(JNIEnv* env, double cValue)
{
  jdouble jValue = static_cast<jdouble>(cValue);
  jclass doubleClass = env->FindClass("java/lang/Double");
  jmethodID methodId = env->GetMethodID(doubleClass, "<init>", "(D)V");
  jobject ret = env->NewObject(doubleClass, methodId, jValue);
  return ret;
}

jobject getBooleanObject(JNIEnv* env, bool cValue)
{
  jboolean jValue = static_cast<jboolean>(cValue);
  jclass booleanClass = env->FindClass("Ljava/lang/Boolean;");
  jmethodID booleanConstructor =
      env->GetMethodID(booleanClass, "<init>", "(Z)V");
  jobject ret = env->NewObject(booleanClass, booleanConstructor, jValue);
  return ret;
}

JNIEnv* getEnv(JavaVM* vm)
{
  JNIEnv* env = nullptr;
  jint rc = vm->GetEnv(reinterpret_cast<void**>(&env), JNI_VERSION_1_6);
  if (rc == JNI_EDETACHED)
  {
    vm->AttachCurrentThread(reinterpret_cast<void**>(&env), nullptr);
  }
  return env;
}

cvc5::Term applyOracle(JavaVM* vm,
                       jobject oracleRef,
                       const std::vector<cvc5::Term>& terms)
{
  JNIEnv* env = getEnv(vm);
  // Release the local references created below when done: this function may
  // be called many times during a single native call.
  env->PushLocalFrame(callbackLocalFrameCapacity);

  // Ownership of the term copies is transferred to the Java wrappers created
  // by the bridge.
  std::vector<jlong> pointers;
  pointers.reserve(terms.size());
  for (const cvc5::Term& term : terms)
  {
    pointers.push_back(reinterpret_cast<jlong>(new cvc5::Term(term)));
  }
  jlongArray jPointers = env->NewLongArray(pointers.size());
  env->SetLongArrayRegion(jPointers, 0, pointers.size(), pointers.data());

  jclass oracleClass = env->GetObjectClass(oracleRef);
  jmethodID applyMethod = env->GetMethodID(oracleClass, "apply", "([J)J");
  jlong termPointer = env->CallLongMethod(oracleRef, applyMethod, jPointers);
  if (env->ExceptionCheck() || termPointer == 0)
  {
    env->ExceptionClear();
    env->PopLocalFrame(nullptr);
    throw cvc5::CVC5ApiException("The oracle threw an exception.");
  }
  // The result is owned by its Java wrapper, which cannot be reclaimed before
  // this native call returns to Java. Copy it now.
  cvc5::Term term = *reinterpret_cast<cvc5::Term*>(termPointer);

  env->PopLocalFrame(nullptr);
  return term;
}
