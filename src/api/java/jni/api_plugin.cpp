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
#include "api_plugin.h"

#include "api_utilities.h"

using namespace cvc5;

ApiPlugin::ApiPlugin(TermManager& tm, JavaVM* vm, jobject plugin)
    : Plugin(tm), d_vm(vm), d_plugin(plugin)
{
}

std::vector<Term> ApiPlugin::check()
{
  JNIEnv* env = getEnv(d_vm);
  // Release the local references created below when done: this function may
  // be called many times during a single native call.
  env->PushLocalFrame(16);

  jclass termClass = env->FindClass("io/github/cvc5/Term");
  jfieldID pointer = env->GetFieldID(termClass, "pointer", "J");
  jclass pluginClass = env->GetObjectClass(d_plugin);
  jmethodID checkMethod =
      env->GetMethodID(pluginClass, "check", "()[Lio/github/cvc5/Term;");
  jobjectArray jTerms =
      static_cast<jobjectArray>(env->CallObjectMethod(d_plugin, checkMethod));
  if (env->ExceptionCheck() || jTerms == nullptr)
  {
    env->ExceptionClear();
    env->PopLocalFrame(nullptr);
    throw CVC5ApiException(
        "The plugin threw an exception or returned null in check().");
  }
  jsize size = env->GetArrayLength(jTerms);
  std::vector<Term> terms;
  for (jsize i = 0; i < size; i++)
  {
    jobject jTerm = env->GetObjectArrayElement(jTerms, i);
    jlong termPointer = env->GetLongField(jTerm, pointer);
    terms.push_back(*reinterpret_cast<Term*>(termPointer));
    env->DeleteLocalRef(jTerm);
  }

  env->PopLocalFrame(nullptr);
  return terms;
}

void ApiPlugin::notifyHelper(const char* functionName, const Term& cl)
{
  JNIEnv* env = getEnv(d_vm);
  env->PushLocalFrame(16);

  jclass termClass = env->FindClass("io/github/cvc5/Term");
  jmethodID termConstructor = env->GetMethodID(termClass, "<init>", "(J)V");
  jlong termPointer = reinterpret_cast<jlong>(new Term(cl));
  jobject jTerm = env->NewObject(termClass, termConstructor, termPointer);
  jclass pluginClass = env->GetObjectClass(d_plugin);
  jmethodID method =
      env->GetMethodID(pluginClass, functionName, "(Lio/github/cvc5/Term;)V");
  env->CallVoidMethod(d_plugin, method, jTerm);
  if (env->ExceptionCheck())
  {
    env->ExceptionClear();
    env->PopLocalFrame(nullptr);
    throw CVC5ApiException(std::string("The plugin threw an exception in ")
                           + functionName + "().");
  }

  env->PopLocalFrame(nullptr);
}

void ApiPlugin::notifySatClause(const Term& cl)
{
  notifyHelper("notifySatClause", cl);
}

void ApiPlugin::notifyTheoryLemma(const Term& lem)
{
  notifyHelper("notifyTheoryLemma", lem);
}

std::string ApiPlugin::getName()
{
  JNIEnv* env = getEnv(d_vm);
  env->PushLocalFrame(16);

  jclass pluginClass = env->GetObjectClass(d_plugin);
  jmethodID getNameMethod =
      env->GetMethodID(pluginClass, "getName", "()Ljava/lang/String;");
  jstring jName =
      static_cast<jstring>(env->CallObjectMethod(d_plugin, getNameMethod));
  if (env->ExceptionCheck() || jName == nullptr)
  {
    env->ExceptionClear();
    env->PopLocalFrame(nullptr);
    throw CVC5ApiException("The plugin threw an exception in getName().");
  }
  const char* s = env->GetStringUTFChars(jName, nullptr);
  std::string name(s);
  env->ReleaseStringUTFChars(jName, s);

  env->PopLocalFrame(nullptr);
  return name;
}
