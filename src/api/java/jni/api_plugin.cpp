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

ApiPlugin::ApiPlugin(TermManager& tm, JavaVM* vm, jweak plugin)
    : Plugin(tm), d_vm(vm), d_plugin(plugin)
{
}

std::vector<Term> ApiPlugin::check()
{
  JNIEnv* env = getEnv(d_vm);
  // Release the local references created below when done: this function may
  // be called many times during a single native call.
  env->PushLocalFrame(callbackLocalFrameCapacity);
  jobject plugin = env->NewLocalRef(d_plugin);
  if (plugin == nullptr)
  {
    env->PopLocalFrame(nullptr);
    return {};
  }

  jclass pluginClass = env->GetObjectClass(plugin);
  jmethodID checkMethod = env->GetMethodID(pluginClass, "checkNative", "()[J");
  jlongArray jPointers =
      static_cast<jlongArray>(env->CallObjectMethod(plugin, checkMethod));
  if (env->ExceptionCheck())
  {
    env->ExceptionClear();
    env->PopLocalFrame(nullptr);
    throw CVC5ApiException("The plugin threw an exception in check().");
  }
  // The lemmas are owned by their Java wrappers, which cannot be reclaimed
  // before this native call returns to Java. Copy them now.
  std::vector<Term> terms = getObjectsFromPointers<Term>(env, jPointers);

  env->PopLocalFrame(nullptr);
  return terms;
}

void ApiPlugin::notifyHelper(const char* functionName, const Term& cl)
{
  JNIEnv* env = getEnv(d_vm);
  env->PushLocalFrame(callbackLocalFrameCapacity);
  jobject plugin = env->NewLocalRef(d_plugin);
  if (plugin == nullptr)
  {
    env->PopLocalFrame(nullptr);
    return;
  }

  // Ownership of the copy is transferred to the Java wrapper created by the
  // bridge.
  jlong termPointer = reinterpret_cast<jlong>(new Term(cl));
  jclass pluginClass = env->GetObjectClass(plugin);
  jmethodID method = env->GetMethodID(pluginClass, functionName, "(J)V");
  env->CallVoidMethod(plugin, method, termPointer);
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
  notifyHelper("notifySatClauseNative", cl);
}

void ApiPlugin::notifyTheoryLemma(const Term& lem)
{
  notifyHelper("notifyTheoryLemmaNative", lem);
}

std::string ApiPlugin::getName()
{
  JNIEnv* env = getEnv(d_vm);
  env->PushLocalFrame(callbackLocalFrameCapacity);
  jobject plugin = env->NewLocalRef(d_plugin);
  if (plugin == nullptr)
  {
    env->PopLocalFrame(nullptr);
    return "";
  }

  jclass pluginClass = env->GetObjectClass(plugin);
  jmethodID getNameMethod =
      env->GetMethodID(pluginClass, "getName", "()Ljava/lang/String;");
  jstring jName =
      static_cast<jstring>(env->CallObjectMethod(plugin, getNameMethod));
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
