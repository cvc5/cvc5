/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Daniel Larraz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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

ApiPlugin::ApiPlugin(TermManager& tm, JNIEnv* env, jobject plugin)
    : Plugin(tm), d_env(env), d_plugin(plugin)
{
}

std::vector<Term> ApiPlugin::check()
{
  jclass termClass = d_env->FindClass("Lio/github/cvc5/Term;");
  jfieldID pointer = d_env->GetFieldID(termClass, "pointer", "J");

  jclass pluginClass = d_env->GetObjectClass(d_plugin);

  jmethodID checkMethod =
      d_env->GetMethodID(pluginClass, "check", "()[Lio/github/cvc5/Term;");
  jobjectArray jTerms =
      (jobjectArray)d_env->CallObjectMethod(d_plugin, checkMethod);
  jsize size = d_env->GetArrayLength(jTerms);
  std::vector<Term> terms;
  for (jsize i = 0; i < size; i++)
  {
    jobject jTerm = d_env->GetObjectArrayElement(jTerms, i);
    jlong termPointer = d_env->GetLongField(jTerm, pointer);
    Term* term = reinterpret_cast<Term*>(termPointer);
    terms.push_back(*term);
  }
  return terms;
}

void ApiPlugin::notifyHelper(const char* functionName, const Term& cl)
{
  jclass termClass = d_env->FindClass("Lio/github/cvc5/Term;");
  jmethodID termConstructor = d_env->GetMethodID(termClass, "<init>", "(J)V");
  jlong termPointer = reinterpret_cast<jlong>(new Term(cl));
  jobject jTerm = d_env->NewObject(termClass, termConstructor, termPointer);

  jclass pluginClass = d_env->GetObjectClass(d_plugin);

  jmethodID method =
      d_env->GetMethodID(pluginClass, functionName, "(Lio/github/cvc5/Term;)V");

  d_env->CallVoidMethod(d_plugin, method, jTerm);
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
  jclass pluginClass = d_env->GetObjectClass(d_plugin);
  jmethodID getNameMethod =
      d_env->GetMethodID(pluginClass, "getName", "()Ljava/lang/String;");
  jstring jName = (jstring)d_env->CallObjectMethod(d_plugin, getNameMethod);

  const char* s = d_env->GetStringUTFChars(jName, nullptr);
  std::string name(s);
  return name;
}
