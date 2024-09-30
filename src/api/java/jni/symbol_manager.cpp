/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 Java API.
 */

#include <cvc5/cvc5.h>
#include <cvc5/cvc5_parser.h>

#include "api_utilities.h"
#include "io_github_cvc5_SymbolManager.h"

using namespace cvc5;
using namespace cvc5::parser;

/*
 * Class:     io_github_cvc5_SymbolManager
 * Method:    newSymbolManager
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_SymbolManager_newSymbolManager(
    JNIEnv* env, jclass, jlong tmPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(tmPointer);
  SymbolManager* symbolManager = new SymbolManager(*tm);
  return reinterpret_cast<jlong>(symbolManager);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_SymbolManager
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_io_github_cvc5_SymbolManager_deletePointer(
    JNIEnv* env, jobject, jlong pointer)
{
  delete reinterpret_cast<SymbolManager*>(pointer);
}

/*
 * Class:     io_github_cvc5_SymbolManager
 * Method:    isLogicSet
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_SymbolManager_isLogicSet(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  SymbolManager* symbolManager = reinterpret_cast<SymbolManager*>(pointer);
  return static_cast<jboolean>(symbolManager->isLogicSet());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_SymbolManager
 * Method:    getLogic
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL
Java_io_github_cvc5_SymbolManager_getLogic(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  SymbolManager* symbolManager = reinterpret_cast<SymbolManager*>(pointer);
  return env->NewStringUTF(symbolManager->getLogic().c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_SymbolManager
 * Method:    getDeclaredSorts
 * Signature: (J)[J
 */
JNIEXPORT jlongArray JNICALL Java_io_github_cvc5_SymbolManager_getDeclaredSorts(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  SymbolManager* symbolManager = reinterpret_cast<SymbolManager*>(pointer);
  std::vector<Sort> sorts = symbolManager->getDeclaredSorts();
  jlongArray ret = getPointersFromObjects<Sort>(env, sorts);
  return ret;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_SymbolManager
 * Method:    getDeclaredTerms
 * Signature: (J)[J
 */
JNIEXPORT jlongArray JNICALL Java_io_github_cvc5_SymbolManager_getDeclaredTerms(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  SymbolManager* symbolManager = reinterpret_cast<SymbolManager*>(pointer);
  std::vector<Term> terms = symbolManager->getDeclaredTerms();
  jlongArray ret = getPointersFromObjects<Term>(env, terms);
  return ret;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_SymbolManager
 * Method:    getNamedTerms
 * Signature: (J)Ljava/util/Map;
 */
JNIEXPORT jobject JNICALL Java_io_github_cvc5_SymbolManager_getNamedTerms(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  SymbolManager* symbolManager = reinterpret_cast<SymbolManager*>(pointer);
  std::map<Term, std::string> map = symbolManager->getNamedTerms();
  // HashMap hashMap = new HashMap();
  jclass hashMapClass = env->FindClass("Ljava/util/HashMap;");
  jmethodID constructor = env->GetMethodID(hashMapClass, "<init>", "()V");
  jobject hashMap = env->NewObject(hashMapClass, constructor);
  jmethodID putMethod = env->GetMethodID(
      hashMapClass,
      "put",
      "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;");

  jclass longClass = env->FindClass("Ljava/lang/Long;");
  jmethodID longConstructor = env->GetMethodID(longClass, "<init>", "(J)V");

  for (const auto& [k, v] : map)
  {
    // hashmap.put(key, value);
    Term* termKey = new Term(k);
    jobject key = env->NewObject(
        longClass, longConstructor, reinterpret_cast<jlong>(termKey));
    jstring value = env->NewStringUTF(v.c_str());
    env->CallObjectMethod(hashMap, putMethod, key, value);
  }
  return hashMap;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}
