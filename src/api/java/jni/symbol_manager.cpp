/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
    JNIEnv* env, jclass, jlong solverPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(solverPointer);
  SymbolManager* symbolManager = new SymbolManager(solver);
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
 * Method:    getModelDeclaredSorts
 * Signature: (J)[J
 */
JNIEXPORT jlongArray JNICALL
Java_io_github_cvc5_SymbolManager_getModelDeclaredSorts(JNIEnv* env,
                                                        jobject,
                                                        jlong pointer)
{

  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  SymbolManager* symbolManager = reinterpret_cast<SymbolManager*>(pointer);
  std::vector<Sort> sorts = symbolManager->getModelDeclaredSorts();
  jlongArray ret = getPointersFromObjects<Sort>(env, sorts);
  return ret;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_SymbolManager
 * Method:    getModelDeclaredTerms
 * Signature: (J)[J
 */
JNIEXPORT jlongArray JNICALL Java_io_github_cvc5_Solver_getModelDeclaredTerms(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  SymbolManager* symbolManager = reinterpret_cast<SymbolManager*>(pointer);
  std::vector<Term> terms = symbolManager->getModelDeclaredTerms();
  jlongArray ret = getPointersFromObjects<Term>(env, terms);
  return ret;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}
