/******************************************************************************
 * Top contributors (to current version):
 *   Hans-Jörg Schurr, Mudathir Mohamed
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

#include <cstdint>

#include "api_utilities.h"
#include "io_github_cvc5_Proof.h"

using namespace cvc5;

/*
 * Class:     io_github_cvc5_Proof
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_io_github_cvc5_Proof_deletePointer(JNIEnv* env,
                                                               jobject,
                                                               jlong pointer)
{
  delete reinterpret_cast<Proof*>(pointer);
}

/*
 * Class:     io_github_cvc5_Proof
 * Method:    getRule
 * Signature: (J)I;
 */
JNIEXPORT jint JNICALL Java_io_github_cvc5_Proof_getRule(JNIEnv* env,
                                                         jobject,
                                                         jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Proof* current = reinterpret_cast<Proof*>(pointer);
  return static_cast<jint>(current->getRule());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Proof
 * Method:    getResult
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Proof_getResult(JNIEnv* env,
                                                            jobject,
                                                            jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Proof* current = reinterpret_cast<Proof*>(pointer);
  Term* ret = new Term(current->getResult());
  return reinterpret_cast<jlong>(ret);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Proof
 * Method:    getChildren
 * Signature: (J)[J
 */
JNIEXPORT jlongArray JNICALL
Java_io_github_cvc5_Proof_getChildren(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Proof* current = reinterpret_cast<Proof*>(pointer);
  std::vector<Proof> proofs = current->getChildren();
  jlongArray ret = getPointersFromObjects<Proof>(env, proofs);
  return ret;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Proof
 * Method:    getArguments
 * Signature: (J)[J
 */
JNIEXPORT jlongArray JNICALL
Java_io_github_cvc5_Proof_getArguments(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Proof* current = reinterpret_cast<Proof*>(pointer);
  std::vector<Term> args = current->getArguments();
  jlongArray ret = getPointersFromObjects<Term>(env, args);
  return ret;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}
