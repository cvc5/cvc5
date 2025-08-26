/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mudathir Mohamed, Aina Niemetz
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

#include <cvc5/cvc5.h>

#include "api_utilities.h"
#include "io_github_cvc5_SynthResult.h"

using namespace cvc5;

/*
 * Class:     io_github_cvc5_SynthResult
 * Method:    getNullSynthResult
 * Signature: ()J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_SynthResult_getNullSynthResult(JNIEnv* env, jclass)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  SynthResult* ret = new SynthResult();
  return reinterpret_cast<jlong>(ret);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_SynthResult
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL
Java_io_github_cvc5_SynthResult_deletePointer(JNIEnv*, jobject, jlong pointer)
{
  delete ((SynthResult*)pointer);
}

/*
 * Class:     io_github_cvc5_SynthResult
 * Method:    isNull
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_SynthResult_isNull(JNIEnv* env,
                                                                  jobject,
                                                                  jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  SynthResult* current = (SynthResult*)pointer;
  return (jboolean)current->isNull();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     io_github_cvc5_SynthResult
 * Method:    equals
 * Signature: (JJ)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_SynthResult_equals(
    JNIEnv* env, jobject, jlong pointer1, jlong pointer2)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  SynthResult* result1 = (SynthResult*)pointer1;
  SynthResult* result2 = (SynthResult*)pointer2;
  // We compare the actual terms, not their pointers.
  return (jboolean)(*result1 == *result2);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     io_github_cvc5_SynthResult
 * Method:    hasSolution
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL
Java_io_github_cvc5_SynthResult_hasSolution(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  SynthResult* current = (SynthResult*)pointer;
  return (jboolean)current->hasSolution();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     io_github_cvc5_SynthResult
 * Method:    hasNoSolution
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_SynthResult_hasNoSolution(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  SynthResult* current = (SynthResult*)pointer;
  return (jboolean)current->hasNoSolution();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     io_github_cvc5_SynthResult
 * Method:    isUnknown
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL
Java_io_github_cvc5_SynthResult_isUnknown(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  SynthResult* current = (SynthResult*)pointer;
  return (jboolean)current->isUnknown();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     io_github_cvc5_SynthResult
 * Method:    toString
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL
Java_io_github_cvc5_SynthResult_toString(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  SynthResult* current = (SynthResult*)pointer;
  return env->NewStringUTF(current->toString().c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_SynthResult
 * Method:    hashCode
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_io_github_cvc5_SynthResult_hashCode(JNIEnv* env,
                                                                jobject,
                                                                jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  SynthResult* result = reinterpret_cast<SynthResult*>(pointer);
  return static_cast<jint>(std::hash<cvc5::SynthResult>()(*result));
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}
