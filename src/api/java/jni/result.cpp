/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andres Noetzli, Andrew Reynolds
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

#include "api_utilities.h"
#include "io_github_cvc5_Result.h"

using namespace cvc5;

/*
 * Class:     io_github_cvc5_Result
 * Method:    getNullResult
 * Signature: ()J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Result_getNullResult(JNIEnv* env,
                                                                 jclass)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Result* ret = new Result();
  return reinterpret_cast<jlong>(ret);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}
/*
 * Class:     io_github_cvc5_Result
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_io_github_cvc5_Result_deletePointer(JNIEnv*,
                                                                jobject,
                                                                jlong pointer)
{
  delete ((Result*)pointer);
}

/*
 * Class:     io_github_cvc5_Result
 * Method:    isNull
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Result_isNull(JNIEnv* env,
                                                             jobject,
                                                             jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Result* current = (Result*)pointer;
  return (jboolean)current->isNull();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     io_github_cvc5_Result
 * Method:    isSat
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Result_isSat(JNIEnv* env,
                                                            jobject,
                                                            jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Result* current = (Result*)pointer;
  return (jboolean)current->isSat();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     io_github_cvc5_Result
 * Method:    isUnsat
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Result_isUnsat(JNIEnv* env,
                                                              jobject,
                                                              jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Result* current = (Result*)pointer;
  return (jboolean)current->isUnsat();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     io_github_cvc5_Result
 * Method:    isUnknown
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Result_isUnknown(JNIEnv* env,
                                                                jobject,
                                                                jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Result* current = (Result*)pointer;
  return (jboolean)current->isUnknown();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     io_github_cvc5_Result
 * Method:    equals
 * Signature: (JJ)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Result_equals(JNIEnv* env,
                                                             jobject,
                                                             jlong pointer1,
                                                             jlong pointer2)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Result* result1 = (Result*)pointer1;
  Result* result2 = (Result*)pointer2;
  // We compare the actual terms, not their pointers.
  return (jboolean)(*result1 == *result2);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     io_github_cvc5_Result
 * Method:    getUnknownExplanation
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_io_github_cvc5_Result_getUnknownExplanation(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Result* current = (Result*)pointer;
  return (jint)current->getUnknownExplanation();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Result
 * Method:    toString
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_io_github_cvc5_Result_toString(JNIEnv* env,
                                                              jobject,
                                                              jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Result* current = (Result*)pointer;
  return env->NewStringUTF(current->toString().c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}
