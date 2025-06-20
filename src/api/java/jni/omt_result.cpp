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
#include "io_github_cvc5_OmtResult.h"

using namespace cvc5;

/*
 * Class:     io_github_cvc5_OmtResult
 * Method:    getNullOmtResult
 * Signature: ()J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_OmtResult_getNullOmtResult(JNIEnv* env, jclass)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  OmtResult* ret = new OmtResult();
  return reinterpret_cast<jlong>(ret);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_OmtResult
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL
Java_io_github_cvc5_OmtResult_deletePointer(JNIEnv*, jobject, jlong pointer)
{
  delete ((OmtResult*)pointer);
}

/*
 * Class:     io_github_cvc5_OmtResult
 * Method:    equals
 * Signature: (JJ)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_OmtResult_equals(
    JNIEnv* env, jobject, jlong pointer1, jlong pointer2)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  OmtResult* result1 = (OmtResult*)pointer1;
  OmtResult* result2 = (OmtResult*)pointer2;
  // We compare the actual terms, not their pointers.
  return (jboolean)(*result1 == *result2);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     io_github_cvc5_OmtResult
 * Method:    isNull
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_OmtResult_isNull(JNIEnv* env,
                                                                  jobject,
                                                                  jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  OmtResult* current = (OmtResult*)pointer;
  return (jboolean)current->isNull();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     io_github_cvc5_OmtResult
 * Method:    isOptimal
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL
Java_io_github_cvc5_OmtResult_isOptimal(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  return (jboolean)((OmtResult*)pointer)->isOptimal();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean)false);
}

/*
 * Class:     io_github_cvc5_OmtResult
 * Method:    isLimitOptimal
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL
Java_io_github_cvc5_OmtResult_isLimitOptimal(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  return (jboolean)((OmtResult*)pointer)->isLimitOptimal();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean)false);
}

/*
 * Class:     io_github_cvc5_OmtResult
 * Method:    isNonOptimal
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL
Java_io_github_cvc5_OmtResult_isNonOptimal(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  return (jboolean)((OmtResult*)pointer)->isNonOptimal();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean)false);
}

/*
 * Class:     io_github_cvc5_OmtResult
 * Method:    isUnbounded
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL
Java_io_github_cvc5_OmtResult_isUnbounded(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  return (jboolean)((OmtResult*)pointer)->isUnbounded();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean)false);
}

/*
 * Class:     io_github_cvc5_OmtResult
 * Method:    isUnsat
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL
Java_io_github_cvc5_OmtResult_isUnsat(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  return (jboolean)((OmtResult*)pointer)->isUnsat();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean)false);
}

/*
 * Class:     io_github_cvc5_OmtResult
 * Method:    isUnknown
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL
Java_io_github_cvc5_OmtResult_isUnknown(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  return (jboolean)((OmtResult*)pointer)->isUnknown();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean)false);
}

/*
 * Class:     io_github_cvc5_OmtResult
 * Method:    toString
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL
Java_io_github_cvc5_OmtResult_toString(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  return env->NewStringUTF(((OmtResult*)pointer)->toString().c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_OmtResult
 * Method:    hashCode
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL
Java_io_github_cvc5_OmtResult_hashCode(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  OmtResult* result = reinterpret_cast<OmtResult*>(pointer);
  return static_cast<jint>(std::hash<OmtResult>()(*result));
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}