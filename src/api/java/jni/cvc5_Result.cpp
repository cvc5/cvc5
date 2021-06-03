/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 Java API.
 */

#include "cvc5_Result.h"

#include "api/cpp/cvc5.h"
#include "cvc5JavaApi.h"

using namespace cvc5::api;

/*
 * Class:     cvc5_Result
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_cvc5_Result_deletePointer(JNIEnv*,
                                                      jclass,
                                                      jlong pointer)
{
  delete ((Result*)pointer);
}

/*
 * Class:     cvc5_Result
 * Method:    isNull
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Result_isNull(JNIEnv* env,
                                                   jobject,
                                                   jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Result* current = (Result*)pointer;
  return (jboolean)current->isNull();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Result
 * Method:    isSat
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Result_isSat(JNIEnv* env,
                                                  jobject,
                                                  jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Result* current = (Result*)pointer;
  return (jboolean)current->isSat();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Result
 * Method:    isUnsat
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Result_isUnsat(JNIEnv* env,
                                                    jobject,
                                                    jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Result* current = (Result*)pointer;
  return (jboolean)current->isUnsat();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Result
 * Method:    isSatUnknown
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Result_isSatUnknown(JNIEnv* env,
                                                         jobject,
                                                         jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Result* current = (Result*)pointer;
  return (jboolean)current->isSatUnknown();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Result
 * Method:    isEntailed
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Result_isEntailed(JNIEnv* env,
                                                       jobject,
                                                       jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Result* current = (Result*)pointer;
  return (jboolean)current->isEntailed();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Result
 * Method:    isNotEntailed
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Result_isNotEntailed(JNIEnv* env,
                                                          jobject,
                                                          jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Result* current = (Result*)pointer;
  return (jboolean)current->isNotEntailed();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Result
 * Method:    isEntailmentUnknown
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Result_isEntailmentUnknown(JNIEnv* env,
                                                                jobject,
                                                                jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Result* current = (Result*)pointer;
  return (jboolean)current->isEntailmentUnknown();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Result
 * Method:    equals
 * Signature: (JJ)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Result_equals(JNIEnv* env,
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
 * Class:     cvc5_Result
 * Method:    getUnknownExplanation
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_cvc5_Result_getUnknownExplanation(JNIEnv* env,
                                                              jobject,
                                                              jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Result* current = (Result*)pointer;
  return (jint)current->getUnknownExplanation();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Result
 * Method:    toString
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_cvc5_Result_toString(JNIEnv* env,
                                                    jobject,
                                                    jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Result* current = (Result*)pointer;
  return env->NewStringUTF(current->toString().c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}
