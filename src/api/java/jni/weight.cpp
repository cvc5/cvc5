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

#include <cvc5/cvc5.h>

#include <cstdint>

#include "api_utilities.h"
#include "io_github_cvc5_Weight.h"

using namespace cvc5;

/*
 * Class:     io_github_cvc5_Weight
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_io_github_cvc5_Weight_deletePointer(JNIEnv*,
                                                                jobject,
                                                                jlong pointer)
{
  delete reinterpret_cast<Weight*>(pointer);
}

/*
 * Class:     io_github_cvc5_Weight
 * Method:    getName
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_io_github_cvc5_Weight_getName(JNIEnv* env,
                                                             jobject,
                                                             jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Weight* current = reinterpret_cast<Weight*>(pointer);
  return env->NewStringUTF(current->getName().c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_Weight
 * Method:    getDefaultValue
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_Weight_getDefaultValue(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Weight* current = reinterpret_cast<Weight*>(pointer);
  Term* retPointer = new Term(current->getDefaultValue());
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Weight
 * Method:    equals
 * Signature: (JJ)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Weight_equals(JNIEnv* env,
                                                             jobject,
                                                             jlong pointer1,
                                                             jlong pointer2)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Weight* weight1 = reinterpret_cast<Weight*>(pointer1);
  Weight* weight2 = reinterpret_cast<Weight*>(pointer2);
  return static_cast<jboolean>(*weight1 == *weight2);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Weight
 * Method:    hashCode
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_io_github_cvc5_Weight_hashCode(JNIEnv* env,
                                                           jobject,
                                                           jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Weight* current = reinterpret_cast<Weight*>(pointer);
  return static_cast<jint>(std::hash<cvc5::Weight>()(*current));
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}
