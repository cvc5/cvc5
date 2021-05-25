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

#include "cvc5_Op.h"

#include "api/cpp/cvc5.h"
#include "cvc5JavaApi.h"

using namespace cvc5::api;

/*
 * Class:     cvc5_Op
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_cvc5_Op_deletePointer(JNIEnv*,
                                                  jclass,
                                                  jlong pointer)
{
  delete ((Op*)pointer);
}

/*
 * Class:     cvc5_Op
 * Method:    equals
 * Signature: (JJ)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Op_equals(JNIEnv* env,
                                               jobject,
                                               jlong pointer1,
                                               jlong pointer2)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Op* op1 = (Op*)pointer1;
  Op* op2 = (Op*)pointer2;
  // We compare the actual operators, not their pointers.
  return (jboolean)(*op1 == *op2);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Op
 * Method:    getKind
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_cvc5_Op_getKind(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Op* current = (Op*)pointer;
  return (jboolean)current->getKind();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Op
 * Method:    isNull
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Op_isNull(JNIEnv* env,
                                               jobject,
                                               jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Op* current = (Op*)pointer;
  return (jboolean)current->isNull();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Op
 * Method:    isIndexed
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Op_isIndexed(JNIEnv* env,
                                                  jobject,
                                                  jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Op* current = (Op*)pointer;
  return (jboolean)current->isIndexed();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, false);
}

/*
 * Class:     cvc5_Op
 * Method:    getNumIndices
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_cvc5_Op_getNumIndices(JNIEnv* env,
                                                  jobject,
                                                  jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Op* current = (Op*)pointer;
  return (jint)current->getNumIndices();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Op
 * Method:    getIntegerIndices
 * Signature: (J)[I
 */
JNIEXPORT jintArray JNICALL Java_cvc5_Op_getIntegerIndices(JNIEnv* env,
                                                           jobject,
                                                           jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Op* current = (Op*)pointer;
  size_t size = current->getNumIndices();
  std::vector<jint> indices(size);
  if (size == 1)
  {
    uint32_t index = current->getIndices<uint32_t>();
    indices[0] = index;
  }

  if (size == 2)
  {
    std::pair<uint32_t, uint32_t> pair =
        current->getIndices<std::pair<uint32_t, uint32_t>>();
    indices[0] = pair.first;
    indices[1] = pair.second;
  }

  if (size > 2)
  {
    std::string message = "Unhandled case when number of indices > 2.";
    throw CVC5ApiException(message);
  }

  jintArray ret = env->NewIntArray((jsize)size);
  env->SetIntArrayRegion(ret, 0, size, indices.data());
  return ret;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     cvc5_Op
 * Method:    getStringIndices
 * Signature: (J)[Ljava/lang/String;
 */
JNIEXPORT jobjectArray JNICALL Java_cvc5_Op_getStringIndices(JNIEnv* env,
                                                             jobject,
                                                             jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Op* current = (Op*)pointer;
  size_t size = current->getNumIndices();
  std::vector<jstring> indices(size);
  if (size == 1)
  {
    std::string cIndex = current->getIndices<std::string>();
    jstring jIndex = env->NewStringUTF(cIndex.c_str());
    indices[0] = jIndex;
  }

  if (size > 1)  // currently only one string is implemented in cvc5.cpp
  {
    std::string message = "Unhandled case when number of indices > 1.";
    throw CVC5ApiException(message);
  }

  // construct a java array of String
  jclass stringClass = env->FindClass("Ljava/lang/String;");
  jobjectArray ret = env->NewObjectArray((jsize)size, stringClass, nullptr);
  for (size_t i = 0; i < size; i++)
  {
    env->SetObjectArrayElement(ret, i, indices[i]);
  }
  return ret;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     cvc5_Op
 * Method:    toString
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_cvc5_Op_toString(JNIEnv* env,
                                                jobject,
                                                jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Op* current = (Op*)pointer;
  return env->NewStringUTF(current->toString().c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}
