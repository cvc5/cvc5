/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andres Noetzli, Aina Niemetz
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
#include "io_github_cvc5_Sort.h"

using namespace cvc5;

/*
 * Class:     io_github_cvc5_Sort
 * Method:    getNullSort
 * Signature: ()J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Sort_getNullSort(JNIEnv* env,
                                                             jclass)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* ret = new Sort();
  return reinterpret_cast<jlong>(ret);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_io_github_cvc5_Sort_deletePointer(JNIEnv*,
                                                              jobject,
                                                              jlong pointer)
{
  delete reinterpret_cast<Sort*>(pointer);
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    equals
 * Signature: (JJ)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Sort_equals(JNIEnv* env,
                                                           jobject,
                                                           jlong pointer1,
                                                           jlong pointer2)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort sort1 = *(reinterpret_cast<Sort*>(pointer1));
  Sort sort2 = *(reinterpret_cast<Sort*>(pointer2));
  return static_cast<jboolean>((sort1 == sort2));
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    compareTo
 * Signature: (JJ)I
 */
JNIEXPORT jint JNICALL Java_io_github_cvc5_Sort_compareTo(JNIEnv* env,
                                                          jobject,
                                                          jlong pointer1,
                                                          jlong pointer2)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* sort1 = reinterpret_cast<Sort*>(pointer1);
  Sort* sort2 = reinterpret_cast<Sort*>(pointer2);
  if (*sort1 < *sort2)
  {
    return static_cast<jint>(-1);
  }
  if (*sort1 == *sort2)
  {
    return 0;
  }
  return static_cast<jint>(1);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    getKind
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_io_github_cvc5_Sort_getKind(JNIEnv* env,
                                                        jobject,
                                                        jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return static_cast<jint>(current->getKind());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    hasSymbol
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Sort_hasSymbol(JNIEnv* env,
                                                              jobject,
                                                              jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return static_cast<jboolean>(current->hasSymbol());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    getSymbol
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_io_github_cvc5_Sort_getSymbol(JNIEnv* env,
                                                             jobject,
                                                             jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return env->NewStringUTF(current->getSymbol().c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    isNull
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Sort_isNull(JNIEnv* env,
                                                           jobject,
                                                           jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return static_cast<jboolean>(current->isNull());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    isBoolean
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Sort_isBoolean(JNIEnv* env,
                                                              jobject,
                                                              jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return static_cast<jboolean>(current->isBoolean());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    isInteger
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Sort_isInteger(JNIEnv* env,
                                                              jobject,
                                                              jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return static_cast<jboolean>(current->isInteger());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    isReal
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Sort_isReal(JNIEnv* env,
                                                           jobject,
                                                           jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return static_cast<jboolean>(current->isReal());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    isString
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Sort_isString(JNIEnv* env,
                                                             jobject,
                                                             jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return static_cast<jboolean>(current->isString());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    isRegExp
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Sort_isRegExp(JNIEnv* env,
                                                             jobject,
                                                             jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return static_cast<jboolean>(current->isRegExp());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    isRoundingMode
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL
Java_io_github_cvc5_Sort_isRoundingMode(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return static_cast<jboolean>(current->isRoundingMode());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    isBitVector
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Sort_isBitVector(JNIEnv* env,
                                                                jobject,
                                                                jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return static_cast<jboolean>(current->isBitVector());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    isFiniteField
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Sort_isFiniteField(JNIEnv* env,
                                                                  jobject,
                                                                  jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return static_cast<jboolean>(current->isFiniteField());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    isFloatingPoint
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL
Java_io_github_cvc5_Sort_isFloatingPoint(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return static_cast<jboolean>(current->isFloatingPoint());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    isDatatype
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Sort_isDatatype(JNIEnv* env,
                                                               jobject,
                                                               jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return static_cast<jboolean>(current->isDatatype());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    isDatatypeConstructor
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Sort_isDatatypeConstructor(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return static_cast<jboolean>(current->isDatatypeConstructor());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    isDatatypeSelector
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL
Java_io_github_cvc5_Sort_isDatatypeSelector(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return static_cast<jboolean>(current->isDatatypeSelector());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    isDatatypeTester
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL
Java_io_github_cvc5_Sort_isDatatypeTester(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return static_cast<jboolean>(current->isDatatypeTester());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    isDatatypeUpdater
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL
Java_io_github_cvc5_Sort_isDatatypeUpdater(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return static_cast<jboolean>(current->isDatatypeUpdater());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    isFunction
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Sort_isFunction(JNIEnv* env,
                                                               jobject,
                                                               jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return static_cast<jboolean>(current->isFunction());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    isPredicate
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Sort_isPredicate(JNIEnv* env,
                                                                jobject,
                                                                jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return static_cast<jboolean>(current->isPredicate());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    isTuple
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Sort_isTuple(JNIEnv* env,
                                                            jobject,
                                                            jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return static_cast<jboolean>(current->isTuple());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    isRecord
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Sort_isRecord(JNIEnv* env,
                                                             jobject,
                                                             jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return static_cast<jboolean>(current->isRecord());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    isArray
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Sort_isArray(JNIEnv* env,
                                                            jobject,
                                                            jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return static_cast<jboolean>(current->isArray());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    isSet
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Sort_isSet(JNIEnv* env,
                                                          jobject,
                                                          jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return static_cast<jboolean>(current->isSet());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    isBag
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Sort_isBag(JNIEnv* env,
                                                          jobject,
                                                          jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return static_cast<jboolean>(current->isBag());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    isSequence
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Sort_isSequence(JNIEnv* env,
                                                               jobject,
                                                               jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return static_cast<jboolean>(current->isSequence());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    isAbstract
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Sort_isAbstract(JNIEnv* env,
                                                               jobject,
                                                               jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return static_cast<jboolean>(current->isAbstract());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    isUninterpretedSort
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Sort_isUninterpretedSort(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return static_cast<jboolean>(current->isUninterpretedSort());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    isUninterpretedSortConstructor
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL
Java_io_github_cvc5_Sort_isUninterpretedSortConstructor(JNIEnv* env,
                                                        jobject,
                                                        jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return static_cast<jboolean>(current->isUninterpretedSortConstructor());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    isInstantiated
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL
Java_io_github_cvc5_Sort_isInstantiated(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return static_cast<jboolean>(current->isInstantiated());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    getInstantiatedParameters
 * Signature: (J)[J
 */
JNIEXPORT jlongArray JNICALL Java_io_github_cvc5_Sort_getInstantiatedParameters(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  std::vector<Sort> sorts = current->getInstantiatedParameters();
  std::vector<jlong> sortPointers(sorts.size());
  for (size_t i = 0; i < sorts.size(); i++)
  {
    sortPointers[i] = reinterpret_cast<jlong>(new Sort(sorts[i]));
  }
  jlongArray ret = env->NewLongArray(sorts.size());
  env->SetLongArrayRegion(ret, 0, sorts.size(), sortPointers.data());
  return ret;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    getUninterpretedSortConstructor
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_Sort_getUninterpretedSortConstructor(JNIEnv* env,
                                                         jobject,
                                                         jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  Sort* retPointer = new Sort(current->getUninterpretedSortConstructor());
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    getDatatype
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Sort_getDatatype(JNIEnv* env,
                                                             jobject,
                                                             jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  Datatype* retPointer = new Datatype(current->getDatatype());
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    instantiate
 * Signature: (J[J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Sort_instantiate(
    JNIEnv* env, jobject, jlong pointer, jlongArray paramsPointers)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  // get the size of params pointers
  jsize size = env->GetArrayLength(paramsPointers);
  // allocate buffer for the long array
  jlong* buffer = new jlong[size];
  // copy java array to the buffer
  env->GetLongArrayRegion(paramsPointers, 0, size, buffer);
  // copy the terms into a vector
  std::vector<Sort> params;
  for (jsize i = 0; i < size; i++)
  {
    Sort* sort = reinterpret_cast<Sort*>(buffer[i]);
    params.push_back(*sort);
  }
  // free the buffer memory
  delete[] buffer;

  Sort* retPointer = new Sort(current->instantiate(params));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    substitute
 * Signature: (JJJ)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_Sort_substitute__JJJ(JNIEnv* env,
                                         jobject,
                                         jlong pointer,
                                         jlong sortPointer,
                                         jlong replacementPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  Sort* sort = reinterpret_cast<Sort*>(sortPointer);
  Sort* replacement = reinterpret_cast<Sort*>(replacementPointer);
  Sort* retPointer = new Sort(current->substitute(*sort, *replacement));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    substitute
 * Signature: (J[J[J)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_Sort_substitute__J_3J_3J(JNIEnv* env,
                                             jobject,
                                             jlong pointer,
                                             jlongArray sortPointers,
                                             jlongArray replacementPointers)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  // get the size of pointers
  jsize sortsSize = env->GetArrayLength(sortPointers);
  jsize replacementsSize = env->GetArrayLength(replacementPointers);
  // allocate buffer for the long array
  jlong* sortsBuffer = new jlong[sortsSize];
  jlong* replacementsBuffer = new jlong[replacementsSize];
  // copy java array to the buffer
  env->GetLongArrayRegion(sortPointers, 0, sortsSize, sortsBuffer);
  env->GetLongArrayRegion(
      replacementPointers, 0, replacementsSize, replacementsBuffer);
  // copy the terms into a vector
  std::vector<Sort> sorts;
  for (jsize i = 0; i < sortsSize; i++)
  {
    Sort* sort = reinterpret_cast<Sort*>(sortsBuffer[i]);
    sorts.push_back(*sort);
  }

  std::vector<Sort> replacements;
  for (jsize i = 0; i < replacementsSize; i++)
  {
    Sort* sort = reinterpret_cast<Sort*>(replacementsBuffer[i]);
    replacements.push_back(*sort);
  }

  // free the buffer memory
  delete[] sortsBuffer;
  delete[] replacementsBuffer;

  Sort* retPointer = new Sort(current->substitute(sorts, replacements));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    toString
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_io_github_cvc5_Sort_toString(JNIEnv* env,
                                                            jobject,
                                                            jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return env->NewStringUTF(current->toString().c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    getDatatypeConstructorArity
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_io_github_cvc5_Sort_getDatatypeConstructorArity(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return static_cast<jint>(current->getDatatypeConstructorArity());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    getDatatypeConstructorDomainSorts
 * Signature: (J)[J
 */
JNIEXPORT jlongArray JNICALL
Java_io_github_cvc5_Sort_getDatatypeConstructorDomainSorts(JNIEnv* env,
                                                           jobject,
                                                           jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  std::vector<Sort> sorts = current->getDatatypeConstructorDomainSorts();
  std::vector<jlong> sortPointers(sorts.size());
  for (size_t i = 0; i < sorts.size(); i++)
  {
    sortPointers[i] = reinterpret_cast<jlong>(new Sort(sorts[i]));
  }
  jlongArray ret = env->NewLongArray(sorts.size());
  env->SetLongArrayRegion(ret, 0, sorts.size(), sortPointers.data());
  return ret;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    getDatatypeConstructorCodomainSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_Sort_getDatatypeConstructorCodomainSort(JNIEnv* env,
                                                            jobject,
                                                            jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  Sort* retPointer = new Sort(current->getDatatypeConstructorCodomainSort());
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    getDatatypeSelectorDomainSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Sort_getDatatypeSelectorDomainSort(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  Sort* retPointer = new Sort(current->getDatatypeSelectorDomainSort());
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    getDatatypeSelectorCodomainSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_Sort_getDatatypeSelectorCodomainSort(JNIEnv* env,
                                                         jobject,
                                                         jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  Sort* retPointer = new Sort(current->getDatatypeSelectorCodomainSort());
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    getDatatypeTesterDomainSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Sort_getDatatypeTesterDomainSort(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  Sort* retPointer = new Sort(current->getDatatypeTesterDomainSort());
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    getDatatypeTesterCodomainSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Sort_getDatatypeTesterCodomainSort(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  Sort* retPointer = new Sort(current->getDatatypeTesterCodomainSort());
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    getFunctionArity
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_io_github_cvc5_Sort_getFunctionArity(JNIEnv* env,
                                                                 jobject,
                                                                 jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return static_cast<jint>(current->getFunctionArity());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    getFunctionDomainSorts
 * Signature: (J)[J
 */
JNIEXPORT jlongArray JNICALL Java_io_github_cvc5_Sort_getFunctionDomainSorts(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  std::vector<Sort> sorts = current->getFunctionDomainSorts();
  std::vector<jlong> sortPointers(sorts.size());
  for (size_t i = 0; i < sorts.size(); i++)
  {
    sortPointers[i] = reinterpret_cast<jlong>(new Sort(sorts[i]));
  }
  jlongArray ret = env->NewLongArray(sorts.size());
  env->SetLongArrayRegion(ret, 0, sorts.size(), sortPointers.data());
  return ret;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    getFunctionCodomainSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Sort_getFunctionCodomainSort(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  Sort* retPointer = new Sort(current->getFunctionCodomainSort());
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    getArrayIndexSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_Sort_getArrayIndexSort(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  Sort* retPointer = new Sort(current->getArrayIndexSort());
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    getArrayElementSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Sort_getArrayElementSort(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  Sort* retPointer = new Sort(current->getArrayElementSort());
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    getSetElementSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_Sort_getSetElementSort(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  Sort* retPointer = new Sort(current->getSetElementSort());
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    getBagElementSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_Sort_getBagElementSort(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  Sort* retPointer = new Sort(current->getBagElementSort());
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    getSequenceElementSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Sort_getSequenceElementSort(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  Sort* retPointer = new Sort(current->getSequenceElementSort());
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    getAbstractedKind
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_io_github_cvc5_Sort_getAbstractedKind(JNIEnv* env,
                                                                  jobject,
                                                                  jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return static_cast<jint>(current->getAbstractedKind());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    getUninterpretedSortConstructorArity
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL
Java_io_github_cvc5_Sort_getUninterpretedSortConstructorArity(JNIEnv* env,
                                                              jobject,
                                                              jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return static_cast<jint>(current->getUninterpretedSortConstructorArity());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    getBitVectorSize
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_io_github_cvc5_Sort_getBitVectorSize(JNIEnv* env,
                                                                 jobject,
                                                                 jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return static_cast<jint>(current->getBitVectorSize());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    getFiniteFieldSize
 * Signature: (J)I
 */
JNIEXPORT jstring JNICALL Java_io_github_cvc5_Sort_getFiniteFieldSize(JNIEnv* env,
                                                                      jobject,
                                                                      jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return env->NewStringUTF(current->getFiniteFieldSize().c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    getFloatingPointExponentSize
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_io_github_cvc5_Sort_getFloatingPointExponentSize(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return static_cast<jint>(current->getFloatingPointExponentSize());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    getFloatingPointSignificandSize
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_io_github_cvc5_Sort_getFloatingPointSignificandSize(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return static_cast<jint>(current->getFloatingPointSignificandSize());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    getDatatypeArity
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_io_github_cvc5_Sort_getDatatypeArity(JNIEnv* env,
                                                                 jobject,
                                                                 jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return static_cast<jint>(current->getDatatypeArity());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    getTupleLength
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_io_github_cvc5_Sort_getTupleLength(JNIEnv* env,
                                                               jobject,
                                                               jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  return static_cast<jint>(current->getTupleLength());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Sort
 * Method:    getTupleSorts
 * Signature: (J)[J
 */
JNIEXPORT jlongArray JNICALL
Java_io_github_cvc5_Sort_getTupleSorts(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = reinterpret_cast<Sort*>(pointer);
  std::vector<Sort> sorts = current->getTupleSorts();
  std::vector<jlong> sortPointers(sorts.size());
  for (size_t i = 0; i < sorts.size(); i++)
  {
    sortPointers[i] = reinterpret_cast<jlong>(new Sort(sorts[i]));
  }
  jlongArray ret = env->NewLongArray(sorts.size());
  env->SetLongArrayRegion(ret, 0, sorts.size(), sortPointers.data());
  return ret;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}
