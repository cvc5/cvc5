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

#include "cvc5_Sort.h"

#include "api/cpp/cvc5.h"
#include "cvc5JavaApi.h"

using namespace cvc5::api;

/*
 * Class:     cvc5_Sort
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_cvc5_Sort_deletePointer(JNIEnv*,
                                                    jclass,
                                                    jlong pointer)
{
  delete ((Sort*)pointer);
}

/*
 * Class:     cvc5_Sort
 * Method:    equals
 * Signature: (JJ)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_equals(JNIEnv* env,
                                                 jobject,
                                                 jlong pointer1,
                                                 jlong pointer2)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort sort1 = *(Sort*)pointer1;
  Sort sort2 = *(Sort*)pointer2;
  return (jboolean)(sort1 == sort2);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Sort
 * Method:    compareTo
 * Signature: (JJ)I
 */
JNIEXPORT jint JNICALL Java_cvc5_Sort_compareTo(JNIEnv* env,
                                                jobject,
                                                jlong pointer1,
                                                jlong pointer2)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* sort1 = (Sort*)pointer1;
  Sort* sort2 = (Sort*)pointer2;
  if (*sort1 < *sort2)
  {
    return (jint)-1;
  }
  if (*sort1 == *sort2)
  {
    return 0;
  }
  return (jint)1;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Sort
 * Method:    isNull
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isNull(JNIEnv* env,
                                                 jobject,
                                                 jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return (jboolean)current->isNull();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Sort
 * Method:    isBoolean
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isBoolean(JNIEnv* env,
                                                    jobject,
                                                    jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return (jboolean)current->isBoolean();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Sort
 * Method:    isInteger
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isInteger(JNIEnv* env,
                                                    jobject,
                                                    jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return (jboolean)current->isInteger();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Sort
 * Method:    isReal
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isReal(JNIEnv* env,
                                                 jobject,
                                                 jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return (jboolean)current->isReal();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Sort
 * Method:    isString
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isString(JNIEnv* env,
                                                   jobject,
                                                   jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return (jboolean)current->isString();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Sort
 * Method:    isRegExp
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isRegExp(JNIEnv* env,
                                                   jobject,
                                                   jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return (jboolean)current->isRegExp();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Sort
 * Method:    isRoundingMode
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isRoundingMode(JNIEnv* env,
                                                         jobject,
                                                         jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return (jboolean)current->isRoundingMode();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Sort
 * Method:    isBitVector
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isBitVector(JNIEnv* env,
                                                      jobject,
                                                      jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return (jboolean)current->isBitVector();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Sort
 * Method:    isFloatingPoint
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isFloatingPoint(JNIEnv* env,
                                                          jobject,
                                                          jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return (jboolean)current->isFloatingPoint();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Sort
 * Method:    isDatatype
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isDatatype(JNIEnv* env,
                                                     jobject,
                                                     jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return (jboolean)current->isDatatype();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Sort
 * Method:    isParametricDatatype
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isParametricDatatype(JNIEnv* env,
                                                               jobject,
                                                               jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return (jboolean)current->isParametricDatatype();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Sort
 * Method:    isConstructor
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isConstructor(JNIEnv* env,
                                                        jobject,
                                                        jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return (jboolean)current->isConstructor();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Sort
 * Method:    isSelector
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isSelector(JNIEnv* env,
                                                     jobject,
                                                     jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return (jboolean)current->isSelector();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Sort
 * Method:    isTester
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isTester(JNIEnv* env,
                                                   jobject,
                                                   jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return (jboolean)current->isTester();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Sort
 * Method:    isUpdater
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isUpdater(JNIEnv* env,
                                                    jobject,
                                                    jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return (jboolean)current->isUpdater();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Sort
 * Method:    isFunction
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isFunction(JNIEnv* env,
                                                     jobject,
                                                     jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return (jboolean)current->isFunction();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Sort
 * Method:    isPredicate
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isPredicate(JNIEnv* env,
                                                      jobject,
                                                      jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return (jboolean)current->isPredicate();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Sort
 * Method:    isTuple
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isTuple(JNIEnv* env,
                                                  jobject,
                                                  jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return (jboolean)current->isTuple();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Sort
 * Method:    isRecord
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isRecord(JNIEnv* env,
                                                   jobject,
                                                   jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return (jboolean)current->isRecord();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Sort
 * Method:    isArray
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isArray(JNIEnv* env,
                                                  jobject,
                                                  jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return (jboolean)current->isArray();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Sort
 * Method:    isSet
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isSet(JNIEnv* env,
                                                jobject,
                                                jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return (jboolean)current->isSet();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Sort
 * Method:    isBag
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isBag(JNIEnv* env,
                                                jobject,
                                                jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return (jboolean)current->isBag();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Sort
 * Method:    isSequence
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isSequence(JNIEnv* env,
                                                     jobject,
                                                     jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return (jboolean)current->isSequence();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Sort
 * Method:    isUninterpretedSort
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isUninterpretedSort(JNIEnv* env,
                                                              jobject,
                                                              jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return (jboolean)current->isUninterpretedSort();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Sort
 * Method:    isSortConstructor
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isSortConstructor(JNIEnv* env,
                                                            jobject,
                                                            jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return (jboolean)current->isSortConstructor();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Sort
 * Method:    isFirstClass
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isFirstClass(JNIEnv* env,
                                                       jobject,
                                                       jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return (jboolean)current->isFirstClass();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Sort
 * Method:    isFunctionLike
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isFunctionLike(JNIEnv* env,
                                                         jobject,
                                                         jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return (jboolean)current->isFunctionLike();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Sort
 * Method:    isSubsortOf
 * Signature: (JJ)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isSubsortOf(JNIEnv* env,
                                                      jobject,
                                                      jlong pointer,
                                                      jlong sortPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  Sort* sort = (Sort*)sortPointer;
  return (jboolean)current->isSubsortOf(*sort);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Sort
 * Method:    isComparableTo
 * Signature: (JJ)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isComparableTo(JNIEnv* env,
                                                         jobject,
                                                         jlong pointer,
                                                         jlong sortPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  Sort* sort = (Sort*)sortPointer;
  return (jboolean)current->isComparableTo(*sort);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Sort
 * Method:    getDatatype
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Sort_getDatatype(JNIEnv* env,
                                                   jobject,
                                                   jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  Datatype* retPointer = new Datatype(current->getDatatype());
  return ((jlong)retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Sort
 * Method:    instantiate
 * Signature: (J[J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Sort_instantiate(JNIEnv* env,
                                                   jobject,
                                                   jlong pointer,
                                                   jlongArray paramsPointers)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
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
    Sort* sort = (Sort*)buffer[i];
    params.push_back(*sort);
  }
  // free the buffer memory
  delete[] buffer;

  Sort* retPointer = new Sort(current->instantiate(params));
  return ((jlong)retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Sort
 * Method:    substitute
 * Signature: (JJJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Sort_substitute__JJJ(JNIEnv* env,
                                                       jobject,
                                                       jlong pointer,
                                                       jlong sortPointer,
                                                       jlong replacementPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  Sort* sort = (Sort*)sortPointer;
  Sort* replacement = (Sort*)replacementPointer;
  Sort* retPointer = new Sort(current->substitute(*sort, *replacement));
  return ((jlong)retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Sort
 * Method:    substitute
 * Signature: (J[J[J)J
 */
JNIEXPORT jlong JNICALL
Java_cvc5_Sort_substitute__J_3J_3J(JNIEnv* env,
                                   jobject,
                                   jlong pointer,
                                   jlongArray sortPointers,
                                   jlongArray replacementPointers)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
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
    Sort* sort = (Sort*)sortsBuffer[i];
    sorts.push_back(*sort);
  }

  std::vector<Sort> replacements;
  for (jsize i = 0; i < replacementsSize; i++)
  {
    Sort* sort = (Sort*)replacementsBuffer[i];
    replacements.push_back(*sort);
  }

  // free the buffer memory
  delete[] sortsBuffer;
  delete[] replacementsBuffer;

  Sort* retPointer = new Sort(current->substitute(sorts, replacements));
  return ((jlong)retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Sort
 * Method:    toString
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_cvc5_Sort_toString(JNIEnv* env,
                                                  jobject,
                                                  jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return env->NewStringUTF(current->toString().c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     cvc5_Sort
 * Method:    getConstructorArity
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_cvc5_Sort_getConstructorArity(JNIEnv* env,
                                                          jobject,
                                                          jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return (jint)current->getConstructorArity();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Sort
 * Method:    getConstructorDomainSorts
 * Signature: (J)[J
 */
JNIEXPORT jlongArray JNICALL
Java_cvc5_Sort_getConstructorDomainSorts(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  std::vector<Sort> sorts = current->getConstructorDomainSorts();
  std::vector<long> sortPointers(sorts.size());
  for (size_t i = 0; i < sorts.size(); i++)
  {
    sortPointers[i] = (long)new Sort(sorts[i]);
  }
  jlongArray ret = env->NewLongArray(sorts.size());
  env->SetLongArrayRegion(ret, 0, sorts.size(), sortPointers.data());
  return ret;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     cvc5_Sort
 * Method:    getConstructorCodomainSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Sort_getConstructorCodomainSort(JNIEnv* env,
                                                                  jobject,
                                                                  jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  Sort* retPointer = new Sort(current->getConstructorCodomainSort());
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Sort
 * Method:    getSelectorDomainSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Sort_getSelectorDomainSort(JNIEnv* env,
                                                             jobject,
                                                             jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  Sort* retPointer = new Sort(current->getSelectorDomainSort());
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Sort
 * Method:    getSelectorCodomainSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Sort_getSelectorCodomainSort(JNIEnv* env,
                                                               jobject,
                                                               jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  Sort* retPointer = new Sort(current->getSelectorCodomainSort());
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Sort
 * Method:    getTesterDomainSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Sort_getTesterDomainSort(JNIEnv* env,
                                                           jobject,
                                                           jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  Sort* retPointer = new Sort(current->getTesterDomainSort());
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Sort
 * Method:    getTesterCodomainSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Sort_getTesterCodomainSort(JNIEnv* env,
                                                             jobject,
                                                             jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  Sort* retPointer = new Sort(current->getTesterCodomainSort());
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Sort
 * Method:    getFunctionArity
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_cvc5_Sort_getFunctionArity(JNIEnv* env,
                                                       jobject,
                                                       jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return (jint)current->getFunctionArity();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Sort
 * Method:    getFunctionDomainSorts
 * Signature: (J)[J
 */
JNIEXPORT jlongArray JNICALL
Java_cvc5_Sort_getFunctionDomainSorts(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  std::vector<Sort> sorts = current->getFunctionDomainSorts();
  std::vector<long> sortPointers(sorts.size());
  for (size_t i = 0; i < sorts.size(); i++)
  {
    sortPointers[i] = (long)new Sort(sorts[i]);
  }
  jlongArray ret = env->NewLongArray(sorts.size());
  env->SetLongArrayRegion(ret, 0, sorts.size(), sortPointers.data());
  return ret;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     cvc5_Sort
 * Method:    getFunctionCodomainSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Sort_getFunctionCodomainSort(JNIEnv* env,
                                                               jobject,
                                                               jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  Sort* retPointer = new Sort(current->getFunctionCodomainSort());
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Sort
 * Method:    getArrayIndexSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Sort_getArrayIndexSort(JNIEnv* env,
                                                         jobject,
                                                         jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  Sort* retPointer = new Sort(current->getArrayIndexSort());
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Sort
 * Method:    getArrayElementSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Sort_getArrayElementSort(JNIEnv* env,
                                                           jobject,
                                                           jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  Sort* retPointer = new Sort(current->getArrayElementSort());
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Sort
 * Method:    getSetElementSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Sort_getSetElementSort(JNIEnv* env,
                                                         jobject,
                                                         jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  Sort* retPointer = new Sort(current->getSetElementSort());
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Sort
 * Method:    getBagElementSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Sort_getBagElementSort(JNIEnv* env,
                                                         jobject,
                                                         jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  Sort* retPointer = new Sort(current->getBagElementSort());
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Sort
 * Method:    getSequenceElementSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Sort_getSequenceElementSort(JNIEnv* env,
                                                              jobject,
                                                              jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  Sort* retPointer = new Sort(current->getSequenceElementSort());
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Sort
 * Method:    getUninterpretedSortName
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_cvc5_Sort_getUninterpretedSortName(JNIEnv* env,
                                                                  jobject,
                                                                  jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return env->NewStringUTF(current->getUninterpretedSortName().c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     cvc5_Sort
 * Method:    isUninterpretedSortParameterized
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isUninterpretedSortParameterized(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return (jboolean)current->isUninterpretedSortParameterized();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Sort
 * Method:    getUninterpretedSortParamSorts
 * Signature: (J)[J
 */
JNIEXPORT jlongArray JNICALL Java_cvc5_Sort_getUninterpretedSortParamSorts(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  std::vector<Sort> sorts = current->getUninterpretedSortParamSorts();
  std::vector<long> sortPointers(sorts.size());
  for (size_t i = 0; i < sorts.size(); i++)
  {
    sortPointers[i] = (long)new Sort(sorts[i]);
  }
  jlongArray ret = env->NewLongArray(sorts.size());
  env->SetLongArrayRegion(ret, 0, sorts.size(), sortPointers.data());
  return ret;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     cvc5_Sort
 * Method:    getSortConstructorName
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_cvc5_Sort_getSortConstructorName(JNIEnv* env,
                                                                jobject,
                                                                jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return env->NewStringUTF(current->getSortConstructorName().c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     cvc5_Sort
 * Method:    getSortConstructorArity
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_cvc5_Sort_getSortConstructorArity(JNIEnv* env,
                                                              jobject,
                                                              jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return (jint)current->getSortConstructorArity();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Sort
 * Method:    getBVSize
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_cvc5_Sort_getBVSize(JNIEnv* env,
                                                jobject,
                                                jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return (jint)current->getBVSize();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Sort
 * Method:    getFPExponentSize
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_cvc5_Sort_getFPExponentSize(JNIEnv* env,
                                                        jobject,
                                                        jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return (jint)current->getFPExponentSize();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Sort
 * Method:    getFPSignificandSize
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_cvc5_Sort_getFPSignificandSize(JNIEnv* env,
                                                           jobject,
                                                           jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return (jint)current->getFPSignificandSize();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Sort
 * Method:    getDatatypeParamSorts
 * Signature: (J)[J
 */
JNIEXPORT jlongArray JNICALL Java_cvc5_Sort_getDatatypeParamSorts(JNIEnv* env,
                                                                  jobject,
                                                                  jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  std::vector<Sort> sorts = current->getDatatypeParamSorts();
  std::vector<long> sortPointers(sorts.size());
  for (size_t i = 0; i < sorts.size(); i++)
  {
    sortPointers[i] = (long)new Sort(sorts[i]);
  }
  jlongArray ret = env->NewLongArray(sorts.size());
  env->SetLongArrayRegion(ret, 0, sorts.size(), sortPointers.data());
  return ret;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     cvc5_Sort
 * Method:    getDatatypeArity
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_cvc5_Sort_getDatatypeArity(JNIEnv* env,
                                                       jobject,
                                                       jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return (jint)current->getDatatypeArity();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Sort
 * Method:    getTupleLength
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_cvc5_Sort_getTupleLength(JNIEnv* env,
                                                     jobject,
                                                     jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  return (jint)current->getTupleLength();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Sort
 * Method:    getTupleSorts
 * Signature: (J)[J
 */
JNIEXPORT jlongArray JNICALL Java_cvc5_Sort_getTupleSorts(JNIEnv* env,
                                                          jobject,
                                                          jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort* current = (Sort*)pointer;
  std::vector<Sort> sorts = current->getTupleSorts();
  std::vector<long> sortPointers(sorts.size());
  for (size_t i = 0; i < sorts.size(); i++)
  {
    sortPointers[i] = (long)new Sort(sorts[i]);
  }
  jlongArray ret = env->NewLongArray(sorts.size());
  env->SetLongArrayRegion(ret, 0, sorts.size(), sortPointers.data());
  return ret;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}
