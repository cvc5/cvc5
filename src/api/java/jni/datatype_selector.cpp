/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Aina Niemetz, Andres Noetzli
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
#include "io_github_cvc5_DatatypeSelector.h"

using namespace cvc5;

/*
 * Class:     io_github_cvc5_DatatypeSelector
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_io_github_cvc5_DatatypeSelector_deletePointer(
    JNIEnv*, jobject, jlong pointer)
{
  delete ((DatatypeSelector*)pointer);
}

/*
 * Class:     io_github_cvc5_DatatypeSelector
 * Method:    equals
 * Signature: (JJ)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_DatatypeSelector_equals(
    JNIEnv* env, jobject, jlong pointer1, jlong pointer2)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeSelector* sel1 = reinterpret_cast<DatatypeSelector*>(pointer1);
  DatatypeSelector* sel2 = reinterpret_cast<DatatypeSelector*>(pointer2);
  // We compare the actual terms, not their pointers.
  return static_cast<jboolean>(*sel1 == *sel2);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_DatatypeSelector
 * Method:    getName
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_io_github_cvc5_DatatypeSelector_getName(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeSelector* current = (DatatypeSelector*)pointer;
  return env->NewStringUTF(current->getName().c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_DatatypeSelector
 * Method:    getTerm
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_DatatypeSelector_getTerm(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeSelector* current = (DatatypeSelector*)pointer;
  Term* retPointer = new Term(current->getTerm());
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_DatatypeSelector
 * Method:    getUpdaterTerm
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_DatatypeSelector_getUpdaterTerm(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeSelector* current = (DatatypeSelector*)pointer;
  Term* retPointer = new Term(current->getUpdaterTerm());
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_DatatypeSelector
 * Method:    getCodomainSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_DatatypeSelector_getCodomainSort(JNIEnv* env,
                                                         jobject,
                                                         jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeSelector* current = (DatatypeSelector*)pointer;
  Sort* retPointer = new Sort(current->getCodomainSort());
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_DatatypeSelector
 * Method:    isNull
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_DatatypeSelector_isNull(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeSelector* current = (DatatypeSelector*)pointer;
  return (jboolean)current->isNull();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     io_github_cvc5_DatatypeSelector
 * Method:    toString
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_io_github_cvc5_DatatypeSelector_toString(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeSelector* current = (DatatypeSelector*)pointer;
  return env->NewStringUTF(current->toString().c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_DatatypeSelector
 * Method:    hashCode
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_io_github_cvc5_DatatypeSelector_hashCode(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeSelector* result = reinterpret_cast<DatatypeSelector*>(pointer);
  return static_cast<jint>(std::hash<cvc5::DatatypeSelector>()(*result));
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}
