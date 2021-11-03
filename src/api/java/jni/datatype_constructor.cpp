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

#include "api/cpp/cvc5.h"
#include "api_utilities.h"
#include "io_github_cvc5_api_DatatypeConstructor.h"

using namespace cvc5::api;

/*
 * Class:     io_github_cvc5_api_DatatypeConstructor
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL
Java_io_github_cvc5_api_DatatypeConstructor_deletePointer(JNIEnv*,
                                                          jobject,
                                                          jlong pointer)
{
  delete ((DatatypeConstructor*)pointer);
}

/*
 * Class:     io_github_cvc5_api_DatatypeConstructor
 * Method:    getName
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_io_github_cvc5_api_DatatypeConstructor_getName(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeConstructor* current = (DatatypeConstructor*)pointer;
  return env->NewStringUTF(current->getName().c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_api_DatatypeConstructor
 * Method:    getConstructorTerm
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_api_DatatypeConstructor_getConstructorTerm(JNIEnv* env,
                                                               jobject,
                                                               jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeConstructor* current = (DatatypeConstructor*)pointer;
  Term* retPointer = new Term(current->getConstructorTerm());
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_api_DatatypeConstructor
 * Method:    getSpecializedConstructorTerm
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_api_DatatypeConstructor_getSpecializedConstructorTerm(
    JNIEnv* env, jobject, jlong pointer, jlong retSortPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeConstructor* current = (DatatypeConstructor*)pointer;
  Sort* sort = (Sort*)retSortPointer;
  Term* retPointer = new Term(current->getSpecializedConstructorTerm(*sort));
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_api_DatatypeConstructor
 * Method:    getTesterTerm
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_api_DatatypeConstructor_getTesterTerm(JNIEnv* env,
                                                          jobject,
                                                          jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeConstructor* current = (DatatypeConstructor*)pointer;
  Term* retPointer = new Term(current->getTesterTerm());
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_api_DatatypeConstructor
 * Method:    getNumSelectors
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL
Java_io_github_cvc5_api_DatatypeConstructor_getNumSelectors(JNIEnv* env,
                                                            jobject,
                                                            jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeConstructor* current = (DatatypeConstructor*)pointer;
  return (jint)current->getNumSelectors();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_api_DatatypeConstructor
 * Method:    getSelector
 * Signature: (JI)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_api_DatatypeConstructor_getSelector__JI(JNIEnv* env,
                                                            jobject,
                                                            jlong pointer,
                                                            jint index)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeConstructor* current = (DatatypeConstructor*)pointer;
  DatatypeSelector* retPointer =
      new DatatypeSelector(current->operator[]((size_t)index));
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_api_DatatypeConstructor
 * Method:    getSelector
 * Signature: (JLjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_api_DatatypeConstructor_getSelector__JLjava_lang_String_2(
    JNIEnv* env, jobject, jlong pointer, jstring jName)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeConstructor* current = (DatatypeConstructor*)pointer;
  const char* s = env->GetStringUTFChars(jName, nullptr);
  std::string cName(s);
  DatatypeSelector* retPointer =
      new DatatypeSelector(current->operator[](cName));
  env->ReleaseStringUTFChars(jName, s);
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_api_DatatypeConstructor
 * Method:    getSelectorTerm
 * Signature: (JLjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_api_DatatypeConstructor_getSelectorTerm(JNIEnv* env,
                                                            jobject,
                                                            jlong pointer,
                                                            jstring jName)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeConstructor* current = (DatatypeConstructor*)pointer;
  const char* s = env->GetStringUTFChars(jName, nullptr);
  std::string cName(s);
  Term* retPointer = new Term(current->getSelectorTerm(cName));
  env->ReleaseStringUTFChars(jName, s);
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_api_DatatypeConstructor
 * Method:    isNull
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_api_DatatypeConstructor_isNull(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeConstructor* current = (DatatypeConstructor*)pointer;
  return (jboolean)current->isNull();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     io_github_cvc5_api_DatatypeConstructor
 * Method:    toString
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_io_github_cvc5_api_DatatypeConstructor_toString(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeConstructor* current = (DatatypeConstructor*)pointer;
  return env->NewStringUTF(current->toString().c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}
