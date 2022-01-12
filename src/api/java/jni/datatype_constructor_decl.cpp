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
#include "io_github_cvc5_api_DatatypeConstructorDecl.h"

using namespace cvc5::api;

/*
 * Class:     io_github_cvc5_api_DatatypeConstructorDecl
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL
Java_io_github_cvc5_api_DatatypeConstructorDecl_deletePointer(JNIEnv*,
                                                              jobject,
                                                              jlong pointer)
{
  delete ((DatatypeConstructorDecl*)pointer);
}

/*
 * Class:     io_github_cvc5_api_DatatypeConstructorDecl
 * Method:    addSelector
 * Signature: (JLjava/lang/String;J)V
 */
JNIEXPORT void JNICALL
Java_io_github_cvc5_api_DatatypeConstructorDecl_addSelector(
    JNIEnv* env, jobject, jlong pointer, jstring jName, jlong sortPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeConstructorDecl* current = (DatatypeConstructorDecl*)pointer;
  const char* s = env->GetStringUTFChars(jName, nullptr);
  std::string cName(s);
  Sort* sort = (Sort*)sortPointer;
  current->addSelector(cName, *sort);
  env->ReleaseStringUTFChars(jName, s);
  CVC5_JAVA_API_TRY_CATCH_END(env);
}

/*
 * Class:     io_github_cvc5_api_DatatypeConstructorDecl
 * Method:    addSelectorSelf
 * Signature: (JLjava/lang/String;)V
 */
JNIEXPORT void JNICALL
Java_io_github_cvc5_api_DatatypeConstructorDecl_addSelectorSelf(JNIEnv* env,
                                                                jobject,
                                                                jlong pointer,
                                                                jstring jName)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeConstructorDecl* current = (DatatypeConstructorDecl*)pointer;
  const char* s = env->GetStringUTFChars(jName, nullptr);
  std::string cName(s);
  current->addSelectorSelf(cName);
  env->ReleaseStringUTFChars(jName, s);
  CVC5_JAVA_API_TRY_CATCH_END(env);
}

/*
 * Class:     io_github_cvc5_api_DatatypeConstructorDecl
 * Method:    isNull
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL
Java_io_github_cvc5_api_DatatypeConstructorDecl_isNull(JNIEnv* env,
                                                       jobject,
                                                       jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeConstructorDecl* current = (DatatypeConstructorDecl*)pointer;
  return (jboolean)current->isNull();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     io_github_cvc5_api_DatatypeConstructorDecl
 * Method:    toString
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL
Java_io_github_cvc5_api_DatatypeConstructorDecl_toString(JNIEnv* env,
                                                         jobject,
                                                         jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeConstructorDecl* current = (DatatypeConstructorDecl*)pointer;
  return env->NewStringUTF(current->toString().c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}
