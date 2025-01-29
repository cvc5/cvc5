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
#include "io_github_cvc5_DatatypeConstructorDecl.h"

using namespace cvc5;

/*
 * Class:     io_github_cvc5_DatatypeConstructorDecl
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL
Java_io_github_cvc5_DatatypeConstructorDecl_deletePointer(JNIEnv*,
                                                              jobject,
                                                              jlong pointer)
{
  delete ((DatatypeConstructorDecl*)pointer);
}

/*
 * Class:     io_github_cvc5_DatatypeConstructorDecl
 * Method:    equals
 * Signature: (JJ)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_DatatypeConstructorDecl_equals(
    JNIEnv* env, jobject, jlong pointer1, jlong pointer2)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeConstructorDecl* cons1 =
      reinterpret_cast<DatatypeConstructorDecl*>(pointer1);
  DatatypeConstructorDecl* cons2 =
      reinterpret_cast<DatatypeConstructorDecl*>(pointer2);
  // We compare the actual terms, not their pointers.
  return static_cast<jboolean>(*cons1 == *cons2);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_DatatypeConstructorDecl
 * Method:    addSelector
 * Signature: (JLjava/lang/String;J)V
 */
JNIEXPORT void JNICALL
Java_io_github_cvc5_DatatypeConstructorDecl_addSelector(
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
 * Class:     io_github_cvc5_DatatypeConstructorDecl
 * Method:    addSelectorSelf
 * Signature: (JLjava/lang/String;)V
 */
JNIEXPORT void JNICALL
Java_io_github_cvc5_DatatypeConstructorDecl_addSelectorSelf(JNIEnv* env,
                                                                jobject,
                                                                jlong pointer,
                                                                jstring jName)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeConstructorDecl* current = (DatatypeConstructorDecl*)pointer;
  const char* s = env->GetStringUTFChars(jName, nullptr);
  std::string sName(s);
  current->addSelectorSelf(sName);
  env->ReleaseStringUTFChars(jName, s);
  CVC5_JAVA_API_TRY_CATCH_END(env);
}

/*
 * Class:     io_github_cvc5_DatatypeConstructorDecl
 * Method:    addSelectorUnresolved
 * Signature: (JLjava/lang/String;Ljava/lang/String;)V
 */
JNIEXPORT void JNICALL
Java_io_github_cvc5_DatatypeConstructorDecl_addSelectorUnresolved(
    JNIEnv* env,
    jobject,
    jlong pointer,
    jstring jName,
    jstring jUnresDataypeName)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeConstructorDecl* current = (DatatypeConstructorDecl*)pointer;
  const char* s = env->GetStringUTFChars(jName, nullptr);
  std::string sName(s);
  const char* du = env->GetStringUTFChars(jUnresDataypeName, nullptr);
  std::string duName(du);
  current->addSelectorUnresolved(sName, duName);
  env->ReleaseStringUTFChars(jUnresDataypeName, du);
  env->ReleaseStringUTFChars(jName, s);
  CVC5_JAVA_API_TRY_CATCH_END(env);
}

/*
 * Class:     io_github_cvc5_DatatypeConstructorDecl
 * Method:    isNull
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL
Java_io_github_cvc5_DatatypeConstructorDecl_isNull(JNIEnv* env,
                                                       jobject,
                                                       jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeConstructorDecl* current = (DatatypeConstructorDecl*)pointer;
  return (jboolean)current->isNull();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     io_github_cvc5_DatatypeConstructorDecl
 * Method:    toString
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL
Java_io_github_cvc5_DatatypeConstructorDecl_toString(JNIEnv* env,
                                                         jobject,
                                                         jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeConstructorDecl* current = (DatatypeConstructorDecl*)pointer;
  return env->NewStringUTF(current->toString().c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_DatatypeConstructorDecl
 * Method:    hashCode
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_io_github_cvc5_DatatypeConstructorDecl_hashCode(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeConstructorDecl* result =
      reinterpret_cast<DatatypeConstructorDecl*>(pointer);
  return static_cast<jint>(std::hash<cvc5::DatatypeConstructorDecl>()(*result));
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}
