/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andres Noetzli, Mathias Preiner
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
#include "io_github_cvc5_DatatypeDecl.h"

using namespace cvc5;

/*
 * Class:     io_github_cvc5_DatatypeDecl
 * Method:    getNullDatatypeDecl
 * Signature: ()J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_DatatypeDecl_getNullDatatypeDecl(JNIEnv* env, jclass)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeDecl* ret = new DatatypeDecl();
  return reinterpret_cast<jlong>(ret);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_DatatypeDecl
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL
Java_io_github_cvc5_DatatypeDecl_deletePointer(JNIEnv*, jobject, jlong pointer)
{
  delete ((DatatypeDecl*)pointer);
}

/*
 * Class:     io_github_cvc5_DatatypeDecl
 * Method:    addConstructor
 * Signature: (JJ)V
 */
JNIEXPORT void JNICALL Java_io_github_cvc5_DatatypeDecl_addConstructor(
    JNIEnv* env, jobject, jlong pointer, jlong declPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeDecl* current = (DatatypeDecl*)pointer;
  DatatypeConstructorDecl* decl = (DatatypeConstructorDecl*)declPointer;
  current->addConstructor(*decl);
  CVC5_JAVA_API_TRY_CATCH_END(env);
}

/*
 * Class:     io_github_cvc5_DatatypeDecl
 * Method:    getNumConstructors
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_io_github_cvc5_DatatypeDecl_getNumConstructors(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeDecl* current = (DatatypeDecl*)pointer;
  return (jint)current->getNumConstructors();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_DatatypeDecl
 * Method:    isParametric
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_DatatypeDecl_isParametric(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeDecl* current = (DatatypeDecl*)pointer;
  return (jboolean)current->isParametric();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     io_github_cvc5_DatatypeDecl
 * Method:    isNull
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL
Java_io_github_cvc5_DatatypeDecl_isNull(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeDecl* current = (DatatypeDecl*)pointer;
  return (jboolean)current->isNull();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     io_github_cvc5_DatatypeDecl
 * Method:    toString
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL
Java_io_github_cvc5_DatatypeDecl_toString(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeDecl* current = (DatatypeDecl*)pointer;
  return env->NewStringUTF(current->toString().c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_DatatypeDecl
 * Method:    getName
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL
Java_io_github_cvc5_DatatypeDecl_getName(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeDecl* current = (DatatypeDecl*)pointer;
  return env->NewStringUTF(current->getName().c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}
