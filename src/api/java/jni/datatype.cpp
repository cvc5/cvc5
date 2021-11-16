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
#include "io_github_cvc5_api_Datatype.h"

using namespace cvc5::api;

/*
 * Class:     io_github_cvc5_api_Datatype
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_io_github_cvc5_api_Datatype_deletePointer(
    JNIEnv* env, jobject, jlong pointer)
{
  delete ((Datatype*)pointer);
}

/*
 * Class:     io_github_cvc5_api_Datatype
 * Method:    getConstructor
 * Signature: (JI)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_api_Datatype_getConstructor__JI(
    JNIEnv* env, jobject, jlong pointer, jint idx)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Datatype* current = (Datatype*)pointer;
  DatatypeConstructor* retPointer =
      new DatatypeConstructor(current->operator[](idx));
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_api_Datatype
 * Method:    getConstructor
 * Signature: (JLjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_api_Datatype_getConstructor__JLjava_lang_String_2(
    JNIEnv* env, jobject, jlong pointer, jstring jName)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Datatype* current = (Datatype*)pointer;
  const char* s = env->GetStringUTFChars(jName, nullptr);
  std::string cName(s);
  DatatypeConstructor* retPointer =
      new DatatypeConstructor(current->operator[](cName));
  env->ReleaseStringUTFChars(jName, s);
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_api_Datatype
 * Method:    getConstructorTerm
 * Signature: (JLjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_api_Datatype_getConstructorTerm(
    JNIEnv* env, jobject, jlong pointer, jstring jName)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Datatype* current = (Datatype*)pointer;
  const char* s = env->GetStringUTFChars(jName, nullptr);
  std::string cName(s);
  Term* retPointer = new Term(current->getConstructorTerm(cName));
  env->ReleaseStringUTFChars(jName, s);
  return ((jlong)retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_api_Datatype
 * Method:    getName
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL
Java_io_github_cvc5_api_Datatype_getName(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Datatype* current = (Datatype*)pointer;
  return env->NewStringUTF(current->getName().c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_api_Datatype
 * Method:    getNumConstructors
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_io_github_cvc5_api_Datatype_getNumConstructors(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Datatype* current = (Datatype*)pointer;
  return (jint)current->getNumConstructors();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_api_Datatype
 * Method:    isParametric
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_api_Datatype_isParametric(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Datatype* current = (Datatype*)pointer;
  return (jboolean)current->isParametric();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_api_Datatype
 * Method:    isCodatatype
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_api_Datatype_isCodatatype(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Datatype* current = (Datatype*)pointer;
  return (jboolean)current->isCodatatype();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_api_Datatype
 * Method:    isTuple
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL
Java_io_github_cvc5_api_Datatype_isTuple(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Datatype* current = (Datatype*)pointer;
  return (jboolean)current->isTuple();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_api_Datatype
 * Method:    isRecord
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL
Java_io_github_cvc5_api_Datatype_isRecord(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Datatype* current = (Datatype*)pointer;
  return (jboolean)current->isRecord();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_api_Datatype
 * Method:    isFinite
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL
Java_io_github_cvc5_api_Datatype_isFinite(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Datatype* current = (Datatype*)pointer;
  return (jboolean)current->isFinite();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_api_Datatype
 * Method:    isWellFounded
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_api_Datatype_isWellFounded(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Datatype* current = (Datatype*)pointer;
  return (jboolean)current->isWellFounded();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_api_Datatype
 * Method:    hasNestedRecursion
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_api_Datatype_hasNestedRecursion(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Datatype* current = (Datatype*)pointer;
  return (jboolean)current->hasNestedRecursion();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_api_Datatype
 * Method:    isNull
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL
Java_io_github_cvc5_api_Datatype_isNull(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Datatype* current = (Datatype*)pointer;
  return (jboolean)current->isNull();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_api_Datatype
 * Method:    toString
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL
Java_io_github_cvc5_api_Datatype_toString(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Datatype* current = (Datatype*)pointer;
  return env->NewStringUTF(current->toString().c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}
