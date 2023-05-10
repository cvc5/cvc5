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
#include "io_github_cvc5_Op.h"

using namespace cvc5;

/*
 * Class:     io_github_cvc5_Op
 * Method:    getNullOp
 * Signature: ()J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Op_getNullOp(JNIEnv* env, jclass)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Op* ret = new Op();
  return reinterpret_cast<jlong>(ret);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Op
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_io_github_cvc5_Op_deletePointer(JNIEnv*,
                                                            jobject,
                                                            jlong pointer)
{
  delete reinterpret_cast<Op*>(pointer);
}

/*
 * Class:     io_github_cvc5_Op
 * Method:    equals
 * Signature: (JJ)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Op_equals(JNIEnv* env,
                                                         jobject,
                                                         jlong pointer1,
                                                         jlong pointer2)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Op* op1 = reinterpret_cast<Op*>(pointer1);
  Op* op2 = reinterpret_cast<Op*>(pointer2);
  // We compare the actual operators, not their pointers.
  return static_cast<jboolean>(*op1 == *op2);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     io_github_cvc5_Op
 * Method:    getKind
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_io_github_cvc5_Op_getKind(JNIEnv* env,
                                                      jobject,
                                                      jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Op* current = reinterpret_cast<Op*>(pointer);
  return static_cast<jboolean>(current->getKind());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Op
 * Method:    isNull
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Op_isNull(JNIEnv* env,
                                                         jobject,
                                                         jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Op* current = reinterpret_cast<Op*>(pointer);
  return static_cast<jboolean>(current->isNull());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     io_github_cvc5_Op
 * Method:    isIndexed
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Op_isIndexed(JNIEnv* env,
                                                            jobject,
                                                            jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Op* current = reinterpret_cast<Op*>(pointer);
  return static_cast<jboolean>(current->isIndexed());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, false);
}

/*
 * Class:     io_github_cvc5_Op
 * Method:    getNumIndices
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_io_github_cvc5_Op_getNumIndices(JNIEnv* env,
                                                            jobject,
                                                            jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Op* current = reinterpret_cast<Op*>(pointer);
  return static_cast<jint>(current->getNumIndices());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Op
 * Method:    get
 * Signature: (JI)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Op_get(JNIEnv* env,
                                                   jobject,
                                                   jlong pointer,
                                                   jint i)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Op* current = reinterpret_cast<Op*>(pointer);
  Term* ret = new Term((*current)[static_cast<size_t>(i)]);
  return reinterpret_cast<jlong>(ret);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Op
 * Method:    toString
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_io_github_cvc5_Op_toString(JNIEnv* env,
                                                          jobject,
                                                          jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Op* current = reinterpret_cast<Op*>(pointer);
  return env->NewStringUTF(current->toString().c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}
