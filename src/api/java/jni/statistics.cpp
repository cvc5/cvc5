/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andres Noetzli, Gereon Kremer
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

#include <sstream>

#include "api_utilities.h"
#include "io_github_cvc5_Statistics.h"

using namespace cvc5;

/*
 * Class:     io_github_cvc5_Statistics
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_io_github_cvc5_Statistics_deletePointer(
    JNIEnv*, jobject, jlong pointer)
{
  delete reinterpret_cast<Statistics*>(pointer);
}

/*
 * Class:     io_github_cvc5_Statistics
 * Method:    toString
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL
Java_io_github_cvc5_Statistics_toString(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;

  Statistics* current = reinterpret_cast<Statistics*>(pointer);
  std::stringstream ss;
  ss << *current;
  return env->NewStringUTF(ss.str().c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_Statistics
 * Method:    get
 * Signature: (JLjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Statistics_get(JNIEnv* env,
                                                               jobject,
                                                               jlong pointer,
                                                               jstring jName)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Statistics* current = reinterpret_cast<Statistics*>(pointer);
  const char* s = env->GetStringUTFChars(jName, nullptr);
  std::string cName(s);
  Stat* retPointer = new Stat(current->get(cName));
  env->ReleaseStringUTFChars(jName, s);
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Statistics
 * Method:    getIterator
 * Signature: (JZZ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Statistics_getIteratorOpts(
    JNIEnv* env, jobject, jlong pointer, jboolean internal, jboolean defaulted)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Statistics* current = reinterpret_cast<Statistics*>(pointer);
  Statistics::iterator* it =
      new Statistics::iterator(current->begin(internal, defaulted));
  return reinterpret_cast<jlong>(it);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Statistics
 * Method:    getIterator
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Statistics_getIterator(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Statistics* current = reinterpret_cast<Statistics*>(pointer);
  Statistics::iterator* it =
      new Statistics::iterator(current->begin());
  return reinterpret_cast<jlong>(it);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Statistics
 * Method:    hasNext
 * Signature: (JJ)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Statistics_hasNext(
    JNIEnv* env, jobject, jlong pointer, jlong iteratorPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Statistics* current = reinterpret_cast<Statistics*>(pointer);
  Statistics::iterator it =
      *reinterpret_cast<Statistics::iterator*>(iteratorPointer);
  return static_cast<jboolean>(it != current->end());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Statistics
 * Method:    getNext
 * Signature: (JJ)Lio/github/cvc5/Pair;
 */
JNIEXPORT jobject JNICALL Java_io_github_cvc5_Statistics_getNext(
    JNIEnv* env, jobject, jlong, jlong iteratorPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Statistics::iterator it =
      *reinterpret_cast<Statistics::iterator*>(iteratorPointer);
  std::string cName = it->first;
  jstring jName = env->NewStringUTF(cName.c_str());
  Stat* stat = new Stat(it->second);
  jlong statPointer = reinterpret_cast<jlong>(stat);

  // Long longObject = new Long(statPointer)
  jclass longClass = env->FindClass("Ljava/lang/Long;");
  jmethodID longConstructor = env->GetMethodID(longClass, "<init>", "(J)V");
  jobject longObject = env->NewObject(longClass, longConstructor, statPointer);

  // Pair<String, Long> pair = new Pair<String, Long>(jName, longObject)
  jclass pairClass = env->FindClass("Lio/github/cvc5/Pair;");
  jmethodID pairConstructor = env->GetMethodID(
      pairClass, "<init>", "(Ljava/lang/Object;Ljava/lang/Object;)V");
  jobject pair = env->NewObject(pairClass, pairConstructor, jName, longObject);

  it++;
  return pair;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_Statistics
 * Method:    increment
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Statistics_increment(
    JNIEnv* env, jobject, jlong pointer, jlong iteratorPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Statistics* current = reinterpret_cast<Statistics*>(pointer);
  Statistics::iterator* itPointer =
      reinterpret_cast<Statistics::iterator*>(iteratorPointer);
  Statistics::iterator it = *itPointer;
  if (it == current->end())
  {
    delete itPointer;
    std::string message = "Reached the end of Statistics::iterator";
    throw CVC5ApiException(message);
  }

  Statistics::iterator* nextIt = new Statistics::iterator(it.operator++());
  delete itPointer;
  return reinterpret_cast<jlong>(nextIt);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Statistics
 * Method:    deleteIteratorPointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_io_github_cvc5_Statistics_deleteIteratorPointer(
    JNIEnv*, jobject, jlong iteratorPointer)
{
  delete reinterpret_cast<Statistics::iterator*>(iteratorPointer);
}
