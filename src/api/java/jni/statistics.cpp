/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
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
JNIEXPORT void JNICALL
Java_io_github_cvc5_Statistics_deletePointer(JNIEnv*, jclass, jlong pointer)
{
  delete reinterpret_cast<Statistics*>(pointer);
}

/*
 * Class:     io_github_cvc5_Statistics
 * Method:    toString
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_io_github_cvc5_Statistics_toString(JNIEnv* env,
                                                                  jobject,
                                                                  jlong pointer)
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
 * Method:    getEntries
 * Signature: (JZZ)Lio/github/cvc5/Pair;
 */
JNIEXPORT jobject JNICALL Java_io_github_cvc5_Statistics_getEntries(
    JNIEnv* env, jobject, jlong pointer, jboolean internal, jboolean defaulted)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Statistics* current = reinterpret_cast<Statistics*>(pointer);
  std::vector<std::string> names;
  std::vector<jlong> stats;
  for (Statistics::iterator it = current->begin(internal, defaulted);
       it != current->end();
       ++it)
  {
    names.push_back(it->first);
    // Ownership is transferred to the Java wrapper.
    stats.push_back(reinterpret_cast<jlong>(new Stat(it->second)));
  }
  jobjectArray jNames = getStringArrayFromStringVector(env, names);
  jlongArray jStats = env->NewLongArray(stats.size());
  env->SetLongArrayRegion(jStats, 0, stats.size(), stats.data());
  // Pair<String[], long[]> pair = new Pair<>(jNames, jStats)
  jclass pairClass = env->FindClass("io/github/cvc5/Pair");
  jmethodID pairConstructor = env->GetMethodID(
      pairClass, "<init>", "(Ljava/lang/Object;Ljava/lang/Object;)V");
  return env->NewObject(pairClass, pairConstructor, jNames, jStats);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}
