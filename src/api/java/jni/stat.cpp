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

#include "api_utilities.h"
#include "io_github_cvc5_Stat.h"

using namespace cvc5;

/*
 * Class:     io_github_cvc5_Stat
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_io_github_cvc5_Stat_deletePointer(JNIEnv*,
                                                                  jobject,
                                                                  jlong pointer)
{
  delete reinterpret_cast<Stat*>(pointer);
}

/*
 * Class:     io_github_cvc5_Stat
 * Method:    toString
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_io_github_cvc5_Stat_toString(JNIEnv* env,
                                                                jobject,
                                                                jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;

  Stat* current = reinterpret_cast<Stat*>(pointer);
  std::stringstream ss;
  ss << *current;
  return env->NewStringUTF(ss.str().c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_Stat
 * Method:    isInternal
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Stat_isInternal(JNIEnv* env,
                                                                 jobject,
                                                                 jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Stat* current = reinterpret_cast<Stat*>(pointer);
  return static_cast<jboolean>(current->isInternal());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Stat
 * Method:    isDefault
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Stat_isDefault(JNIEnv* env,
                                                                  jobject,
                                                                  jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Stat* current = reinterpret_cast<Stat*>(pointer);
  return static_cast<jboolean>(current->isDefault());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Stat
 * Method:    isInt
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Stat_isInt(JNIEnv* env,
                                                              jobject,
                                                              jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Stat* current = reinterpret_cast<Stat*>(pointer);
  return static_cast<jboolean>(current->isInt());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Stat
 * Method:    getInt
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Stat_getInt(JNIEnv* env,
                                                            jobject,
                                                            jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Stat* current = reinterpret_cast<Stat*>(pointer);
  return static_cast<jlong>(current->getInt());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jlong>(0));
}

/*
 * Class:     io_github_cvc5_Stat
 * Method:    isDouble
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Stat_isDouble(JNIEnv* env,
                                                                 jobject,
                                                                 jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Stat* current = reinterpret_cast<Stat*>(pointer);
  return static_cast<jboolean>(current->isDouble());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Stat
 * Method:    getDouble
 * Signature: (J)D
 */
JNIEXPORT jdouble JNICALL Java_io_github_cvc5_Stat_getDouble(JNIEnv* env,
                                                                 jobject,
                                                                 jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Stat* current = reinterpret_cast<Stat*>(pointer);
  return static_cast<jdouble>(current->getDouble());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jdouble>(0));
}

/*
 * Class:     io_github_cvc5_Stat
 * Method:    isString
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Stat_isString(JNIEnv* env,
                                                                 jobject,
                                                                 jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Stat* current = reinterpret_cast<Stat*>(pointer);
  return static_cast<jboolean>(current->isString());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Stat
 * Method:    getString
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_io_github_cvc5_Stat_getString(JNIEnv* env,
                                                                 jobject,
                                                                 jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Stat* current = reinterpret_cast<Stat*>(pointer);
  return env->NewStringUTF(current->getString().c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_Stat
 * Method:    isHistogram
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL
Java_io_github_cvc5_Stat_isHistogram(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Stat* current = reinterpret_cast<Stat*>(pointer);
  return static_cast<jboolean>(current->isHistogram());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Stat
 * Method:    getHistogram
 * Signature: (J)Ljava/util/Map;
 */
JNIEXPORT jobject JNICALL
Java_io_github_cvc5_Stat_getHistogram(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Stat* current = reinterpret_cast<Stat*>(pointer);
  std::map<std::string, uint64_t> histogram = current->getHistogram();
  // HashMap hashMap = new HashMap();
  jclass hashMapClass = env->FindClass("Ljava/util/HashMap;");
  jmethodID constructor = env->GetMethodID(hashMapClass, "<init>", "()V");
  jobject hashMap = env->NewObject(hashMapClass, constructor);
  jmethodID putMethod = env->GetMethodID(
      hashMapClass,
      "put",
      "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;");

  // Long longObject = new Long(statPointer)
  jclass longClass = env->FindClass("Ljava/lang/Long;");
  jmethodID longConstructor = env->GetMethodID(longClass, "<init>", "(J)V");

  for (const std::pair<const std::basic_string<char>, uint64_t>& it : histogram)
  {
    // hashmap.put(key, value);
    jstring key = env->NewStringUTF(it.first.c_str());
    jobject value = env->NewObject(
        longClass, longConstructor, static_cast<jlong>(it.second));
    env->CallObjectMethod(hashMap, putMethod, key, value);
  }
  return hashMap;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}
