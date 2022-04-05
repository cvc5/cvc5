/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 Java API.
 */

#include "api_utilities.h"

#include <string>
#include <vector>

jobjectArray getStringArrayFromStringVector(
    JNIEnv* env, const std::vector<std::string>& cStrings)
{
  jclass stringClass = env->FindClass("java/lang/String");
  jobjectArray ret =
      env->NewObjectArray(cStrings.size(), stringClass, env->NewStringUTF(""));
  for (size_t i = 0; i < cStrings.size(); i++)
  {
    jstring jString = env->NewStringUTF(cStrings[i].c_str());
    env->SetObjectArrayElement(ret, i, jString);
  }
  return ret;
}

jobject getDoubleObject(JNIEnv* env, double cValue)
{
  jdouble jValue = static_cast<jdouble>(cValue);
  jclass doubleClass = env->FindClass("java/lang/Double");
  jmethodID methodId = env->GetMethodID(doubleClass, "<init>", "(D)V");
  jobject ret = env->NewObject(doubleClass, methodId, jValue);
  return ret;
}

jobject getBooleanObject(JNIEnv* env, bool cValue)
{
  jboolean jValue = static_cast<jboolean>(cValue);
  jclass booleanClass = env->FindClass("Ljava/lang/Boolean;");
  jmethodID booleanConstructor =
      env->GetMethodID(booleanClass, "<init>", "(Z)V");
  jobject ret = env->NewObject(booleanClass, booleanConstructor, jValue);
  return ret;
}