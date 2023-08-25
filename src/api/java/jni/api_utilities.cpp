/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
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

cvc5::Term applyOracle(JNIEnv* env,
                       jobject oracleRef,
                       const std::vector<cvc5::Term>& terms)
{
  jclass termClass = env->FindClass("Lio/github/cvc5/Term;");
  jmethodID termConstructor = env->GetMethodID(termClass, "<init>", "(J)V");

  jobjectArray jTerms = env->NewObjectArray(terms.size(), termClass, NULL);

  for (size_t i = 0; i < terms.size(); i++)
  {
    jlong termPointer = reinterpret_cast<jlong>(new cvc5::Term(terms[i]));
    jobject jTerm = env->NewObject(termClass, termConstructor, termPointer);
    env->SetObjectArrayElement(jTerms, i, jTerm);
  }

  jclass oracleClass = env->GetObjectClass(oracleRef);
  jmethodID applyMethod = env->GetMethodID(
      oracleClass, "apply", "([Lio/github/cvc5/Term;)Lio/github/cvc5/Term;");

  jobject jTerm = env->CallObjectMethod(oracleRef, applyMethod, jTerms);
  jfieldID pointer = env->GetFieldID(termClass, "pointer", "J");
  jlong termPointer = env->GetLongField(jTerm, pointer);
  cvc5::Term* term = reinterpret_cast<cvc5::Term*>(termPointer);
  return *term;
}
