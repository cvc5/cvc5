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

#include "cvc5_OptionInfo.h"

#include <iostream>
#include <sstream>

#include "api/cpp/cvc5.h"
#include "cvc5JavaApi.h"

using namespace cvc5::api;

/*
 * Class:     cvc5_OptionInfo
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_cvc5_OptionInfo_deletePointer(JNIEnv*,
                                                          jclass,
                                                          jlong pointer)
{
  delete reinterpret_cast<OptionInfo*>(pointer);
}

/*
 * Class:     cvc5_OptionInfo
 * Method:    toString
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_cvc5_OptionInfo_toString(JNIEnv* env,
                                                        jobject,
                                                        jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  OptionInfo* current = reinterpret_cast<OptionInfo*>(pointer);
  std::stringstream ss;
  ss << *current;
  return env->NewStringUTF(ss.str().c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     cvc5_OptionInfo
 * Method:    getName
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_cvc5_OptionInfo_getName(JNIEnv* env,
                                                       jobject,
                                                       jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  OptionInfo* current = reinterpret_cast<OptionInfo*>(pointer);
  return env->NewStringUTF(current->name.c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     cvc5_OptionInfo
 * Method:    getAliases
 * Signature: (J)[Ljava/lang/String;
 */
JNIEXPORT jobjectArray JNICALL Java_cvc5_OptionInfo_getAliases(JNIEnv* env,
                                                               jobject,
                                                               jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  OptionInfo* current = reinterpret_cast<OptionInfo*>(pointer);
  jobjectArray ret = getStringArrayFromStrings(env, current->aliases);
  return ret;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     cvc5_OptionInfo
 * Method:    getSetByUser
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_OptionInfo_getSetByUser(JNIEnv* env,
                                                             jobject,
                                                             jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  OptionInfo* current = reinterpret_cast<OptionInfo*>(pointer);
  return static_cast<jboolean>(current->setByUser);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     cvc5_OptionInfo
 * Method:    getValueInfo
 * Signature: (J)Lcvc5/OptionInfo/ValueInfo;
 */
JNIEXPORT jobject JNICALL Java_cvc5_OptionInfo_getValueInfo(JNIEnv* env,
                                                            jobject optionInfo,
                                                            jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  OptionInfo* current = reinterpret_cast<OptionInfo*>(pointer);
  std::variant<OptionInfo::VoidInfo,
               OptionInfo::ValueInfo<bool>,
               OptionInfo::ValueInfo<std::string>,
               OptionInfo::NumberInfo<int64_t>,
               OptionInfo::NumberInfo<uint64_t>,
               OptionInfo::NumberInfo<double>,
               OptionInfo::ModeInfo>
      v = current->valueInfo;

  jobject ret;
  if (std::holds_alternative<OptionInfo::VoidInfo>(v))
  {
    jclass voidInfoClass = env->FindClass("cvc5/OptionInfo$VoidInfo");
    jmethodID methodId =
        env->GetMethodID(voidInfoClass, "<init>", "(Lcvc5/OptionInfo;)V");
    ret = env->CallObjectMethod(voidInfoClass, methodId, optionInfo);
    return ret;
  }

  if (std::holds_alternative<OptionInfo::ValueInfo<bool>>(v))
  {
    auto info = std::get<OptionInfo::ValueInfo<bool>>(v);
    jclass valueInfoClass = env->FindClass("cvc5/OptionInfo$ValueInfo");
    jmethodID methodId = env->GetMethodID(
        valueInfoClass,
        "<init>",
        "(Lcvc5/OptionInfo;Ljava/lang/Object;Ljava/lang/Object;)V");
    std::cout << "methodId: " << methodId << std::endl;
    jclass booleanClass = env->FindClass("Ljava/lang/Boolean;");
    jmethodID booleanConstructor =
        env->GetMethodID(booleanClass, "<init>", "(Z)V");
    jobject currentValue =
        env->NewObject(booleanClass,
                       booleanConstructor,
                       static_cast<jboolean>(info.currentValue));
    jobject defaultValue =
        env->NewObject(booleanClass,
                       booleanConstructor,
                       static_cast<jboolean>(info.defaultValue));
    ret = env->CallObjectMethod(
        valueInfoClass, methodId, optionInfo, defaultValue, currentValue);
    return ret;
  }

  if (std::holds_alternative<OptionInfo::ValueInfo<std::string>>(v))
  {
    auto info = std::get<OptionInfo::ValueInfo<std::string>>(v);
    jclass valueInfoClass = env->FindClass("cvc5/OptionInfo$ValueInfo");
    jmethodID methodId = env->GetMethodID(
        valueInfoClass,
        "<init>",
        "(Lcvc5/OptionInfo;Ljava/lang/Object;Ljava/lang/Object;)V");
    std::cout << "methodId: " << methodId << std::endl;
    jstring defaultValue = env->NewStringUTF(info.defaultValue.c_str());
    jstring currentValue = env->NewStringUTF(info.currentValue.c_str());
    ret = env->CallObjectMethod(
        valueInfoClass, methodId, optionInfo, defaultValue, currentValue);
    return ret;
  }

  if (std::holds_alternative<OptionInfo::NumberInfo<int64_t>>(v) ||
      std::holds_alternative<OptionInfo::NumberInfo<uint64_t>>(v)
      )
  {
    auto info = std::get<OptionInfo::NumberInfo<uint64_t>>(v);
    jclass valueInfoClass = env->FindClass("cvc5/OptionInfo$NumberInfo");
    jmethodID methodId = env->GetMethodID(
        valueInfoClass,
        "<init>",
        "(Lcvc5/OptionInfo;Ljava/lang/Object;Ljava/lang/Object;Ljava/lang/Object;Ljava/lang/Object;)V");
    std::stringstream ssDefault, ssCurrent;
    ssDefault << info.defaultValue;
    ssCurrent << info.currentValue;
    jstring jDefault = env->NewStringUTF(ssDefault.str().c_str());
    jstring jCurrent = env->NewStringUTF(ssCurrent.str().c_str());
    jclass bigIntegerClass = env->FindClass("java/math/BigInteger");
    jmethodID bigIntegerConstructor = env->GetMethodID(bigIntegerClass, "<init>", "(Ljava/lang/String;)V");
    jobject defaultValue = env->NewObject(bigIntegerClass, bigIntegerConstructor, jDefault);
    jobject currentValue = env->NewObject(bigIntegerClass, bigIntegerConstructor, jCurrent);
    ret = env->CallObjectMethod(
        valueInfoClass, methodId, optionInfo, defaultValue, currentValue, nullptr, nullptr);
    return ret;
  }

  return ret;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     cvc5_OptionInfo
 * Method:    booleanValue
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_OptionInfo_booleanValue(JNIEnv* env,
                                                             jobject,
                                                             jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  OptionInfo* current = reinterpret_cast<OptionInfo*>(pointer);
  return static_cast<jboolean>(current->boolValue());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     cvc5_OptionInfo
 * Method:    stringValue
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_cvc5_OptionInfo_stringValue(JNIEnv* env,
                                                           jobject,
                                                           jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  OptionInfo* current = reinterpret_cast<OptionInfo*>(pointer);
  std::string ret = current->stringValue();
  return env->NewStringUTF(ret.c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     cvc5_OptionInfo
 * Method:    intValue
 * Signature: (J)Ljava/math/BigInteger;
 */
JNIEXPORT jobject JNICALL Java_cvc5_OptionInfo_intValue(JNIEnv*,
                                                        jobject,
                                                        jlong);

/*
 * Class:     cvc5_OptionInfo
 * Method:    doubleValue
 * Signature: (J)D
 */
JNIEXPORT jdouble JNICALL Java_cvc5_OptionInfo_doubleValue(JNIEnv* env,
                                                           jobject,
                                                           jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  OptionInfo* current = reinterpret_cast<OptionInfo*>(pointer);
  double ret = current->doubleValue();
  return static_cast<jdouble>(ret);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jdouble>(0.0));
}
