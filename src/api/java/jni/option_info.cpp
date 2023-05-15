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

#include <cstdint>

#include <cvc5/cvc5.h>

#include "api_utilities.h"
#include "io_github_cvc5_OptionInfo.h"

using namespace cvc5;

/*
 * Class:     io_github_cvc5_OptionInfo
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_io_github_cvc5_OptionInfo_deletePointer(
    JNIEnv*, jobject, jlong pointer)
{
  delete reinterpret_cast<OptionInfo*>(pointer);
}

/*
 * Class:     io_github_cvc5_OptionInfo
 * Method:    toString
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL
Java_io_github_cvc5_OptionInfo_toString(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  OptionInfo* current = reinterpret_cast<OptionInfo*>(pointer);
  std::stringstream ss;
  ss << *current;
  return env->NewStringUTF(ss.str().c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_OptionInfo
 * Method:    getName
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL
Java_io_github_cvc5_OptionInfo_getName(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  OptionInfo* current = reinterpret_cast<OptionInfo*>(pointer);
  return env->NewStringUTF(current->name.c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_OptionInfo
 * Method:    getAliases
 * Signature: (J)[Ljava/lang/String;
 */
JNIEXPORT jobjectArray JNICALL Java_io_github_cvc5_OptionInfo_getAliases(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  OptionInfo* current = reinterpret_cast<OptionInfo*>(pointer);
  jobjectArray ret = getStringArrayFromStringVector(env, current->aliases);
  return ret;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_OptionInfo
 * Method:    getSetByUser
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_OptionInfo_getSetByUser(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  OptionInfo* current = reinterpret_cast<OptionInfo*>(pointer);
  return static_cast<jboolean>(current->setByUser);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/**
 * Convert OptionInfo::NumberInfo cpp object to OptionInfo.NumberInfo java
 * object
 * @tparam T cpp integer types int64_t, uint64_t, etc
 * @param env jni environment
 * @param optionInfo a java object for this OptionInfo
 * @param numberInfoClass the java class for OptionInfo.NumberInfo
 * @param methodId a constructor for OptionInfo.NumberInfo
 * @param info the cpp OptionInfo::NumberInfo object
 * @return a java object of class OptionInfo.NumberInfo<BigInteger>
 */
template <typename T>
jobject getNumberInfoFromInteger(JNIEnv* env,
                                 const _jobject* optionInfo,
                                 jclass numberInfoClass,
                                 jmethodID methodId,
                                 const OptionInfo::NumberInfo<T>& info)
{
  jobject defaultValue = getBigIntegerObject<T>(env, info.defaultValue);
  jobject currentValue = getBigIntegerObject<T>(env, info.currentValue);
  jobject minimum = nullptr;
  if (info.minimum)
  {
    minimum = getBigIntegerObject<T>(env, *info.minimum);
  }
  jobject maximum = nullptr;
  if (info.maximum)
  {
    maximum = getBigIntegerObject<T>(env, *info.maximum);
  }
  jobject ret = env->NewObject(numberInfoClass,
                               methodId,
                               optionInfo,
                               defaultValue,
                               currentValue,
                               minimum,
                               maximum);

  return ret;
}

template <typename T>
jobject getNumberInfoFromInteger(JNIEnv* env,
                                 const _jobject* optionInfo,
                                 jclass numberInfoClass,
                                 jmethodID methodId,
                                 const OptionInfo::NumberInfo<int64_t>& info);

template <typename T>
jobject getNumberInfoFromInteger(JNIEnv* env,
                                 const _jobject* optionInfo,
                                 jclass numberInfoClass,
                                 jmethodID methodId,
                                 const OptionInfo::NumberInfo<uint64_t>& info);

/*
 * Class:     io_github_cvc5_OptionInfo
 * Method:    getBaseInfo
 * Signature: (J)Lio/github/cvc5/OptionInfo/BaseInfo;
 */
JNIEXPORT jobject JNICALL Java_io_github_cvc5_OptionInfo_getBaseInfo(
    JNIEnv* env, jobject optionInfo, jlong pointer)
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

  if (std::holds_alternative<OptionInfo::VoidInfo>(v))
  {
    jclass voidInfoClass =
        env->FindClass("io/github/cvc5/OptionInfo$VoidInfo");
    jmethodID methodId = env->GetMethodID(
        voidInfoClass, "<init>", "(Lio/github/cvc5/OptionInfo;)V");
    jobject ret = env->NewObject(voidInfoClass, methodId, optionInfo);
    return ret;
  }

  if (std::holds_alternative<OptionInfo::ValueInfo<bool>>(v)
      || std::holds_alternative<OptionInfo::ValueInfo<std::string>>(v))
  {
    jclass valueInfoClass =
        env->FindClass("io/github/cvc5/OptionInfo$ValueInfo");
    jmethodID methodId =
        env->GetMethodID(valueInfoClass,
                         "<init>",
                         "(Lio/github/cvc5/OptionInfo;Ljava/lang/"
                         "Object;Ljava/lang/Object;)V");

    if (std::holds_alternative<OptionInfo::ValueInfo<bool>>(v))
    {
      auto info = std::get<OptionInfo::ValueInfo<bool>>(v);
      jobject currentValue = getBooleanObject(env, info.currentValue);
      jobject defaultValue = getBooleanObject(env, info.defaultValue);
      jobject ret = env->NewObject(
          valueInfoClass, methodId, optionInfo, defaultValue, currentValue);
      return ret;
    }

    if (std::holds_alternative<OptionInfo::ValueInfo<std::string>>(v))
    {
      auto info = std::get<OptionInfo::ValueInfo<std::string>>(v);
      jstring defaultValue = env->NewStringUTF(info.defaultValue.c_str());
      jstring currentValue = env->NewStringUTF(info.currentValue.c_str());
      jobject ret = env->NewObject(
          valueInfoClass, methodId, optionInfo, defaultValue, currentValue);
      return ret;
    }
  }

  if (std::holds_alternative<OptionInfo::NumberInfo<int64_t>>(v)
      || std::holds_alternative<OptionInfo::NumberInfo<uint64_t>>(v)
      || std::holds_alternative<OptionInfo::NumberInfo<double>>(v))
  {
    jclass numberInfoClass =
        env->FindClass("io/github/cvc5/OptionInfo$NumberInfo");
    jmethodID methodId = env->GetMethodID(
        numberInfoClass,
        "<init>",
        "(Lio/github/cvc5/OptionInfo;Ljava/lang/Object;Ljava/lang/"
        "Object;Ljava/lang/Object;Ljava/lang/Object;)V");

    if (std::holds_alternative<OptionInfo::NumberInfo<int64_t>>(v))
    {
      auto info = std::get<OptionInfo::NumberInfo<int64_t>>(v);
      return getNumberInfoFromInteger(
          env, optionInfo, numberInfoClass, methodId, info);
    }

    if (std::holds_alternative<OptionInfo::NumberInfo<uint64_t>>(v))
    {
      auto info = std::get<OptionInfo::NumberInfo<uint64_t>>(v);
      return getNumberInfoFromInteger(
          env, optionInfo, numberInfoClass, methodId, info);
    }

    if (std::holds_alternative<OptionInfo::NumberInfo<double>>(v))
    {
      auto info = std::get<OptionInfo::NumberInfo<double>>(v);
      jobject defaultValue = getDoubleObject(env, info.defaultValue);
      jobject currentValue = getDoubleObject(env, info.currentValue);
      jobject minimum = nullptr;
      if (info.minimum)
      {
        minimum = getDoubleObject(env, *info.minimum);
      }
      jobject maximum = nullptr;
      if (info.maximum)
      {
        maximum = getDoubleObject(env, *info.maximum);
      }
      jobject ret = env->NewObject(numberInfoClass,
                                   methodId,
                                   optionInfo,
                                   defaultValue,
                                   currentValue,
                                   minimum,
                                   maximum);
      return ret;
    }
  }

  if (std::holds_alternative<OptionInfo::ModeInfo>(v))
  {
    jclass modeInfoClass =
        env->FindClass("io/github/cvc5/OptionInfo$ModeInfo");
    jmethodID methodId = env->GetMethodID(
        modeInfoClass,
        "<init>",
        "(Lio/github/cvc5/OptionInfo;Ljava/lang/String;Ljava/lang/"
        "String;[Ljava/lang/String;)V");

    auto info = std::get<OptionInfo::ModeInfo>(v);
    jstring defaultValue = env->NewStringUTF(info.defaultValue.c_str());
    jstring currentValue = env->NewStringUTF(info.currentValue.c_str());
    jobject stringArray = getStringArrayFromStringVector(env, info.modes);
    jobject ret = env->NewObject(modeInfoClass,
                                 methodId,
                                 optionInfo,
                                 defaultValue,
                                 currentValue,
                                 stringArray);
    return ret;
  }

  return nullptr;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_OptionInfo
 * Method:    booleanValue
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_OptionInfo_booleanValue(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  OptionInfo* current = reinterpret_cast<OptionInfo*>(pointer);
  return static_cast<jboolean>(current->boolValue());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_OptionInfo
 * Method:    stringValue
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_io_github_cvc5_OptionInfo_stringValue(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  OptionInfo* current = reinterpret_cast<OptionInfo*>(pointer);
  std::string ret = current->stringValue();
  return env->NewStringUTF(ret.c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_OptionInfo
 * Method:    intValue
 * Signature: (J)Ljava/math/BigInteger;
 */
JNIEXPORT jobject JNICALL
Java_io_github_cvc5_OptionInfo_intValue(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  OptionInfo* current = reinterpret_cast<OptionInfo*>(pointer);
  if (std::holds_alternative<OptionInfo::NumberInfo<uint64_t>>(
          current->valueInfo))
  {
    std::uint64_t value = current->uintValue();
    jobject ret = getBigIntegerObject<std::uint64_t>(env, value);
    return ret;
  }
  if (std::holds_alternative<OptionInfo::NumberInfo<int64_t>>(
          current->valueInfo))
  {
    std::int64_t value = current->intValue();
    jobject ret = getBigIntegerObject<std::int64_t>(env, value);
    return ret;
  }
  throw CVC5ApiRecoverableException("Option is neither int64_t nor uint64_t");
  return jobject();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_OptionInfo
 * Method:    doubleValue
 * Signature: (J)D
 */
JNIEXPORT jdouble JNICALL Java_io_github_cvc5_OptionInfo_doubleValue(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  OptionInfo* current = reinterpret_cast<OptionInfo*>(pointer);
  double ret = current->doubleValue();
  return static_cast<jdouble>(ret);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jdouble>(0.0));
}
