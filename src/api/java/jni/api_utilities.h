/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andres Noetzli
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

#ifndef CVC5__API_UTILITIES_H
#define CVC5__API_UTILITIES_H
#include <cvc5/cvc5.h>
#include <jni.h>

#include <string>
#include <vector>

#define CVC5_JAVA_API_TRY_CATCH_BEGIN \
  try                                 \
  {
#define CVC5_JAVA_API_TRY_CATCH_END(env)                                       \
  }                                                                            \
  catch (const CVC5ApiOptionException& e)                                      \
  {                                                                            \
    jclass exceptionClass =                                                    \
        env->FindClass("io/github/cvc5/CVC5ApiOptionException");               \
    env->ThrowNew(exceptionClass, e.what());                                   \
  }                                                                            \
  catch (const CVC5ApiRecoverableException& e)                                 \
  {                                                                            \
    jclass exceptionClass =                                                    \
        env->FindClass("io/github/cvc5/CVC5ApiRecoverableException");          \
    env->ThrowNew(exceptionClass, e.what());                                   \
  }                                                                            \
  catch (const CVC5ApiException& e)                                            \
  {                                                                            \
    jclass exceptionClass = env->FindClass("io/github/cvc5/CVC5ApiException"); \
    env->ThrowNew(exceptionClass, e.what());                                   \
  }
#define CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, returnValue) \
  CVC5_JAVA_API_TRY_CATCH_END(env)                           \
  return returnValue;

/**
 * Convert pointers coming from Java to cvc5 objects
 * @tparam T cvc5 class (Term, Sort, Grammar, etc)
 * @param env jni environment
 * @param jPointers pointers coming from java
 * @return a vector of cvc5 objects
 */
template <class T>
std::vector<T> getObjectsFromPointers(JNIEnv* env, jlongArray jPointers)
{
  // get the size of pointers
  jsize size = env->GetArrayLength(jPointers);
  // allocate a buffer for c pointers
  std::vector<jlong> cPointers(size);
  // copy java array to the buffer
  env->GetLongArrayRegion(jPointers, 0, size, cPointers.data());
  // copy the terms into a vector
  std::vector<T> objects;
  for (jlong pointer : cPointers)
  {
    T* term = reinterpret_cast<T*>(pointer);
    objects.push_back(*term);
  }
  return objects;
}

/**
 * Convert cvc5 objects into pointers
 * @tparam T cvc5 class (Term, Sort, Grammar, etc)
 * @param env jni environment
 * @param objects cvc5 objects
 * @return jni array of pointers
 */
template <class T>
jlongArray getPointersFromObjects(JNIEnv* env, const std::vector<T>& objects)
{
  std::vector<jlong> pointers(objects.size());
  for (size_t i = 0; i < objects.size(); i++)
  {
    pointers[i] = reinterpret_cast<jlong>(new T(objects[i]));
  }
  jlongArray ret = env->NewLongArray(objects.size());
  env->SetLongArrayRegion(ret, 0, objects.size(), pointers.data());
  return ret;
}

/**
 * Convert a cpp signed (unsigned) integer to an object of BigInteger class
 * @tparam T cpp types (int64_t, uint64_t, int32_t, int32_t, etc)
 * @param env jni environment
 * @param value cpp integer value
 * @return an object of java BigInteger
 */
template <class T>
jobject getBigIntegerObject(JNIEnv* env, T value)
{
  std::string s = std::to_string(value);
  jstring javaString = env->NewStringUTF(s.c_str());
  jclass bigIntegerClass = env->FindClass("java/math/BigInteger");
  jmethodID bigIntegerConstructor =
      env->GetMethodID(bigIntegerClass, "<init>", "(Ljava/lang/String;)V");
  jobject ret =
      env->NewObject(bigIntegerClass, bigIntegerConstructor, javaString);
  return ret;
}

/**
 * Generate an array of java strings from a vector of cpp strings
 * @param env jni environment
 * @param cStrings a vector of strings
 * @return an array of java strings
 */
jobjectArray getStringArrayFromStringVector(
    JNIEnv* env, const std::vector<std::string>& cStrings);

/**
 * Generate a Double object from cpp double value
 * @param env jni environment
 * @param value
 * @return a Double object
 */
jobject getDoubleObject(JNIEnv* env, double value);

/**
 * Generate a Boolean object from cpp bool value
 * @param env jni environment
 * @param value
 * @return a Boolean object
 */
jobject getBooleanObject(JNIEnv* env, bool value);

/**
 * a map from solver pointers to global references that need to be freed when
 * the java Solver.close method is called
 */
inline std::map<jlong, std::vector<jobject> > globalReferences;

/**
 * @param env jni environment
 * @param solverRef a global reference to java Solver object
 * @param oracleRef a global reference to java IOracle object
 * @param terms a list of terms
 * @return the result of calling IOracle.compute(terms)
 */
cvc5::Term applyOracle(JNIEnv* env,
                       jobject oracleRef,
                       const std::vector<cvc5::Term>& terms);

#endif  // CVC5__API_UTILITIES_H
