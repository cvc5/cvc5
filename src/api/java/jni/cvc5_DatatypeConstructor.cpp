#include "cvc5_DatatypeConstructor.h"

#include "api/cpp/cvc5.h"
#include "cvc5JavaApi.h"

using namespace cvc5::api;

/*
 * Class:     cvc5_DatatypeConstructor
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_cvc5_DatatypeConstructor_deletePointer(JNIEnv*,
                                                                   jclass,
                                                                   jlong);

/*
 * Class:     cvc5_DatatypeConstructor
 * Method:    getName
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_cvc5_DatatypeConstructor_getName(JNIEnv* env,
                                                                jobject,
                                                                jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeConstructor* current = (DatatypeConstructor*)pointer;
  return env->NewStringUTF(current->getName().c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     cvc5_DatatypeConstructor
 * Method:    getConstructorTerm
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_DatatypeConstructor_getConstructorTerm(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeConstructor* current = (DatatypeConstructor*)pointer;
  Term* retPointer = new Term(current->getConstructorTerm());
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_DatatypeConstructor
 * Method:    getSpecializedConstructorTerm
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL
Java_cvc5_DatatypeConstructor_getSpecializedConstructorTerm(
    JNIEnv* env, jobject, jlong pointer, jlong retSortPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeConstructor* current = (DatatypeConstructor*)pointer;
  Sort* sort = (Sort*)retSortPointer;
  Term* retPointer = new Term(current->getSpecializedConstructorTerm(*sort));
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_DatatypeConstructor
 * Method:    getTesterTerm
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL
Java_cvc5_DatatypeConstructor_getTesterTerm(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeConstructor* current = (DatatypeConstructor*)pointer;
  Term* retPointer = new Term(current->getTesterTerm());
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_DatatypeConstructor
 * Method:    getNumSelectors
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_cvc5_DatatypeConstructor_getNumSelectors(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeConstructor* current = (DatatypeConstructor*)pointer;
  return (jint)current->getNumSelectors();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_DatatypeConstructor
 * Method:    getSelector
 * Signature: (JI)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_DatatypeConstructor_getSelector__JI(
    JNIEnv* env, jobject, jlong pointer, jint index)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeConstructor* current = (DatatypeConstructor*)pointer;
  DatatypeSelector* retPointer =
      new DatatypeSelector(current->operator[]((size_t)index));
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_DatatypeConstructor
 * Method:    getSelector
 * Signature: (JLjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL
Java_cvc5_DatatypeConstructor_getSelector__JLjava_lang_String_2(JNIEnv* env,
                                                                jobject,
                                                                jlong pointer,
                                                                jstring jName)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeConstructor* current = (DatatypeConstructor*)pointer;
  const char* s = env->GetStringUTFChars(jName, nullptr);
  std::string cName(s);
  DatatypeSelector* retPointer =
      new DatatypeSelector(current->operator[](cName));
  env->ReleaseStringUTFChars(jName, s);
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_DatatypeConstructor
 * Method:    getSelectorTerm
 * Signature: (JLjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_DatatypeConstructor_getSelectorTerm(
    JNIEnv* env, jobject, jlong pointer, jstring jName)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeConstructor* current = (DatatypeConstructor*)pointer;
  const char* s = env->GetStringUTFChars(jName, nullptr);
  std::string cName(s);
  Term* retPointer = new Term(current->getSelectorTerm(cName));
  env->ReleaseStringUTFChars(jName, s);
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_DatatypeConstructor
 * Method:    isNull
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_DatatypeConstructor_isNull(JNIEnv*,
                                                                jobject,
                                                                jlong);

/*
 * Class:     cvc5_DatatypeConstructor
 * Method:    toString
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_cvc5_DatatypeConstructor_toString(JNIEnv*,
                                                                 jobject,
                                                                 jlong);
