#include "cvc5_Op.h"

#include "api/cpp/cvc5.h"
#include "cvc5JavaApi.h"

using namespace cvc5::api;

/*
 * Class:     cvc5_Op
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_cvc5_Op_deletePointer(JNIEnv*,
                                                  jclass,
                                                  jlong pointer)
{
  delete ((Op*)pointer);
}

/*
 * Class:     cvc5_Op
 * Method:    equals
 * Signature: (JJ)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Op_equals(JNIEnv* env,
                                               jobject,
                                               jlong pointer1,
                                               jlong pointer2)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Op* op1 = (Op*)pointer1;
  Op* op2 = (Op*)pointer2;
  // We compare the actual operators, not their pointers.
  return (jboolean)(*op1 == *op2);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Op
 * Method:    getKind
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_cvc5_Op_getKind(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Op* current = (Op*)pointer;
  return (jboolean)current->getKind();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Op
 * Method:    isNull
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Op_isNull(JNIEnv* env,
                                               jobject,
                                               jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Op* current = (Op*)pointer;
  return (jboolean)current->isNull();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_Op
 * Method:    isIndexed
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Op_isIndexed(JNIEnv* env,
                                                  jobject,
                                                  jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Op* current = (Op*)pointer;
  return (jboolean)current->isIndexed();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Op
 * Method:    getIntegerIndices
 * Signature: (J)[I
 */
JNIEXPORT jintArray JNICALL Java_cvc5_Op_getIntegerIndices(JNIEnv* env,
                                                           jobject,
                                                           jlong pointer);
//{
//  CVC5_JAVA_API_TRY_CATCH_BEGIN;
//  Op* current = (Op*)pointer;
//  current->
//  std::vector<long> sortPointers(sorts.size());
//  for (size_t i = 0; i < sorts.size(); i++)
//  {
//    sortPointers[i] = (long)new Sort(sorts[i]);
//  }
//  jlongArray ret = env->NewLongArray(sorts.size());
//  env->SetLongArrayRegion(ret, 0, sorts.size(), sortPointers.data());
//  return ret;
//  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
//}

/*
 * Class:     cvc5_Op
 * Method:    getStringIndices
 * Signature: (J)[Ljava/lang/String;
 */
JNIEXPORT jobjectArray JNICALL Java_cvc5_Op_getStringIndices(JNIEnv* env,
                                                             jobject,
                                                             jlong pointer);


/*
 * Class:     cvc5_Op
 * Method:    toString
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_cvc5_Op_toString(JNIEnv*, jobject, jlong);
