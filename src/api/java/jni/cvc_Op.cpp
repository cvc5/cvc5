#include "cvc_Op.h"

#include "cvc4/api/cvc4cpp.h"
#include "cvcJavaApi.h"

using namespace CVC4::api;

/*
 * Class:     cvc_Op
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_cvc_Op_deletePointer(JNIEnv*, jclass, jlong pointer)
{
  std::cout << "Deleting Op pointer: " << pointer << std::endl;
  delete ((Op*)pointer);
}

/*
 * Class:     cvc_Op
 * Method:    toString
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_cvc_Op_toString(JNIEnv* env,
                                               jobject,
                                               jlong pointer)
{
  Op* op = (Op*)pointer;
  return env->NewStringUTF(op->toString().c_str());
}

/*
 * Class:     cvc_Op
 * Method:    equals
 * Signature: (JJ)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc_Op_equals(JNIEnv* env,
                                              jobject,
                                              jlong pointer1,
                                              jlong pointer2)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Op* op1 = (Op*)pointer1;
  Op* op2 = (Op*)pointer2;
  // We compare the actual operators, not their pointers.
  // Otherwise the two ops may not be equal
  return (jboolean)(*op1 == *op2);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc_Op
 * Method:    getKind
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_cvc_Op_getKind(JNIEnv*, jobject, jlong pointer)
{
  Op* op = (Op*)pointer;
  return (jint)op->getKind();
}

/*
 * Class:     cvc_Op
 * Method:    isNull
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc_Op_isNull(JNIEnv*, jobject, jlong pointer)
{
  Op* op = (Op*)pointer;
  return (jboolean)op->isNull();
}

/*
 * Class:     cvc_Op
 * Method:    isIndexed
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc_Op_isIndexed(JNIEnv*,
                                                 jobject,
                                                 jlong pointer)
{
  Op* op = (Op*)pointer;
  return (jboolean)op->isIndexed();
}

/*
 * Class:     cvc_Op
 * Method:    getIntegerIndex
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_cvc_Op_getIntegerIndex(JNIEnv* env,
                                                   jobject,
                                                   jlong pointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Op* op = (Op*)pointer;
  return (jint)op->getIndices<uint32_t>();
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Op
 * Method:    getStringIndices
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_cvc_Op_getStringIndices(JNIEnv* env,
                                                       jobject,
                                                       jlong pointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Op* op = (Op*)pointer;
  std::string indices = op->getIndices<std::string>();
  return env->NewStringUTF(indices.data());
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}
/*
 * Class:     cvc_Op
 * Method:    getIntegerPairIndices
 * Signature: (J)[I
 */
JNIEXPORT jintArray JNICALL Java_cvc_Op_getIntegerPairIndices(JNIEnv* env,
                                                              jobject,
                                                              jlong pointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Op* op = (Op*)pointer;
  std::pair<uint32_t, uint32_t> indices =
      op->getIndices<std::pair<uint32_t, uint32_t>>();
  jintArray intArray = env->NewIntArray(2);
  jint intBuffer[2];
  intBuffer[0] = indices.first;
  intBuffer[1] = indices.second;
  env->SetIntArrayRegion(intArray, 0, 2, intBuffer);
  return intArray;
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}
