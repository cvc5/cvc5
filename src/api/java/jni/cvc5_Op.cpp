#include "cvc5_Op.h"

#include "api/cpp/cvc5.h"
#include "cvc5JavaApi.h"

using namespace cvc5::api;

/*
 * Class:     cvc5_Op
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_cvc5_Op_deletePointer(JNIEnv*, jclass, jlong);

/*
 * Class:     cvc5_Op
 * Method:    equals
 * Signature: (JJ)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Op_equals(JNIEnv* env, jobject, jlong pointer1, jlong pointer2)
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
JNIEXPORT jint JNICALL Java_cvc5_Op_getKind(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Op
 * Method:    isNull
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Op_isNull(JNIEnv*, jobject, jlong);

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
  Op* op = (Op*)pointer;
  return (jboolean)op->isIndexed();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Op
 * Method:    getIntegerIndex
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_cvc5_Op_getIntegerIndex(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Op
 * Method:    getStringIndices
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_cvc5_Op_getStringIndices(JNIEnv*,
                                                        jobject,
                                                        jlong);

/*
 * Class:     cvc5_Op
 * Method:    getIntegerPairIndices
 * Signature: (J)[I
 */
JNIEXPORT jintArray JNICALL Java_cvc5_Op_getIntegerPairIndices(JNIEnv*,
                                                               jobject,
                                                               jlong);

/*
 * Class:     cvc5_Op
 * Method:    toString
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_cvc5_Op_toString(JNIEnv*, jobject, jlong);
