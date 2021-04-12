#include "cvc5_Datatype.h"

#include "api/cpp/cvc5.h"
#include "cvc5JavaApi.h"

using namespace cvc5::api;

/*
 * Class:     cvc5_Datatype
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_cvc5_Datatype_deletePointer(JNIEnv*, jclass, jlong);

/*
 * Class:     cvc5_Datatype
 * Method:    getConstructor
 * Signature: (JI)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Datatype_getConstructor__JI(JNIEnv*,
                                                              jobject,
                                                              jlong,
                                                              jint);

/*
 * Class:     cvc5_Datatype
 * Method:    getConstructor
 * Signature: (JLjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Datatype_getConstructor__JLjava_lang_String_2(
    JNIEnv*, jobject, jlong, jstring);

/*
 * Class:     cvc5_Datatype
 * Method:    getConstructorTerm
 * Signature: (JLjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Datatype_getConstructorTerm(JNIEnv* env,
                                                              jobject,
                                                              jlong pointer,
                                                              jstring jName)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Datatype* current = (Datatype*)pointer;
  const char* s = env->GetStringUTFChars(jName, nullptr);
  std::string cName(s);
  Term* retPointer = new Term(current->getConstructorTerm(cName));
  env->ReleaseStringUTFChars(jName, s);
  return ((jlong)retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Datatype
 * Method:    getName
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_cvc5_Datatype_getName(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Datatype
 * Method:    getNumConstructors
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_cvc5_Datatype_getNumConstructors(JNIEnv*,
                                                             jobject,
                                                             jlong);

/*
 * Class:     cvc5_Datatype
 * Method:    isParametric
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Datatype_isParametric(JNIEnv*,
                                                           jobject,
                                                           jlong);

/*
 * Class:     cvc5_Datatype
 * Method:    isCodatatype
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Datatype_isCodatatype(JNIEnv*,
                                                           jobject,
                                                           jlong);

/*
 * Class:     cvc5_Datatype
 * Method:    isTuple
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Datatype_isTuple(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Datatype
 * Method:    isRecord
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Datatype_isRecord(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Datatype
 * Method:    isFinite
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Datatype_isFinite(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Datatype
 * Method:    isWellFounded
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Datatype_isWellFounded(JNIEnv*,
                                                            jobject,
                                                            jlong);

/*
 * Class:     cvc5_Datatype
 * Method:    hasNestedRecursion
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Datatype_hasNestedRecursion(JNIEnv*,
                                                                 jobject,
                                                                 jlong);

/*
 * Class:     cvc5_Datatype
 * Method:    isNull
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Datatype_isNull(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Datatype
 * Method:    toString
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_cvc5_Datatype_toString(JNIEnv*, jobject, jlong);
