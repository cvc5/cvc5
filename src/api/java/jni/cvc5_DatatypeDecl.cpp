#include "cvc5_DatatypeDecl.h"

#include "api/cpp/cvc5.h"
#include "cvc5JavaApi.h"

using namespace cvc5::api;

/*
 * Class:     cvc5_DatatypeDecl
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_cvc5_DatatypeDecl_deletePointer(JNIEnv*,
                                                            jclass,
                                                            jlong);

/*
 * Class:     cvc5_DatatypeDecl
 * Method:    addConstructor
 * Signature: (JJ)V
 */
JNIEXPORT void JNICALL Java_cvc5_DatatypeDecl_addConstructor(JNIEnv* env,
                                                             jobject,
                                                             jlong pointer,
                                                             jlong declPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeDecl* current = (DatatypeDecl*)pointer;
  DatatypeConstructorDecl* decl = (DatatypeConstructorDecl*)declPointer;
  current->addConstructor(*decl);
  CVC5_JAVA_API_TRY_CATCH_END(env);
}

/*
 * Class:     cvc5_DatatypeDecl
 * Method:    getNumConstructors
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_cvc5_DatatypeDecl_getNumConstructors(JNIEnv*,
                                                                 jobject,
                                                                 jlong);

/*
 * Class:     cvc5_DatatypeDecl
 * Method:    isParametric
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_DatatypeDecl_isParametric(JNIEnv*,
                                                               jobject,
                                                               jlong);

/*
 * Class:     cvc5_DatatypeDecl
 * Method:    isNull
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_DatatypeDecl_isNull(JNIEnv*,
                                                         jobject,
                                                         jlong);

/*
 * Class:     cvc5_DatatypeDecl
 * Method:    toString
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_cvc5_DatatypeDecl_toString(JNIEnv*,
                                                          jobject,
                                                          jlong);

/*
 * Class:     cvc5_DatatypeDecl
 * Method:    getName
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_cvc5_DatatypeDecl_getName(JNIEnv*,
                                                         jobject,
                                                         jlong);
