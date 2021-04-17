#include "cvc5_DatatypeSelector.h"

#include "api/cpp/cvc5.h"
#include "cvc5JavaApi.h"

using namespace cvc5::api;

/*
 * Class:     cvc5_DatatypeSelector
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_cvc5_DatatypeSelector_deletePointer(JNIEnv*,
                                                                jclass,
                                                                jlong);

/*
 * Class:     cvc5_DatatypeSelector
 * Method:    getName
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_cvc5_DatatypeSelector_getName(JNIEnv*,
                                                             jobject,
                                                             jlong);

/*
 * Class:     cvc5_DatatypeSelector
 * Method:    getSelectorTerm
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL
Java_cvc5_DatatypeSelector_getSelectorTerm(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeSelector* current = (DatatypeSelector*)pointer;
  Term* retPointer = new Term(current->getSelectorTerm());
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_DatatypeSelector
 * Method:    getRangeSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_DatatypeSelector_getRangeSort(JNIEnv*,
                                                                jobject,
                                                                jlong);

/*
 * Class:     cvc5_DatatypeSelector
 * Method:    isNull
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_DatatypeSelector_isNull(JNIEnv*,
                                                             jobject,
                                                             jlong);

/*
 * Class:     cvc5_DatatypeSelector
 * Method:    toString
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_cvc5_DatatypeSelector_toString(JNIEnv*,
                                                              jobject,
                                                              jlong);
