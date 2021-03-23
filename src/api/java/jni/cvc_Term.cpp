#include "cvc_Term.h"

#include "cvc4/api/cvc4cpp.h"
#include "cvcJavaApi.h"

using namespace CVC4::api;

/*
 * Class:     cvc_Term
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_cvc_Term_deletePointer(JNIEnv*,
                                                   jclass,
                                                   jlong pointer)
{
  std::cout << "Deleting Term pointer: " << pointer << std::endl;
  delete ((Term*)pointer);
}

/*
 * Class:     cvc_Term
 * Method:    toString
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_cvc_Term_toString(JNIEnv* env,
                                                 jobject,
                                                 jlong pointer)
{
  Term* term = (Term*)pointer;
  return env->NewStringUTF(term->toString().c_str());
}

/*
 * Class:     cvc_Term
 * Method:    equals
 * Signature: (JJ)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc_Term_equals(JNIEnv* env,
                                                jobject,
                                                jlong pointer1,
                                                jlong pointer2)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Term* term1 = (Term*)pointer1;
  Term* term2 = (Term*)pointer2;
  // We compare the actual terms, not their pointers.
  // Otherwise the two terms may not be equal
  return (jboolean)(*term1 == *term2);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc_Term
 * Method:    eqTerm
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Term_eqTerm(JNIEnv* env,
                                             jobject,
                                             jlong termPointer,
                                             jlong tPointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Term* term = (Term*)termPointer;
  Term* t = (Term*)tPointer;
  Term* ret = new Term(term->eqTerm(*t));
  return ((jlong)ret);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Term
 * Method:    notTerm
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Term_notTerm(JNIEnv* env,
                                              jobject,
                                              jlong termPointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Term* term = (Term*)termPointer;
  Term* ret = new Term(term->notTerm());
  return ((jlong)ret);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}