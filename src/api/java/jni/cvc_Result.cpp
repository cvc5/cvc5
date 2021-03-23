#include "cvc_Result.h"

#include "cvc4/api/cvc4cpp.h"
#include "cvcJavaApi.h"

using namespace CVC4::api;

/*
 * Class:     cvc_Result
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_cvc_Result_deletePointer(JNIEnv*,
                                                     jclass,
                                                     jlong pointer)
{
  std::cout << "Deleting Result: " << pointer << std::endl;
  delete ((Result*)pointer);
}

/*
 * Class:     cvc_Result
 * Method:    toString
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_cvc_Result_toString(JNIEnv* env,
                                                   jobject,
                                                   jlong resultPointer)
{
  Result* result = (Result*)resultPointer;
  return env->NewStringUTF(result->toString().c_str());
}