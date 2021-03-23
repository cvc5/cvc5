#include "cvc4/api/cvc4cpp.h"
#include "cvcJavaApi.h"
#include "cvc_Result.h"

using namespace CVC4::api;

/*
 * Class:     cvc_Datatype
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_cvc_Datatype_deletePointer(JNIEnv*,
                                                       jclass,
                                                       jlong pointer)
{
  std::cout << "Deleting datatype pointer: " << pointer << std::endl;
  delete ((Datatype*)pointer);
}

/*
 * Class:     cvc_Datatype
 * Method:    toString
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_cvc_Datatype_toString(JNIEnv* env,
                                                     jobject,
                                                     jlong pointer)
{
  Datatype* datatype = (Datatype*)pointer;
  return env->NewStringUTF(datatype->toString().c_str());
}
