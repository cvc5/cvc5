#include "cvc_Sort.h"

#include "cvc4/api/cvc4cpp.h"
#include "cvcJavaApi.h"

using namespace CVC4::api;

/*
 * Class:     cvc_Sort
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_cvc_Sort_deletePointer(JNIEnv*,
                                                   jclass,
                                                   jlong pointer)
{
  std::cout << "Deleting Sort pointer: " << pointer << std::endl;
  delete ((Sort*)pointer);
}

/*
 * Class:     cvc_Sort
 * Method:    toString
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_cvc_Sort_toString(JNIEnv* env,
                                                 jobject,
                                                 jlong sortPointer)
{
  Sort* sort = (Sort*)sortPointer;
  return env->NewStringUTF(sort->toString().c_str());
}

/*
 * Class:     cvc_Sort
 * Method:    getDatatype
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Sort_getDatatype(JNIEnv* env,
                                                  jobject,
                                                  jlong pointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Sort* sort = (Sort*)pointer;
  Datatype* datatype = new Datatype(sort->getDatatype());
  return (jlong)datatype;
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}