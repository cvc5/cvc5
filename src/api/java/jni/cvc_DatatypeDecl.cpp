#include "cvc_DatatypeDecl.h"

#include "cvc4/api/cvc4cpp.h"
#include "cvcJavaApi.h"

using namespace CVC4::api;

/*
 * Class:     cvc_DatatypeDecl
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_cvc_DatatypeDecl_deletePointer(JNIEnv*,
                                                           jclass,
                                                           jlong pointer)
{
  std::cout << "Deleting DatatypeDecl pointer: " << pointer << std::endl;
  delete ((DatatypeDecl*)pointer);
}

/*
 * Class:     cvc_DatatypeDecl
 * Method:    toString
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_cvc_DatatypeDecl_toString(JNIEnv* env,
                                                         jobject,
                                                         jlong pointer)
{
  DatatypeDecl* datatypeDecl = (DatatypeDecl*)pointer;
  return env->NewStringUTF(datatypeDecl->toString().c_str());
}

/*
 * Class:     cvc_DatatypeDecl
 * Method:    addConstructor
 * Signature: (JJ)V
 */
JNIEXPORT void JNICALL Java_cvc_DatatypeDecl_addConstructor(
    JNIEnv* env, jobject, jlong pointer, jlong datatypeConstructorDeclPointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeDecl* datatypeDecl = (DatatypeDecl*)pointer;
  DatatypeConstructorDecl* decl =
      (DatatypeConstructorDecl*)datatypeConstructorDeclPointer;
  datatypeDecl->addConstructor(*decl);
  CVC_JAVA_API_TRY_CATCH_END(env);
}
