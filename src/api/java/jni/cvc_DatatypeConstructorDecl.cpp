#include "cvc_DatatypeConstructorDecl.h"

#include "cvc4/api/cvc4cpp.h"
#include "cvcJavaApi.h"

using namespace CVC4::api;

/*
 * Class:     cvc_DatatypeConstructorDecl
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL
Java_cvc_DatatypeConstructorDecl_deletePointer(JNIEnv*, jclass, jlong pointer)
{
  std::cout << "Deleting DatatypeConstructorDecl pointer: " << pointer
            << std::endl;
  delete ((DatatypeConstructorDecl*)pointer);
}

/*
 * Class:     cvc_DatatypeConstructorDecl
 * Method:    toString
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL
Java_cvc_DatatypeConstructorDecl_toString(JNIEnv* env, jobject, jlong pointer)
{
  DatatypeConstructorDecl* decl = (DatatypeConstructorDecl*)pointer;
  return env->NewStringUTF(decl->toString().c_str());
}

/*
 * Class:     cvc_DatatypeConstructorDecl
 * Method:    addSelector
 * Signature: (JLjava/lang/String;J)V
 */
JNIEXPORT void JNICALL Java_cvc_DatatypeConstructorDecl_addSelector(
    JNIEnv* env, jobject, jlong pointer, jstring jName, jlong sortPointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeConstructorDecl* decl = (DatatypeConstructorDecl*)pointer;
  const char* cName = env->GetStringUTFChars(jName, nullptr);
  Sort* sort = (Sort*)sortPointer;
  decl->addSelector(std::string(cName), *sort);
  CVC_JAVA_API_TRY_CATCH_END(env);
}
