#include "cvc5_DatatypeConstructorDecl.h"

#include "api/cpp/cvc5.h"
#include "cvc5JavaApi.h"

using namespace cvc5::api;

/*
 * Class:     cvc5_DatatypeConstructorDecl
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL
Java_cvc5_DatatypeConstructorDecl_deletePointer(JNIEnv*, jclass, jlong pointer)
{
  delete ((DatatypeConstructorDecl*)pointer);
}

/*
 * Class:     cvc5_DatatypeConstructorDecl
 * Method:    addSelector
 * Signature: (JLjava/lang/String;J)V
 */
JNIEXPORT void JNICALL Java_cvc5_DatatypeConstructorDecl_addSelector(
    JNIEnv* env, jobject, jlong pointer, jstring jName, jlong sortPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeConstructorDecl* current = (DatatypeConstructorDecl*)pointer;
  const char* s = env->GetStringUTFChars(jName, nullptr);
  std::string cName(s);
  Sort* sort = (Sort*)sortPointer;
  current->addSelector(cName, *sort);
  env->ReleaseStringUTFChars(jName, s);
  CVC5_JAVA_API_TRY_CATCH_END(env);
}

/*
 * Class:     cvc5_DatatypeConstructorDecl
 * Method:    addSelectorSelf
 * Signature: (JLjava/lang/String;)V
 */
JNIEXPORT void JNICALL Java_cvc5_DatatypeConstructorDecl_addSelectorSelf(
    JNIEnv* env, jobject, jlong pointer, jstring jName)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeConstructorDecl* current = (DatatypeConstructorDecl*)pointer;
  const char* s = env->GetStringUTFChars(jName, nullptr);
  std::string cName(s);
  current->addSelectorSelf(cName);
  env->ReleaseStringUTFChars(jName, s);
  CVC5_JAVA_API_TRY_CATCH_END(env);
}

/*
 * Class:     cvc5_DatatypeConstructorDecl
 * Method:    isNull
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL
Java_cvc5_DatatypeConstructorDecl_isNull(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeConstructorDecl* current = (DatatypeConstructorDecl*)pointer;
  return (jboolean)current->isNull();
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, (jboolean) false);
}

/*
 * Class:     cvc5_DatatypeConstructorDecl
 * Method:    toString
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL
Java_cvc5_DatatypeConstructorDecl_toString(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  DatatypeConstructorDecl* current = (DatatypeConstructorDecl*)pointer;
  return env->NewStringUTF(current->toString().c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}
