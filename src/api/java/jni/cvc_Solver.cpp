#include "cvc_Solver.h"

#include "api/cpp/cvc5.h"
#include "cvcJavaApi.h"

using namespace cvc5::api;

/*
 * Class:     cvc_Solver
 * Method:    newSolver
 * Signature: ()J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_newSolver(JNIEnv*, jobject)
{
  Solver* solver = new Solver();
  return ((jlong)solver);
}

/*
 * Class:     cvc_Solver
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_cvc_Solver_deletePointer(JNIEnv*,
                                                     jclass,
                                                     jlong pointer)
{
  delete ((Solver*)pointer);
}

/*
 * Class:     cvc_Solver
 * Method:    setLogic
 * Signature: (Ljava/lang/String;)V
 */
JNIEXPORT void JNICALL Java_cvc_Solver_setLogic(JNIEnv* env,
                                                jobject,
                                                jlong solverPointer,
                                                jstring jLogic)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;

  Solver* solver = (Solver*)solverPointer;
  const char* cLogic = env->GetStringUTFChars(jLogic, nullptr);
  solver->setLogic(std::string(cLogic));

  CVC_JAVA_API_TRY_CATCH_END(env);
}
