#include "cvc5_Solver.h"

#include "api/cpp/cvc5.h"
#include "cvc5JavaApi.h"

using namespace cvc5::api;

/*
 * Class:     cvc5_Solver
 * Method:    newSolver
 * Signature: ()J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_newSolver(JNIEnv*, jobject)
{
  Solver* solver = new Solver();
  return ((jlong)solver);
}

/*
 * Class:     cvc5_Solver
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_cvc5_Solver_deletePointer(JNIEnv*,
                                                      jclass,
                                                      jlong pointer)
{
  delete ((Solver*)pointer);
}

/*
 * Class:     cvc5_Solver
 * Method:    setLogic
 * Signature: (Ljava/lang/String;)V
 */
JNIEXPORT void JNICALL Java_cvc5_Solver_setLogic(JNIEnv* env,
                                                 jobject,
                                                 jlong solverPointer,
                                                 jstring jLogic)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;

  Solver* solver = (Solver*)solverPointer;
  const char* cLogic = env->GetStringUTFChars(jLogic, nullptr);
  solver->setLogic(std::string(cLogic));

  CVC5_JAVA_API_TRY_CATCH_END(env);
}

/*
 * Class:     cvc5_Solver
 * Method:    mkUninterpretedSort
 * Signature: (JLjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkUninterpretedSort(JNIEnv* env,
                                                             jobject,
                                                             jlong pointer,
                                                             jstring jSymbol)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;

  Solver* solver = (Solver*)pointer;
  const char* cSymbol = env->GetStringUTFChars(jSymbol, nullptr);
  Sort* sort = new Sort(solver->mkUninterpretedSort(std::string(cSymbol)));
  env->ReleaseStringUTFChars(jSymbol, cSymbol);
  return (jlong)sort;

  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Solver
 * Method:    mkVar
 * Signature: (JJLjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkVar(
    JNIEnv* env, jobject, jlong pointer, jlong sortPointer, jstring jSymbol)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;

  Solver* solver = (Solver*)pointer;
  Sort* sort = (Sort*)sortPointer;
  const char* s = env->GetStringUTFChars(jSymbol, nullptr);
  std::string cSymbol(s);
  Term* ret = new Term(solver->mkVar(*sort, cSymbol));
  env->ReleaseStringUTFChars(jSymbol, s);
  return ((jlong)ret);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Solver
 * Method:    getIntegerSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_getIntegerSort(JNIEnv* env,
                                                        jobject,
                                                        jlong solverPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)solverPointer;
  Sort* sortPointer = new Sort(solver->getIntegerSort());
  return ((jlong)sortPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Solver
 * Method:    getNullTerm
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_getNullTerm(JNIEnv* env,
                                                     jobject,
                                                     jlong)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Term* ret = new Term();
  return ((jlong)ret);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}