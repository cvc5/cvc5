/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 Java API.
 */

#include <cvc5/cvc5.h>

#include "api/java/jni/api_utilities.h"
#include "api_plugin.h"
#include "api_utilities.h"
#include "io_github_cvc5_Solver.h"

using namespace cvc5;

/*
 * Class:     io_github_cvc5_Solver
 * Method:    newSolver
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Solver_newSolver(JNIEnv* env,
                                                             jclass,
                                                             jlong tmPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(tmPointer);
  Solver* solver = new Solver(*tm);
  return reinterpret_cast<jlong>(solver);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_io_github_cvc5_Solver_deletePointer(JNIEnv* env,
                                                                jobject,
                                                                jlong pointer)
{
  ApiManager::currentAM()->deletePointer(env, pointer);
  delete (reinterpret_cast<Solver*>(pointer));
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getTermManager
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Solver_getTermManager(JNIEnv* env,
                                                                  jobject,
                                                                  jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  TermManager* tm = &solver->getTermManager();
  return reinterpret_cast<jlong>(tm);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    simplify
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Solver_simplify__JJ(
    JNIEnv* env, jobject, jlong pointer, jlong termPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  Term* term = reinterpret_cast<Term*>(termPointer);
  Term* retPointer = new Term(solver->simplify(*term));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    simplify
 * Signature: (JJZ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Solver_simplify__JJZ(
    JNIEnv* env, jobject, jlong pointer, jlong termPointer, jboolean applySubs)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  Term* term = reinterpret_cast<Term*>(termPointer);
  Term* retPointer = new Term(solver->simplify(*term, (bool)applySubs));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    assertFormula
 * Signature: (JJ)V
 */
JNIEXPORT void JNICALL Java_io_github_cvc5_Solver_assertFormula(
    JNIEnv* env, jobject, jlong pointer, jlong termPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  Term* term = reinterpret_cast<Term*>(termPointer);
  solver->assertFormula(*term);
  CVC5_JAVA_API_TRY_CATCH_END(env);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    checkSat
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Solver_checkSat(JNIEnv* env,
                                                            jobject,
                                                            jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  Result* retPointer = new Result(solver->checkSat());
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    checkSatAssuming
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Solver_checkSatAssuming__JJ(
    JNIEnv* env, jobject, jlong pointer, jlong assumptionPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  Term* assumption = reinterpret_cast<Term*>(assumptionPointer);
  Result* retPointer = new Result(solver->checkSatAssuming(*assumption));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    checkSatAssuming
 * Signature: (J[J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Solver_checkSatAssuming__J_3J(
    JNIEnv* env, jobject, jlong pointer, jlongArray jAssumptions)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  std::vector<Term> assumptions =
      getObjectsFromPointers<Term>(env, jAssumptions);
  Result* retPointer = new Result(solver->checkSatAssuming(assumptions));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    declareDatatype
 * Signature: (JLjava/lang/String;[J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Solver_declareDatatype(
    JNIEnv* env, jobject, jlong pointer, jstring jSymbol, jlongArray jCtors)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  const char* s = env->GetStringUTFChars(jSymbol, nullptr);
  std::string cSymbol(s);
  std::vector<DatatypeConstructorDecl> ctors =
      getObjectsFromPointers<DatatypeConstructorDecl>(env, jCtors);
  Sort* retPointer = new Sort(solver->declareDatatype(cSymbol, ctors));
  env->ReleaseStringUTFChars(jSymbol, s);
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    declareFun
 * Signature: (JLjava/lang/String;[JJ)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_Solver_declareFun__JLjava_lang_String_2_3JJ(
    JNIEnv* env,
    jobject,
    jlong pointer,
    jstring jSymbol,
    jlongArray jSorts,
    jlong sortPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  Sort* sort = reinterpret_cast<Sort*>(sortPointer);
  const char* s = env->GetStringUTFChars(jSymbol, nullptr);
  std::string cSymbol(s);
  std::vector<Sort> sorts = getObjectsFromPointers<Sort>(env, jSorts);
  Term* retPointer = new Term(solver->declareFun(cSymbol, sorts, *sort));
  env->ReleaseStringUTFChars(jSymbol, s);
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    declareFun
 * Signature: (JLjava/lang/String;[JJZ)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_Solver_declareFun__JLjava_lang_String_2_3JJZ(
    JNIEnv* env,
    jobject,
    jlong pointer,
    jstring jSymbol,
    jlongArray jSorts,
    jlong sortPointer,
    jboolean fresh)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  Sort* sort = reinterpret_cast<Sort*>(sortPointer);
  const char* s = env->GetStringUTFChars(jSymbol, nullptr);
  std::string cSymbol(s);
  std::vector<Sort> sorts = getObjectsFromPointers<Sort>(env, jSorts);
  Term* retPointer =
      new Term(solver->declareFun(cSymbol, sorts, *sort, (bool)fresh));
  env->ReleaseStringUTFChars(jSymbol, s);
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    declareSort
 * Signature: (JLjava/lang/String;I)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_Solver_declareSort__JLjava_lang_String_2I(
    JNIEnv* env, jobject, jlong pointer, jstring jSymbol, jint arity)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  const char* s = env->GetStringUTFChars(jSymbol, nullptr);
  std::string cSymbol(s);
  Sort* retPointer = new Sort(solver->declareSort(cSymbol, (uint32_t)arity));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    declareSort
 * Signature: (JLjava/lang/String;IZ)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_Solver_declareSort__JLjava_lang_String_2IZ(JNIEnv* env,
                                                               jobject,
                                                               jlong pointer,
                                                               jstring jSymbol,
                                                               jint arity,
                                                               jboolean fresh)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  const char* s = env->GetStringUTFChars(jSymbol, nullptr);
  std::string cSymbol(s);
  Sort* retPointer =
      new Sort(solver->declareSort(cSymbol, (uint32_t)arity, (bool)fresh));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    defineFun
 * Signature: (JLjava/lang/String;[JJJZ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Solver_defineFun(JNIEnv* env,
                                                             jobject,
                                                             jlong pointer,
                                                             jstring jSymbol,
                                                             jlongArray jVars,
                                                             jlong sortPointer,
                                                             jlong termPointer,
                                                             jboolean global)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  Sort* sort = reinterpret_cast<Sort*>(sortPointer);
  Term* term = reinterpret_cast<Term*>(termPointer);
  const char* s = env->GetStringUTFChars(jSymbol, nullptr);
  std::string cSymbol(s);
  std::vector<Term> vars = getObjectsFromPointers<Term>(env, jVars);
  Term* retPointer =
      new Term(solver->defineFun(cSymbol, vars, *sort, *term, (bool)global));
  env->ReleaseStringUTFChars(jSymbol, s);
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    defineFunRec
 * Signature: (JLjava/lang/String;[JJJZ)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_Solver_defineFunRec__JLjava_lang_String_2_3JJJZ(
    JNIEnv* env,
    jobject,
    jlong pointer,
    jstring jSymbol,
    jlongArray jVars,
    jlong sortPointer,
    jlong termPointer,
    jboolean global)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  Sort* sort = reinterpret_cast<Sort*>(sortPointer);
  Term* term = reinterpret_cast<Term*>(termPointer);
  const char* s = env->GetStringUTFChars(jSymbol, nullptr);
  std::string cSymbol(s);
  std::vector<Term> vars = getObjectsFromPointers<Term>(env, jVars);
  Term* retPointer =
      new Term(solver->defineFunRec(cSymbol, vars, *sort, *term, (bool)global));
  env->ReleaseStringUTFChars(jSymbol, s);
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    defineFunRec
 * Signature: (JJ[JJZ)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_Solver_defineFunRec__JJ_3JJZ(JNIEnv* env,
                                                 jobject,
                                                 jlong pointer,
                                                 jlong funPointer,
                                                 jlongArray jVars,
                                                 jlong termPointer,
                                                 jboolean global)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  Term* fun = reinterpret_cast<Term*>(funPointer);
  Term* term = reinterpret_cast<Term*>(termPointer);
  std::vector<Term> vars = getObjectsFromPointers<Term>(env, jVars);
  Term* retPointer =
      new Term(solver->defineFunRec(*fun, vars, *term, (bool)global));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    defineFunsRec
 * Signature: (J[J[[J[JZ)V
 */
JNIEXPORT void JNICALL
Java_io_github_cvc5_Solver_defineFunsRec(JNIEnv* env,
                                         jobject,
                                         jlong pointer,
                                         jlongArray jFuns,
                                         jobjectArray jVars,
                                         jlongArray jTerms,
                                         jboolean global)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  std::vector<Term> funs = getObjectsFromPointers<Term>(env, jFuns);
  std::vector<Term> terms = getObjectsFromPointers<Term>(env, jTerms);
  std::vector<std::vector<Term>> varsMatrix;
  jsize rows = env->GetArrayLength(jVars);
  for (jint i = 0; i < rows; i++)
  {
    std::vector<Term> vars;
    jlongArray row = (jlongArray)env->GetObjectArrayElement(jVars, i);
    jsize columns = env->GetArrayLength(row);
    jlong* columnElements = env->GetLongArrayElements(row, nullptr);
    for (jint j = 0; j < columns; j++)
    {
      Term* var = reinterpret_cast<Term*>((jlongArray)columnElements[j]);
      vars.push_back(*var);
    }
    varsMatrix.push_back(vars);
  }
  solver->defineFunsRec(funs, varsMatrix, terms, (bool)global);
  CVC5_JAVA_API_TRY_CATCH_END(env);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getLearnedLiterals
 * Signature: (J)[J
 */
JNIEXPORT jlongArray JNICALL Java_io_github_cvc5_Solver_getLearnedLiterals__J(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  std::vector<Term> assertions = solver->getLearnedLiterals();
  jlongArray ret = getPointersFromObjects<Term>(env, assertions);
  return ret;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getLearnedLiterals
 * Signature: (JI)[J
 */
JNIEXPORT jlongArray JNICALL Java_io_github_cvc5_Solver_getLearnedLiterals__JI(
    JNIEnv* env, jobject, jlong pointer, jint typeValue)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  modes::LearnedLitType t = static_cast<modes::LearnedLitType>(typeValue);
  std::vector<Term> assertions = solver->getLearnedLiterals(t);
  jlongArray ret = getPointersFromObjects<Term>(env, assertions);
  return ret;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getAssertions
 * Signature: (J)[J
 */
JNIEXPORT jlongArray JNICALL
Java_io_github_cvc5_Solver_getAssertions(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  std::vector<Term> assertions = solver->getAssertions();
  jlongArray ret = getPointersFromObjects<Term>(env, assertions);
  return ret;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getInfo
 * Signature: (JLjava/lang/String;)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_io_github_cvc5_Solver_getInfo(JNIEnv* env,
                                                             jobject,
                                                             jlong pointer,
                                                             jstring jFlag)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  const char* s = env->GetStringUTFChars(jFlag, nullptr);
  std::string cFlag(s);
  env->ReleaseStringUTFChars(jFlag, s);
  return env->NewStringUTF(solver->getInfo(cFlag).c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getOption
 * Signature: (JLjava/lang/String;)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_io_github_cvc5_Solver_getOption(JNIEnv* env,
                                                               jobject,
                                                               jlong pointer,
                                                               jstring jOption)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  const char* s = env->GetStringUTFChars(jOption, nullptr);
  std::string cOption(s);
  env->ReleaseStringUTFChars(jOption, s);
  return env->NewStringUTF(solver->getOption(cOption).c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getOptionNames
 * Signature: (J)[Ljava/lang/String;
 */
JNIEXPORT jobjectArray JNICALL
Java_io_github_cvc5_Solver_getOptionNames(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  std::vector<std::string> options = solver->getOptionNames();
  jobjectArray ret = getStringArrayFromStringVector(env, options);
  return ret;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getOptionInfo
 * Signature: (JLjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Solver_getOptionInfo(
    JNIEnv* env, jobject, jlong pointer, jstring jOption)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  std::string cOption(env->GetStringUTFChars(jOption, nullptr));
  OptionInfo* ret = new OptionInfo(solver->getOptionInfo(cOption));
  return reinterpret_cast<jlong>(ret);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getDriverOptions
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_Solver_getDriverOptions(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  DriverOptions* ret = new DriverOptions(solver->getDriverOptions());
  return reinterpret_cast<jlong>(ret);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getUnsatAssumptions
 * Signature: (J)[J
 */
JNIEXPORT jlongArray JNICALL Java_io_github_cvc5_Solver_getUnsatAssumptions(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  std::vector<Term> core = solver->getUnsatAssumptions();
  jlongArray ret = getPointersFromObjects<Term>(env, core);
  return ret;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getUnsatCore
 * Signature: (J)[J
 */
JNIEXPORT jlongArray JNICALL
Java_io_github_cvc5_Solver_getUnsatCore(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  std::vector<Term> core = solver->getUnsatCore();
  jlongArray ret = getPointersFromObjects<Term>(env, core);
  return ret;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getUnsatCoreLemmas
 * Signature: (J)[J
 */
JNIEXPORT jlongArray JNICALL Java_io_github_cvc5_Solver_getUnsatCoreLemmas(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  std::vector<Term> core = solver->getUnsatCoreLemmas();
  jlongArray ret = getPointersFromObjects<Term>(env, core);
  return ret;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getDifficulty
 * Signature: (J)Ljava/util/Map;
 */
JNIEXPORT jobject JNICALL
Java_io_github_cvc5_Solver_getDifficulty(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  std::map<Term, Term> map = solver->getDifficulty();
  // HashMap hashMap = new HashMap();
  jclass hashMapClass = env->FindClass("Ljava/util/HashMap;");
  jmethodID constructor = env->GetMethodID(hashMapClass, "<init>", "()V");
  jobject hashMap = env->NewObject(hashMapClass, constructor);
  jmethodID putMethod = env->GetMethodID(
      hashMapClass,
      "put",
      "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;");

  // Long longObject = new Long(statPointer)
  jclass longClass = env->FindClass("Ljava/lang/Long;");
  jmethodID longConstructor = env->GetMethodID(longClass, "<init>", "(J)V");

  for (const auto& [k, v] : map)
  {
    // hashmap.put(key, value);
    Term* termKey = new Term(k);
    Term* termValue = new Term(v);
    jobject key = env->NewObject(
        longClass, longConstructor, reinterpret_cast<jlong>(termKey));
    jobject value = env->NewObject(
        longClass, longConstructor, reinterpret_cast<jlong>(termValue));
    env->CallObjectMethod(hashMap, putMethod, key, value);
  }
  return hashMap;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getTimeoutCore
 * Signature: (J)Lio/github/cvc5/Pair;
 */
JNIEXPORT jobject JNICALL
Java_io_github_cvc5_Solver_getTimeoutCore(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  auto [result, terms] = solver->getTimeoutCore();
  Result* resultPointer = new Result(result);
  jlongArray a = getPointersFromObjects<Term>(env, terms);

  // Long r = new Long(resultPointer);
  jclass longClass = env->FindClass("Ljava/lang/Long;");
  jmethodID longConstructor = env->GetMethodID(longClass, "<init>", "(J)V");
  jobject r = env->NewObject(longClass, longConstructor, resultPointer);

  // Pair pair = new Pair<Long, long[]>(r, a);
  jclass pairClass = env->FindClass("Lio/github/cvc5/Pair;");
  jmethodID pairConstructor = env->GetMethodID(
      pairClass, "<init>", "(Ljava/lang/Object;Ljava/lang/Object;)V");
  jobject pair = env->NewObject(pairClass, pairConstructor, r, a);

  return pair;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getTimeoutCoreAssuming
 * Signature: (J[J)J
 */
JNIEXPORT jobject JNICALL Java_io_github_cvc5_Solver_getTimeoutCoreAssuming(
    JNIEnv* env, jobject, jlong pointer, jlongArray assumptions)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  std::vector<Term> as = getObjectsFromPointers<Term>(env, assumptions);
  auto [result, terms] = solver->getTimeoutCoreAssuming(as);
  Result* resultPointer = new Result(result);
  jlongArray a = getPointersFromObjects<Term>(env, terms);

  // Long r = new Long(resultPointer);
  jclass longClass = env->FindClass("Ljava/lang/Long;");
  jmethodID longConstructor = env->GetMethodID(longClass, "<init>", "(J)V");
  jobject r = env->NewObject(longClass, longConstructor, resultPointer);

  // Pair pair = new Pair<Long, long[]>(r, a);
  jclass pairClass = env->FindClass("Lio/github/cvc5/Pair;");
  jmethodID pairConstructor = env->GetMethodID(
      pairClass, "<init>", "(Ljava/lang/Object;Ljava/lang/Object;)V");
  jobject pair = env->NewObject(pairClass, pairConstructor, r, a);

  return pair;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getProof
 * Signature: (J)[J
 */
JNIEXPORT jlongArray JNICALL
Java_io_github_cvc5_Solver_getProof__J(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  std::vector<Proof> proofs = solver->getProof();
  jlongArray ret = getPointersFromObjects<Proof>(env, proofs);
  return ret;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getProof
 * Signature: (JI)[J;
 */
JNIEXPORT jlongArray JNICALL Java_io_github_cvc5_Solver_getProof__JI(
    JNIEnv* env, jobject, jlong pointer, jint pcvalue)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  modes::ProofComponent pc = static_cast<modes::ProofComponent>(pcvalue);
  std::vector<Proof> proofs = solver->getProof(pc);
  jlongArray ret = getPointersFromObjects<Proof>(env, proofs);
  return ret;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    proofToString
 * Signature: (JJ)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_io_github_cvc5_Solver_proofToString__JJ(
    JNIEnv* env, jobject, jlong pointer, jlong proofPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  Proof* proof = reinterpret_cast<Proof*>(proofPointer);
  std::string proofStr = solver->proofToString(*proof);
  return env->NewStringUTF(proofStr.c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    proofToString
 * Signature: (JJI)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_io_github_cvc5_Solver_proofToString__JJI(
    JNIEnv* env, jobject, jlong pointer, jlong proofPointer, jint pfvalue)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  modes::ProofFormat pf = static_cast<modes::ProofFormat>(pfvalue);
  Proof* proof = reinterpret_cast<Proof*>(proofPointer);
  std::string proofStr = solver->proofToString(*proof, pf);
  return env->NewStringUTF(proofStr.c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    proofToString
 * Signature: (JJILjava/util/Map;)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL
Java_io_github_cvc5_Solver_proofToString__JJILjava_util_Map_2(
    JNIEnv* env,
    jobject,
    jlong pointer,
    jlong proofPointer,
    jint pfvalue,
    jobject assertionNames)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  modes::ProofFormat pf = static_cast<modes::ProofFormat>(pfvalue);
  Proof* proof = reinterpret_cast<Proof*>(proofPointer);

  jclass c_map = env->GetObjectClass(assertionNames);
  jmethodID id_entrySet =
      env->GetMethodID(c_map, "entrySet", "()Ljava/util/Set;");

  jclass c_entryset = env->FindClass("java/util/Set");
  jmethodID id_iterator =
      env->GetMethodID(c_entryset, "iterator", "()Ljava/util/Iterator;");

  jclass c_iterator = env->FindClass("java/util/Iterator");
  jmethodID id_hasNext = env->GetMethodID(c_iterator, "hasNext", "()Z");
  jmethodID id_next =
      env->GetMethodID(c_iterator, "next", "()Ljava/lang/Object;");

  jclass c_entry = env->FindClass("java/util/Map$Entry");
  jmethodID id_getKey =
      env->GetMethodID(c_entry, "getKey", "()Ljava/lang/Object;");
  jmethodID id_getValue =
      env->GetMethodID(c_entry, "getValue", "()Ljava/lang/Object;");

  jclass c_term = env->FindClass("io/github/cvc5/Term");
  jmethodID id_getPointer = env->GetMethodID(c_term, "getPointer", "()J");

  jobject obj_entrySet = env->CallObjectMethod(assertionNames, id_entrySet);
  jobject obj_iterator = env->CallObjectMethod(obj_entrySet, id_iterator);

  std::map<Term, std::string> namesMap;

  while ((bool)env->CallBooleanMethod(obj_iterator, id_hasNext))
  {
    jobject entry = env->CallObjectMethod(obj_iterator, id_next);

    jobject key = env->CallObjectMethod(entry, id_getKey);
    jstring value = (jstring)env->CallObjectMethod(entry, id_getValue);

    jlong termPointer = (jlong)env->CallObjectMethod(key, id_getPointer);
    Term term = *reinterpret_cast<Term*>(termPointer);

    const char* termName = (env)->GetStringUTFChars(value, 0);
    std::string termNameString = std::string(termName);
    (env)->ReleaseStringUTFChars(value, termName);

    namesMap.insert(std::pair{term, termNameString});
  }

  std::string proofStr = solver->proofToString(*proof, pf, namesMap);
  return env->NewStringUTF(proofStr.c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getValue
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Solver_getValue__JJ(
    JNIEnv* env, jobject, jlong pointer, jlong termPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  Term* term = reinterpret_cast<Term*>(termPointer);
  Term* retPointer = new Term(solver->getValue(*term));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getValue
 * Signature: (J[J)[J
 */
JNIEXPORT jlongArray JNICALL Java_io_github_cvc5_Solver_getValue__J_3J(
    JNIEnv* env, jobject, jlong pointer, jlongArray termPointers)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  std::vector<Term> terms = getObjectsFromPointers<Term>(env, termPointers);
  std::vector<Term> values = solver->getValue(terms);
  jlongArray ret = getPointersFromObjects<Term>(env, values);
  return ret;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getModelDomainElements
 * Signature: (JJ)[J
 */
JNIEXPORT jlongArray JNICALL Java_io_github_cvc5_Solver_getModelDomainElements(
    JNIEnv* env, jobject, jlong pointer, jlong sortPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  Sort* sort = reinterpret_cast<Sort*>(sortPointer);
  std::vector<Term> terms = solver->getModelDomainElements(*sort);
  jlongArray ret = getPointersFromObjects<Term>(env, terms);
  return ret;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    isModelCoreSymbol
 * Signature: (JJ)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Solver_isModelCoreSymbol(
    JNIEnv* env, jobject, jlong pointer, jlong termPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  Term* term = reinterpret_cast<Term*>(termPointer);
  return static_cast<jboolean>(solver->isModelCoreSymbol(*term));
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getModel
 * Signature: (J[J[J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL
Java_io_github_cvc5_Solver_getModel(JNIEnv* env,
                                    jobject,
                                    jlong pointer,
                                    jlongArray sortPointers,
                                    jlongArray varPointers)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  std::vector<Sort> sorts = getObjectsFromPointers<Sort>(env, sortPointers);
  std::vector<Term> vars = getObjectsFromPointers<Term>(env, varPointers);
  std::string model = solver->getModel(sorts, vars);
  return env->NewStringUTF(model.c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getQuantifierElimination
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Solver_getQuantifierElimination(
    JNIEnv* env, jobject, jlong pointer, jlong qPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  Term* q = reinterpret_cast<Term*>(qPointer);
  Term* retPointer = new Term(solver->getQuantifierElimination(*q));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getQuantifierEliminationDisjunct
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_Solver_getQuantifierEliminationDisjunct(JNIEnv* env,
                                                            jobject,
                                                            jlong pointer,
                                                            jlong qPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  Term* q = reinterpret_cast<Term*>(qPointer);
  Term* retPointer = new Term(solver->getQuantifierEliminationDisjunct(*q));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    declareSepHeap
 * Signature: (JJJ)V
 */
JNIEXPORT void JNICALL
Java_io_github_cvc5_Solver_declareSepHeap(JNIEnv* env,
                                          jobject,
                                          jlong pointer,
                                          jlong locSortPointer,
                                          jlong dataSortPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  Sort* locSort = reinterpret_cast<Sort*>(locSortPointer);
  Sort* dataSort = reinterpret_cast<Sort*>(dataSortPointer);
  solver->declareSepHeap(*locSort, *dataSort);
  CVC5_JAVA_API_TRY_CATCH_END(env);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getValueSepHeap
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_Solver_getValueSepHeap(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  Term* retPointer = new Term(solver->getValueSepHeap());
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getValueSepNil
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Solver_getValueSepNil(JNIEnv* env,
                                                                  jobject,
                                                                  jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  Term* retPointer = new Term(solver->getValueSepNil());
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    declarePool
 * Signature: (Ljava/lang/String;J[J])J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_Solver_declarePool(JNIEnv* env,
                                       jobject,
                                       jlong pointer,
                                       jstring jsymbol,
                                       jlong sort,
                                       jlongArray initValuePointers)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  const char* s = env->GetStringUTFChars(jsymbol, nullptr);
  std::string symbol(s);
  Sort* sortptr = reinterpret_cast<Sort*>(sort);
  std::vector<Term> initValue =
      getObjectsFromPointers<Term>(env, initValuePointers);
  Term* retPointer = new Term(solver->declarePool(symbol, *sortptr, initValue));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    declareOracleFun
 * Signature: (JLjava/lang/String;[JJLio/github/cvc5/IOracle;)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_Solver_declareOracleFun(JNIEnv* env,
                                            jobject,
                                            jlong pointer,
                                            jstring jSymbol,
                                            jlongArray sortPointers,
                                            jlong sortPointer,
                                            jobject oracle)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  ApiManager* am = ApiManager::currentAM();
  jobject oracleReference = am->addGlobalReference(env, pointer, oracle);
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  const char* s = env->GetStringUTFChars(jSymbol, nullptr);
  std::string cSymbol(s);
  Sort* sort = reinterpret_cast<Sort*>(sortPointer);
  std::vector<Sort> sorts = getObjectsFromPointers<Sort>(env, sortPointers);
  std::function<Term(std::vector<Term>)> fn =
      [env, oracleReference](std::vector<Term> input) {
        Term term = applyOracle(env, oracleReference, input);
        return term;
      };
  Term* retPointer =
      new Term(solver->declareOracleFun(cSymbol, sorts, *sort, fn));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    addPlugin
 * Signature: (JJLio/github/cvc5/AbstractPlugin;)V
 */
JNIEXPORT void JNICALL
Java_io_github_cvc5_Solver_addPlugin(JNIEnv* env,
                                     jobject,
                                     jlong pointer,
                                     jlong termManagerPointer,
                                     jobject plugin)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  ApiManager* am = ApiManager::currentAM();
  jobject pluginReference = am->addGlobalReference(env, pointer, plugin);
  ApiPlugin* p = new ApiPlugin(*tm, env, pluginReference);
  am->addPluginPointer(pointer, reinterpret_cast<jlong>(p));
  solver->addPlugin(*p);

  CVC5_JAVA_API_TRY_CATCH_END(env);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    pop
 * Signature: (JI)V
 */
JNIEXPORT void JNICALL Java_io_github_cvc5_Solver_pop(JNIEnv* env,
                                                      jobject,
                                                      jlong pointer,
                                                      jint nscopes)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  solver->pop((uint32_t)nscopes);
  CVC5_JAVA_API_TRY_CATCH_END(env);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getInterpolant
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Solver_getInterpolant__JJ(
    JNIEnv* env, jobject, jlong pointer, jlong conjPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  Term* conj = reinterpret_cast<Term*>(conjPointer);
  Term* result = new Term(solver->getInterpolant(*conj));
  return reinterpret_cast<jlong>(result);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getInterpolant
 * Signature: (JJJ)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_Solver_getInterpolant__JJJ(JNIEnv* env,
                                               jobject,
                                               jlong pointer,
                                               jlong conjPointer,
                                               jlong grammarPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  Term* conj = reinterpret_cast<Term*>(conjPointer);
  Grammar* grammar = reinterpret_cast<Grammar*>(grammarPointer);
  Term* result = new Term(solver->getInterpolant(*conj, *grammar));
  return reinterpret_cast<jlong>(result);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getInterpolantNext
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Solver_getInterpolantNext(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  Term* result = new Term(solver->getInterpolantNext());
  return reinterpret_cast<jlong>(result);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getAbduct
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Solver_getAbduct__JJ(
    JNIEnv* env, jobject, jlong pointer, jlong conjPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  Term* conj = reinterpret_cast<Term*>(conjPointer);
  Term* result = new Term(solver->getAbduct(*conj));
  return reinterpret_cast<jlong>(result);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getAbduct
 * Signature: (JJJ)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_Solver_getAbduct__JJJ(JNIEnv* env,
                                          jobject,
                                          jlong pointer,
                                          jlong conjPointer,
                                          jlong grammarPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  Term* conj = reinterpret_cast<Term*>(conjPointer);
  Grammar* grammar = reinterpret_cast<Grammar*>(grammarPointer);
  Term* result = new Term(solver->getAbduct(*conj, *grammar));
  return reinterpret_cast<jlong>(result);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getAbductNext
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Solver_getAbductNext(JNIEnv* env,
                                                                 jobject,
                                                                 jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  Term* result = new Term(solver->getAbductNext());
  return reinterpret_cast<jlong>(result);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    blockModel
 * Signature: (JI)V
 */
JNIEXPORT void JNICALL Java_io_github_cvc5_Solver_blockModel(JNIEnv* env,
                                                             jobject,
                                                             jlong pointer,
                                                             jint modeValue)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  modes::BlockModelsMode mode = static_cast<modes::BlockModelsMode>(modeValue);
  solver->blockModel(mode);
  CVC5_JAVA_API_TRY_CATCH_END(env);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    blockModelValues
 * Signature: (J[J)V
 */
JNIEXPORT void JNICALL Java_io_github_cvc5_Solver_blockModelValues(
    JNIEnv* env, jobject, jlong pointer, jlongArray jTerms)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  std::vector<Term> terms = getObjectsFromPointers<Term>(env, jTerms);
  solver->blockModelValues(terms);
  CVC5_JAVA_API_TRY_CATCH_END(env);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getInstantiations
 * Signature: (J[J[J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_io_github_cvc5_Solver_getInstantiations(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  std::string insts = solver->getInstantiations();
  return env->NewStringUTF(insts.c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    push
 * Signature: (JI)V
 */
JNIEXPORT void JNICALL Java_io_github_cvc5_Solver_push(JNIEnv* env,
                                                       jobject,
                                                       jlong pointer,
                                                       jint nscopes)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  solver->push((uint32_t)nscopes);
  CVC5_JAVA_API_TRY_CATCH_END(env);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    resetAssertions
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_io_github_cvc5_Solver_resetAssertions(JNIEnv* env,
                                                                  jobject,
                                                                  jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  solver->resetAssertions();
  CVC5_JAVA_API_TRY_CATCH_END(env);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    setInfo
 * Signature: (JLjava/lang/String;Ljava/lang/String;)V
 */
JNIEXPORT void JNICALL Java_io_github_cvc5_Solver_setInfo(
    JNIEnv* env, jobject, jlong pointer, jstring jKeyword, jstring jValue)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  const char* sKeyword = env->GetStringUTFChars(jKeyword, nullptr);
  const char* sValue = env->GetStringUTFChars(jValue, nullptr);
  std::string cKeyword(sKeyword);
  std::string cValue(sValue);
  solver->setInfo(cKeyword, cValue);
  env->ReleaseStringUTFChars(jKeyword, sKeyword);
  env->ReleaseStringUTFChars(jValue, sValue);
  CVC5_JAVA_API_TRY_CATCH_END(env);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    setLogic
 * Signature: (JLjava/lang/String;)V
 */
JNIEXPORT void JNICALL Java_io_github_cvc5_Solver_setLogic(JNIEnv* env,
                                                           jobject,
                                                           jlong pointer,
                                                           jstring jLogic)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  const char* cLogic = env->GetStringUTFChars(jLogic, nullptr);
  solver->setLogic(std::string(cLogic));
  CVC5_JAVA_API_TRY_CATCH_END(env);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    isLogicSet
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_io_github_cvc5_Solver_isLogicSet(JNIEnv* env,
                                                                 jobject,
                                                                 jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  return static_cast<jboolean>(solver->isLogicSet());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, static_cast<jboolean>(false));
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getLogic
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_io_github_cvc5_Solver_getLogic(JNIEnv* env,
                                                              jobject,
                                                              jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  return env->NewStringUTF(solver->getLogic().c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    setOption
 * Signature: (JLjava/lang/String;Ljava/lang/String;)V
 */
JNIEXPORT void JNICALL Java_io_github_cvc5_Solver_setOption(
    JNIEnv* env, jobject, jlong pointer, jstring jOption, jstring jValue)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  const char* sOption = env->GetStringUTFChars(jOption, nullptr);
  const char* sValue = env->GetStringUTFChars(jValue, nullptr);
  std::string cOption(sOption);
  std::string cValue(sValue);
  solver->setOption(cOption, cValue);
  env->ReleaseStringUTFChars(jOption, sOption);
  env->ReleaseStringUTFChars(jValue, sValue);
  CVC5_JAVA_API_TRY_CATCH_END(env);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    declareSygusVar
 * Signature: (JJjava/lang/String;L)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Solver_declareSygusVar(
    JNIEnv* env, jobject, jlong pointer, jstring jSymbol, jlong sortPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  Sort* sort = reinterpret_cast<Sort*>(sortPointer);
  const char* s = env->GetStringUTFChars(jSymbol, nullptr);
  std::string cSymbol(s);
  Term* retPointer = new Term(solver->declareSygusVar(cSymbol, *sort));
  env->ReleaseStringUTFChars(jSymbol, s);
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    mkGrammar
 * Signature: (J[J[J)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_Solver_mkGrammar(JNIEnv* env,
                                     jobject,
                                     jlong pointer,
                                     jlongArray jBoundVars,
                                     jlongArray jNtSymbols)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  std::vector<Term> boundVars = getObjectsFromPointers<Term>(env, jBoundVars);
  std::vector<Term> ntSymbols = getObjectsFromPointers<Term>(env, jNtSymbols);
  Grammar* retPointer = new Grammar(solver->mkGrammar(boundVars, ntSymbols));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    synthFun
 * Signature: (JLjava/lang/String;[JJ)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_Solver_synthFun__JLjava_lang_String_2_3JJ(JNIEnv* env,
                                                              jobject,
                                                              jlong pointer,
                                                              jstring jSymbol,
                                                              jlongArray jVars,
                                                              jlong sortPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  Sort* sort = reinterpret_cast<Sort*>(sortPointer);
  const char* s = env->GetStringUTFChars(jSymbol, nullptr);
  std::string cSymbol(s);
  std::vector<Term> boundVars = getObjectsFromPointers<Term>(env, jVars);
  Term* retPointer = new Term(solver->synthFun(cSymbol, boundVars, *sort));
  env->ReleaseStringUTFChars(jSymbol, s);
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    synthFun
 * Signature: (JLjava/lang/String;[JJJ)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_Solver_synthFun__JLjava_lang_String_2_3JJJ(
    JNIEnv* env,
    jobject,
    jlong pointer,
    jstring jSymbol,
    jlongArray jVars,
    jlong sortPointer,
    jlong grammarPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  Sort* sort = reinterpret_cast<Sort*>(sortPointer);
  Grammar* grammar = reinterpret_cast<Grammar*>(grammarPointer);
  const char* s = env->GetStringUTFChars(jSymbol, nullptr);
  std::string cSymbol(s);
  std::vector<Term> boundVars = getObjectsFromPointers<Term>(env, jVars);
  Term* retPointer =
      new Term(solver->synthFun(cSymbol, boundVars, *sort, *grammar));
  env->ReleaseStringUTFChars(jSymbol, s);
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    addSygusConstraint
 * Signature: (JJ)V
 */
JNIEXPORT void JNICALL Java_io_github_cvc5_Solver_addSygusConstraint(
    JNIEnv* env, jobject, jlong pointer, jlong termPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  Term* term = reinterpret_cast<Term*>(termPointer);
  solver->addSygusConstraint(*term);
  CVC5_JAVA_API_TRY_CATCH_END(env);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getSygusConstraints
 * Signature: (J)[J
 */
JNIEXPORT jlongArray JNICALL Java_io_github_cvc5_Solver_getSygusConstraints(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  std::vector<Term> constraints = solver->getSygusConstraints();
  jlongArray ret = getPointersFromObjects<Term>(env, constraints);
  return ret;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    addSygusAssume
 * Signature: (JJ)V
 */
JNIEXPORT void JNICALL Java_io_github_cvc5_Solver_addSygusAssume(
    JNIEnv* env, jobject, jlong pointer, jlong termPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  Term* term = reinterpret_cast<Term*>(termPointer);
  solver->addSygusAssume(*term);
  CVC5_JAVA_API_TRY_CATCH_END(env);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getSygusAssumptions
 * Signature: (J)[J
 */
JNIEXPORT jlongArray JNICALL Java_io_github_cvc5_Solver_getSygusAssumptions(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  std::vector<Term> assumptions = solver->getSygusAssumptions();
  jlongArray ret = getPointersFromObjects<Term>(env, assumptions);
  return ret;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    addSygusInvConstraint
 * Signature: (JJJJJ)V
 */
JNIEXPORT void JNICALL
Java_io_github_cvc5_Solver_addSygusInvConstraint(JNIEnv* env,
                                                 jobject,
                                                 jlong pointer,
                                                 jlong invPointer,
                                                 jlong prePointer,
                                                 jlong transPointer,
                                                 jlong postPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  Term* inv = reinterpret_cast<Term*>(invPointer);
  Term* pre = reinterpret_cast<Term*>(prePointer);
  Term* trans = reinterpret_cast<Term*>(transPointer);
  Term* post = reinterpret_cast<Term*>(postPointer);
  solver->addSygusInvConstraint(*inv, *pre, *trans, *post);
  CVC5_JAVA_API_TRY_CATCH_END(env);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    checkSynth
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Solver_checkSynth(JNIEnv* env,
                                                              jobject,
                                                              jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  SynthResult* retPointer = new SynthResult(solver->checkSynth());
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    checkSynthNext
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Solver_checkSynthNext(JNIEnv* env,
                                                                  jobject,
                                                                  jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  SynthResult* retPointer = new SynthResult(solver->checkSynthNext());
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getSynthSolution
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Solver_getSynthSolution(
    JNIEnv* env, jobject, jlong pointer, jlong termPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  Term* term = reinterpret_cast<Term*>(termPointer);
  Term* retPointer = new Term(solver->getSynthSolution(*term));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getSynthSolutions
 * Signature: (J[J)[J
 */
JNIEXPORT jlongArray JNICALL Java_io_github_cvc5_Solver_getSynthSolutions(
    JNIEnv* env, jobject, jlong pointer, jlongArray jTerms)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  std::vector<Term> terms = getObjectsFromPointers<Term>(env, jTerms);
  std::vector<Term> solutions = solver->getSynthSolutions(terms);
  jlongArray ret = getPointersFromObjects<Term>(env, solutions);
  return ret;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    findSynth
 * Signature: (JI)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Solver_findSynth__JI(JNIEnv* env,
                                                                 jobject,
                                                                 jlong pointer,
                                                                 jint fstvalue)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  modes::FindSynthTarget fst = static_cast<modes::FindSynthTarget>(fstvalue);
  Term* retPointer = new Term(solver->findSynth(fst));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    findSynth
 * Signature: (JIJ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Solver_findSynth__JIJ(
    JNIEnv* env, jobject, jlong pointer, jint fstvalue, jlong grammarPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  modes::FindSynthTarget fst = static_cast<modes::FindSynthTarget>(fstvalue);
  Grammar* grammar = reinterpret_cast<Grammar*>(grammarPointer);
  Term* retPointer = new Term(solver->findSynth(fst, *grammar));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    findSynthNext
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Solver_findSynthNext(JNIEnv* env,
                                                                 jobject,
                                                                 jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  Term* retPointer = new Term(solver->findSynthNext());
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getStatistics
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_Solver_getStatistics(JNIEnv* env,
                                                                 jobject,
                                                                 jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  Statistics* retPointer = new Statistics(solver->getStatistics());
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_Solver
 * Method:    getVersion
 * Signature: (JLjava/lang/String;)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_io_github_cvc5_Solver_getVersion(JNIEnv* env,
                                                                jobject,
                                                                jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = reinterpret_cast<Solver*>(pointer);
  return env->NewStringUTF(solver->getVersion().c_str());
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}
