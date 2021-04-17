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
 * Method:    supportsFloatingPoint
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Solver_supportsFloatingPoint(JNIEnv*,
                                                                  jobject,
                                                                  jlong);

/*
 * Class:     cvc5_Solver
 * Method:    getNullSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_getNullSort(JNIEnv* env,
                                                     jobject,
                                                     jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Sort* sortPointer = new Sort(solver->getNullSort());
  return ((jlong)sortPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Solver
 * Method:    getBooleanSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_getBooleanSort(JNIEnv* env,
                                                        jobject,
                                                        jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Sort* sortPointer = new Sort(solver->getBooleanSort());
  return ((jlong)sortPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Solver
 * Method:    getIntegerSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_getIntegerSort(JNIEnv* env,
                                                        jobject,
                                                        jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Sort* sortPointer = new Sort(solver->getIntegerSort());
  return ((jlong)sortPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Solver
 * Method:    getRealSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_getRealSort(JNIEnv* env,
                                                     jobject,
                                                     jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Sort* sortPointer = new Sort(solver->getRealSort());
  return ((jlong)sortPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Solver
 * Method:    getRegExpSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_getRegExpSort(JNIEnv* env,
                                                       jobject,
                                                       jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Sort* sortPointer = new Sort(solver->getRegExpSort());
  return ((jlong)sortPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Solver
 * Method:    getRoundingModeSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_getRoundingModeSort(JNIEnv*,
                                                             jobject,
                                                             jlong);

/*
 * Class:     cvc5_Solver
 * Method:    getStringSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_getStringSort(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Solver
 * Method:    mkArraySort
 * Signature: (JJJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkArraySort(JNIEnv* env,
                                                     jobject,
                                                     jlong pointer,
                                                     jlong indexSortPointer,
                                                     jlong elementSortPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Sort* indexSort = (Sort*)indexSortPointer;
  Sort* elementSort = (Sort*)elementSortPointer;
  Sort* retPointer = new Sort(solver->mkArraySort(*indexSort, *elementSort));
  return ((jlong)retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Solver
 * Method:    mkBitVectorSort
 * Signature: (JI)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkBitVectorSort(JNIEnv* env,
                                                         jobject,
                                                         jlong pointer,
                                                         jint size)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Sort* sortPointer = new Sort(solver->mkBitVectorSort((uint32_t)size));
  return ((jlong)sortPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Solver
 * Method:    mkFloatingPointSort
 * Signature: (JII)J
 */
JNIEXPORT jlong JNICALL
Java_cvc5_Solver_mkFloatingPointSort(JNIEnv*, jobject, jlong, jint, jint);

/*
 * Class:     cvc5_Solver
 * Method:    mkDatatypeSort
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkDatatypeSort(
    JNIEnv* env, jobject, jlong pointer, jlong datatypeDeclPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  DatatypeDecl* decl = (DatatypeDecl*)datatypeDeclPointer;
  Sort* retPointer = new Sort(solver->mkDatatypeSort(*decl));
  return ((jlong)retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Solver
 * Method:    mkDatatypeSorts
 * Signature: (J[J)[J
 */
JNIEXPORT jlongArray JNICALL Java_cvc5_Solver_mkDatatypeSorts__J_3J(JNIEnv*,
                                                                    jobject,
                                                                    jlong,
                                                                    jlongArray);

/*
 * Class:     cvc5_Solver
 * Method:    mkDatatypeSorts
 * Signature: (J[J[J)[J
 */
JNIEXPORT jlongArray JNICALL Java_cvc5_Solver_mkDatatypeSorts__J_3J_3J(
    JNIEnv*, jobject, jlong, jlongArray, jlongArray);

/*
 * Class:     cvc5_Solver
 * Method:    mkFunctionSort
 * Signature: (JJJ)J
 */
JNIEXPORT jlong JNICALL
Java_cvc5_Solver_mkFunctionSort__JJJ(JNIEnv* env,
                                     jobject,
                                     jlong pointer,
                                     jlong domainPointer,
                                     jlong codomainPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Sort* domain = (Sort*)domainPointer;
  Sort* codomain = (Sort*)codomainPointer;
  Sort* sortPointer = new Sort(solver->mkFunctionSort(*domain, *codomain));
  return ((jlong)sortPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Solver
 * Method:    mkFunctionSort
 * Signature: (J[JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkFunctionSort__J_3JJ(
    JNIEnv*, jobject, jlong, jlongArray, jlong);

/*
 * Class:     cvc5_Solver
 * Method:    mkParamSort
 * Signature: (JLjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkParamSort(JNIEnv* env,
                                                     jobject,
                                                     jlong pointer,
                                                     jstring jSymbol)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  const char* s = env->GetStringUTFChars(jSymbol, nullptr);
  std::string cSymbol(s);
  Sort* retPointer = new Sort(solver->mkParamSort(cSymbol));
  env->ReleaseStringUTFChars(jSymbol, s);
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Solver
 * Method:    mkPredicateSort
 * Signature: (J[J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkPredicateSort(JNIEnv*,
                                                         jobject,
                                                         jlong,
                                                         jlongArray);

/*
 * Class:     cvc5_Solver
 * Method:    mkRecordSort
 * Signature: (J[Lcvc5/Pair;)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkRecordSort(JNIEnv*,
                                                      jobject,
                                                      jlong,
                                                      jobjectArray);

/*
 * Class:     cvc5_Solver
 * Method:    mkSetSort
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkSetSort(JNIEnv* env,
                                                   jobject,
                                                   jlong pointer,
                                                   jlong elemSortPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Sort* elemSort = (Sort*)elemSortPointer;
  Sort* retPointer = new Sort(solver->mkSetSort(*elemSort));
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Solver
 * Method:    mkBagSort
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkBagSort(JNIEnv* env,
                                                   jobject,
                                                   jlong pointer,
                                                   jlong elemSortPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Sort* elemSort = (Sort*)elemSortPointer;
  Sort* retPointer = new Sort(solver->mkBagSort(*elemSort));
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Solver
 * Method:    mkSequenceSort
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkSequenceSort(JNIEnv* env,
                                                        jobject,
                                                        jlong pointer,
                                                        jlong elemSortPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Sort* elemSort = (Sort*)elemSortPointer;
  Sort* sortPointer = new Sort(solver->mkSequenceSort(*elemSort));
  return ((jlong)sortPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
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
 * Method:    mkSortConstructorSort
 * Signature: (JLjava/lang/String;I)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkSortConstructorSort(
    JNIEnv* env, jobject, jlong pointer, jstring jSymbol, jint arity)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;

  Solver* solver = (Solver*)pointer;
  const char* s = env->GetStringUTFChars(jSymbol, nullptr);
  std::string cSymbol(s);
  Sort* retPointer = new Sort(solver->mkSortConstructorSort(cSymbol, (size_t)arity));
  env->ReleaseStringUTFChars(jSymbol, s);
  return (jlong)retPointer;

  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Solver
 * Method:    mkTupleSort
 * Signature: (J[J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkTupleSort(JNIEnv* env,
                                                     jobject,
                                                     jlong pointer,
                                                     jlongArray sortPointers)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  // get the size of sort pointers
  jsize size = env->GetArrayLength(sortPointers);
  // allocate buffer for the long array
  jlong* buffer = new jlong[size];
  // copy java array to the buffer
  env->GetLongArrayRegion(sortPointers, 0, size, buffer);
  // copy the terms into a vector
  std::vector<Sort> sorts;
  for (jsize i = 0; i < size; i++)
  {
    Sort* sort = (Sort*)buffer[i];
    sorts.push_back(*sort);
  }
  // free the buffer memory
  delete[] buffer;

  Sort* retPointer = new Sort(solver->mkTupleSort(sorts));
  return ((jlong)retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Solver
 * Method:    mkTerm
 * Signature: (JI)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkTerm__JI(JNIEnv*,
                                                    jobject,
                                                    jlong,
                                                    jint);

/*
 * Class:     cvc5_Solver
 * Method:    mkTerm
 * Signature: (JIJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkTerm__JIJ(
    JNIEnv* env, jobject, jlong pointer, jint kindValue, jlong childPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Kind kind = (Kind)kindValue;
  Term* child = (Term*)childPointer;
  Term* termPointer = new Term(solver->mkTerm(kind, *child));
  return ((jlong)termPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Solver
 * Method:    mkTerm
 * Signature: (JIJJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkTerm__JIJJ(JNIEnv* env,
                                                      jobject,
                                                      jlong pointer,
                                                      jint kindValue,
                                                      jlong child1Pointer,
                                                      jlong child2Pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Kind kind = (Kind)kindValue;
  Term* child1 = (Term*)child1Pointer;
  Term* child2 = (Term*)child2Pointer;
  Term* termPointer = new Term(solver->mkTerm(kind, *child1, *child2));
  return ((jlong)termPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Solver
 * Method:    mkTerm
 * Signature: (JIJJJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkTerm__JIJJJ(JNIEnv* env,
                                                       jobject,
                                                       jlong pointer,
                                                       jint kindValue,
                                                       jlong child1Pointer,
                                                       jlong child2Pointer,
                                                       jlong child3Pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Kind kind = (Kind)kindValue;
  Term* child1 = (Term*)child1Pointer;
  Term* child2 = (Term*)child2Pointer;
  Term* child3 = (Term*)child3Pointer;
  Term* retPointer = new Term(solver->mkTerm(kind, *child1, *child2, *child3));
  return ((jlong)retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Solver
 * Method:    mkTerm
 * Signature: (JI[J)J
 */
JNIEXPORT jlong JNICALL
Java_cvc5_Solver_mkTerm__JI_3J(JNIEnv*, jobject, jlong, jint, jlongArray);

/*
 * Class:     cvc5_Solver
 * Method:    mkTerm
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkTerm__JJ(JNIEnv*,
                                                    jobject,
                                                    jlong,
                                                    jlong);

/*
 * Class:     cvc5_Solver
 * Method:    mkTerm
 * Signature: (JJJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkTerm__JJJ(
    JNIEnv* env, jobject, jlong pointer, jlong opPointer, jlong childPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Op* op = (Op*)opPointer;
  Term* child = (Term*)childPointer;
  Term* retPointer = new Term(solver->mkTerm(*op, *child));
  return ((jlong)retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Solver
 * Method:    mkTerm
 * Signature: (JJJJ)J
 */
JNIEXPORT jlong JNICALL
Java_cvc5_Solver_mkTerm__JJJJ(JNIEnv*, jobject, jlong, jlong, jlong, jlong);

/*
 * Class:     cvc5_Solver
 * Method:    mkTerm
 * Signature: (JJJJJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkTerm__JJJJJ(
    JNIEnv*, jobject, jlong, jlong, jlong, jlong, jlong);

/*
 * Class:     cvc5_Solver
 * Method:    mkTerm
 * Signature: (JJ[J)J
 */
JNIEXPORT jlong JNICALL
Java_cvc5_Solver_mkTerm__JJ_3J(JNIEnv* env,
                               jobject,
                               jlong pointer,
                               jlong opPointer,
                               jlongArray childrenPointers)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Op* op = (Op*)opPointer;

  // get the size of children pointers
  jsize size = env->GetArrayLength(childrenPointers);
  // allocate buffer for the long array
  jlong* buffer = new jlong[size];
  // copy java array to the buffer
  env->GetLongArrayRegion(childrenPointers, 0, size, buffer);
  // copy the terms into a vector
  std::vector<Term> children;
  for (jsize i = 0; i < size; i++)
  {
    Term* term = (Term*)buffer[i];
    children.push_back(*term);
  }
  // free the buffer memory
  delete[] buffer;

  Term* retPointer = new Term(solver->mkTerm(*op, children));
  return ((jlong)retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Solver
 * Method:    mkTuple
 * Signature: (J[J[J)J
 */
JNIEXPORT jlong JNICALL
Java_cvc5_Solver_mkTuple(JNIEnv*, jobject, jlong, jlongArray, jlongArray);

/*
 * Class:     cvc5_Solver
 * Method:    mkOp
 * Signature: (JI)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkOp__JI(JNIEnv*,
                                                  jobject,
                                                  jlong,
                                                  jint);

/*
 * Class:     cvc5_Solver
 * Method:    mkOp
 * Signature: (JILjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkOp__JILjava_lang_String_2(
    JNIEnv*, jobject, jlong, jint, jstring);

/*
 * Class:     cvc5_Solver
 * Method:    mkOp
 * Signature: (JII)J
 */
JNIEXPORT jlong JNICALL
Java_cvc5_Solver_mkOp__JII(JNIEnv*, jobject, jlong, jint, jint);

/*
 * Class:     cvc5_Solver
 * Method:    mkOp
 * Signature: (JIII)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkOp__JIII(
    JNIEnv* env, jobject, jlong pointer, jint kindValue, jint arg1, jint arg2)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Kind kind = (Kind)kindValue;
  Op* retPointer = new Op(solver->mkOp(kind, (uint32_t)arg1, (uint32_t)arg2));
  return ((jlong)retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Solver
 * Method:    mkOp
 * Signature: (JI[I)J
 */
JNIEXPORT jlong JNICALL
Java_cvc5_Solver_mkOp__JI_3I(JNIEnv*, jobject, jlong, jint, jintArray);

/*
 * Class:     cvc5_Solver
 * Method:    mkTrue
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkTrue(JNIEnv* env,
                                                jobject,
                                                jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Term* termPointer = new Term(solver->mkTrue());
  return ((jlong)termPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Solver
 * Method:    mkFalse
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkFalse(JNIEnv* env,
                                                 jobject,
                                                 jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Term* termPointer = new Term(solver->mkFalse());
  return ((jlong)termPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Solver
 * Method:    mkBoolean
 * Signature: (JZ)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkBoolean(JNIEnv*,
                                                   jobject,
                                                   jlong,
                                                   jboolean);

/*
 * Class:     cvc5_Solver
 * Method:    mkPi
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkPi(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Solver
 * Method:    mkInteger
 * Signature: (JLjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkInteger__JLjava_lang_String_2(
    JNIEnv* env, jobject, jlong pointer, jstring jS)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  const char* s = env->GetStringUTFChars(jS, nullptr);
  std::string cS(s);
  Term* retPointer = new Term(solver->mkInteger(cS));
  env->ReleaseStringUTFChars(jS, s);
  return ((jlong)retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Solver
 * Method:    mkInteger
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkInteger__JJ(JNIEnv* env,
                                                       jobject,
                                                       jlong pointer,
                                                       jlong val)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Term* termPointer = new Term(solver->mkInteger((int64_t)val));
  return ((jlong)termPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Solver
 * Method:    mkReal
 * Signature: (JLjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkReal__JLjava_lang_String_2(JNIEnv*,
                                                                      jobject,
                                                                      jlong,
                                                                      jstring);

/*
 * Class:     cvc5_Solver
 * Method:    mkRealValue
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkRealValue(JNIEnv* env,
                                                     jobject,
                                                     jlong pointer,
                                                     jlong val)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Term* retPointer = new Term(solver->mkReal((int64_t)val));
  return ((jlong)retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Solver
 * Method:    mkReal
 * Signature: (JJJ)J
 */
JNIEXPORT jlong JNICALL
Java_cvc5_Solver_mkReal__JJJ(JNIEnv*, jobject, jlong, jlong, jlong);

/*
 * Class:     cvc5_Solver
 * Method:    mkRegexpEmpty
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkRegexpEmpty(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Solver
 * Method:    mkRegexpSigma
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkRegexpSigma(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Solver
 * Method:    mkEmptySet
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkEmptySet(JNIEnv*,
                                                    jobject,
                                                    jlong,
                                                    jlong);

/*
 * Class:     cvc5_Solver
 * Method:    mkEmptyBag
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkEmptyBag(JNIEnv*,
                                                    jobject,
                                                    jlong,
                                                    jlong);

/*
 * Class:     cvc5_Solver
 * Method:    mkSepNil
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkSepNil(JNIEnv*,
                                                  jobject,
                                                  jlong,
                                                  jlong);

/*
 * Class:     cvc5_Solver
 * Method:    mkString
 * Signature: (JLjava/lang/String;Z)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkString__JLjava_lang_String_2Z(
    JNIEnv* env, jobject, jlong pointer, jstring jS, jboolean useEscSequences)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  const char* s = env->GetStringUTFChars(jS, nullptr);
  std::string cS(s);
  Term* retPointer = new Term(solver->mkString(cS, (bool)useEscSequences));
  env->ReleaseStringUTFChars(jS, s);
  return ((jlong)retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Solver
 * Method:    mkString
 * Signature: (JC)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkString__JC(JNIEnv*,
                                                      jobject,
                                                      jlong,
                                                      jchar);

/*
 * Class:     cvc5_Solver
 * Method:    mkString
 * Signature: (J[I)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkString__J_3I(JNIEnv*,
                                                        jobject,
                                                        jlong,
                                                        jintArray);

/*
 * Class:     cvc5_Solver
 * Method:    mkChar
 * Signature: (JLjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkChar(JNIEnv*,
                                                jobject,
                                                jlong,
                                                jstring);

/*
 * Class:     cvc5_Solver
 * Method:    mkEmptySequence
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkEmptySequence(JNIEnv* env,
                                                         jobject,
                                                         jlong pointer,
                                                         jlong sortPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Sort* sort = (Sort*)sortPointer;
  Term* retPointer = new Term(solver->mkEmptySequence(*sort));
  return ((jlong)retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Solver
 * Method:    mkUniverseSet
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkUniverseSet(JNIEnv*,
                                                       jobject,
                                                       jlong,
                                                       jlong);

/*
 * Class:     cvc5_Solver
 * Method:    mkBitVector
 * Signature: (JIJ)J
 */
JNIEXPORT jlong JNICALL
Java_cvc5_Solver_mkBitVector__JIJ(JNIEnv*, jobject, jlong, jint, jlong);

/*
 * Class:     cvc5_Solver
 * Method:    mkBitVector
 * Signature: (JLjava/lang/String;I)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkBitVector__JLjava_lang_String_2I(
    JNIEnv*, jobject, jlong, jstring, jint);

/*
 * Class:     cvc5_Solver
 * Method:    mkBitVector
 * Signature: (JILjava/lang/String;I)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkBitVector__JILjava_lang_String_2I(
    JNIEnv*, jobject, jlong, jint, jstring, jint);

/*
 * Class:     cvc5_Solver
 * Method:    mkConstArray
 * Signature: (JJJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkConstArray(
    JNIEnv* env, jobject, jlong pointer, jlong sortPointer, jlong valPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Sort* sort = (Sort*)sortPointer;
  Term* val = (Term*)valPointer;
  Term* retPointer = new Term(solver->mkConstArray(*sort, *val));
  return ((jlong)retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Solver
 * Method:    mkPosInf
 * Signature: (JII)J
 */
JNIEXPORT jlong JNICALL
Java_cvc5_Solver_mkPosInf(JNIEnv*, jobject, jlong, jint, jint);

/*
 * Class:     cvc5_Solver
 * Method:    mkNegInf
 * Signature: (JII)J
 */
JNIEXPORT jlong JNICALL
Java_cvc5_Solver_mkNegInf(JNIEnv*, jobject, jlong, jint, jint);

/*
 * Class:     cvc5_Solver
 * Method:    mkNaN
 * Signature: (JII)J
 */
JNIEXPORT jlong JNICALL
Java_cvc5_Solver_mkNaN(JNIEnv*, jobject, jlong, jint, jint);

/*
 * Class:     cvc5_Solver
 * Method:    mkPosZero
 * Signature: (JII)J
 */
JNIEXPORT jlong JNICALL
Java_cvc5_Solver_mkPosZero(JNIEnv*, jobject, jlong, jint, jint);

/*
 * Class:     cvc5_Solver
 * Method:    mkNegZero
 * Signature: (JII)J
 */
JNIEXPORT jlong JNICALL
Java_cvc5_Solver_mkNegZero(JNIEnv*, jobject, jlong, jint, jint);

/*
 * Class:     cvc5_Solver
 * Method:    mkRoundingMode
 * Signature: (JI)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkRoundingMode(JNIEnv*,
                                                        jobject,
                                                        jlong,
                                                        jint);

/*
 * Class:     cvc5_Solver
 * Method:    mkUninterpretedConst
 * Signature: (JJI)J
 */
JNIEXPORT jlong JNICALL
Java_cvc5_Solver_mkUninterpretedConst(JNIEnv*, jobject, jlong, jlong, jint);

/*
 * Class:     cvc5_Solver
 * Method:    mkAbstractValue
 * Signature: (JLjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkAbstractValue__JLjava_lang_String_2(
    JNIEnv*, jobject, jlong, jstring);

/*
 * Class:     cvc5_Solver
 * Method:    mkAbstractValue
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkAbstractValue__JJ(JNIEnv*,
                                                             jobject,
                                                             jlong,
                                                             jlong);

/*
 * Class:     cvc5_Solver
 * Method:    mkFloatingPoint
 * Signature: (JIIJ)J
 */
JNIEXPORT jlong JNICALL
Java_cvc5_Solver_mkFloatingPoint(JNIEnv*, jobject, jlong, jint, jint, jlong);

/*
 * Class:     cvc5_Solver
 * Method:    mkConst
 * Signature: (JJLjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkConst__JJLjava_lang_String_2(
    JNIEnv* env, jobject, jlong pointer, jlong sortPointer, jstring jSymbol)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Sort* sort = (Sort*)sortPointer;
  const char* s = env->GetStringUTFChars(jSymbol, nullptr);
  std::string cSymbol(s);
  Term* retPointer = new Term(solver->mkConst(*sort, cSymbol));
  env->ReleaseStringUTFChars(jSymbol, s);
  return ((jlong)retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Solver
 * Method:    mkConst
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkConst__JJ(JNIEnv*,
                                                     jobject,
                                                     jlong,
                                                     jlong);

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
 * Method:    mkDatatypeConstructorDecl
 * Signature: (JLjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkDatatypeConstructorDecl(
    JNIEnv* env, jobject, jlong pointer, jstring jName)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  const char* s = env->GetStringUTFChars(jName, nullptr);
  std::string cName(s);

  DatatypeConstructorDecl* retPointer =
      new DatatypeConstructorDecl(solver->mkDatatypeConstructorDecl(cName));
  env->ReleaseStringUTFChars(jName, s);
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Solver
 * Method:    mkDatatypeDecl
 * Signature: (JLjava/lang/String;Z)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkDatatypeDecl__JLjava_lang_String_2Z(
    JNIEnv* env, jobject, jlong pointer, jstring jName, jboolean isCoDatatype)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  const char* s = env->GetStringUTFChars(jName, nullptr);
  std::string cName(s);
  DatatypeDecl* retPointer =
      new DatatypeDecl(solver->mkDatatypeDecl(cName, (bool)isCoDatatype));
  env->ReleaseStringUTFChars(jName, s);
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Solver
 * Method:    mkDatatypeDecl
 * Signature: (JLjava/lang/String;JZ)J
 */
JNIEXPORT jlong JNICALL
Java_cvc5_Solver_mkDatatypeDecl__JLjava_lang_String_2JZ(JNIEnv* env,
                                                        jobject,
                                                        jlong pointer,
                                                        jstring jName,
                                                        jlong paramPointer,
                                                        jboolean isCoDatatype)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  const char* s = env->GetStringUTFChars(jName, nullptr);
  std::string cName(s);
  Sort* param = (Sort*)paramPointer;
  DatatypeDecl* retPointer = new DatatypeDecl(
      solver->mkDatatypeDecl(cName, *param, (bool)isCoDatatype));
  env->ReleaseStringUTFChars(jName, s);
  return (jlong)retPointer;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Solver
 * Method:    mkDatatypeDecl
 * Signature: (JLjava/lang/String;[JZ)J
 */
JNIEXPORT jlong JNICALL
Java_cvc5_Solver_mkDatatypeDecl__JLjava_lang_String_2_3JZ(
    JNIEnv*, jobject, jlong, jstring, jlongArray, jboolean);

/*
 * Class:     cvc5_Solver
 * Method:    simplify
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_simplify(JNIEnv*,
                                                  jobject,
                                                  jlong,
                                                  jlong);

/*
 * Class:     cvc5_Solver
 * Method:    assertFormula
 * Signature: (JJ)V
 */
JNIEXPORT void JNICALL Java_cvc5_Solver_assertFormula(JNIEnv*,
                                                      jobject,
                                                      jlong,
                                                      jlong);

/*
 * Class:     cvc5_Solver
 * Method:    checkSat
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_checkSat(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Solver
 * Method:    checkSatAssuming
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_checkSatAssuming__JJ(JNIEnv*,
                                                              jobject,
                                                              jlong,
                                                              jlong);

/*
 * Class:     cvc5_Solver
 * Method:    checkSatAssuming
 * Signature: (J[J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_checkSatAssuming__J_3J(JNIEnv*,
                                                                jobject,
                                                                jlong,
                                                                jlongArray);

/*
 * Class:     cvc5_Solver
 * Method:    checkEntailed
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_checkEntailed__JJ(JNIEnv*,
                                                           jobject,
                                                           jlong,
                                                           jlong);

/*
 * Class:     cvc5_Solver
 * Method:    checkEntailed
 * Signature: (J[J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_checkEntailed__J_3J(JNIEnv*,
                                                             jobject,
                                                             jlong,
                                                             jlongArray);

/*
 * Class:     cvc5_Solver
 * Method:    declareDatatype
 * Signature: (JLjava/lang/String;[J)J
 */
JNIEXPORT jlong JNICALL
Java_cvc5_Solver_declareDatatype(JNIEnv*, jobject, jlong, jstring, jlongArray);

/*
 * Class:     cvc5_Solver
 * Method:    declareFun
 * Signature: (JLjava/lang/String;[JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_declareFun(
    JNIEnv*, jobject, jlong, jstring, jlongArray, jlong);

/*
 * Class:     cvc5_Solver
 * Method:    declareSort
 * Signature: (JLjava/lang/String;I)J
 */
JNIEXPORT jlong JNICALL
Java_cvc5_Solver_declareSort(JNIEnv*, jobject, jlong, jstring, jint);

/*
 * Class:     cvc5_Solver
 * Method:    defineFun
 * Signature: (JLjava/lang/String;[JJJZ)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_defineFun__JLjava_lang_String_2_3JJJZ(
    JNIEnv*, jobject, jlong, jstring, jlongArray, jlong, jlong, jboolean);

/*
 * Class:     cvc5_Solver
 * Method:    defineFun
 * Signature: (J[JJZ)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_defineFun__J_3JJZ(
    JNIEnv*, jobject, jlong, jlongArray, jlong, jboolean);

/*
 * Class:     cvc5_Solver
 * Method:    defineFunRec
 * Signature: (JLjava/lang/String;[JJJZ)J
 */
JNIEXPORT jlong JNICALL
Java_cvc5_Solver_defineFunRec__JLjava_lang_String_2_3JJJZ(
    JNIEnv*, jobject, jlong, jstring, jlongArray, jlong, jlong, jboolean);

/*
 * Class:     cvc5_Solver
 * Method:    defineFunRec
 * Signature: (JJ[JJZ)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_defineFunRec__JJ_3JJZ(
    JNIEnv*, jobject, jlong, jlong, jlongArray, jlong, jboolean);

/*
 * Class:     cvc5_Solver
 * Method:    defineFunsRec
 * Signature: (J[J[[J[JZ)V
 */
JNIEXPORT void JNICALL Java_cvc5_Solver_defineFunsRec(
    JNIEnv*, jobject, jlong, jlongArray, jobjectArray, jlongArray, jboolean);

/*
 * Class:     cvc5_Solver
 * Method:    getAssertions
 * Signature: (J)[J
 */
JNIEXPORT jlongArray JNICALL Java_cvc5_Solver_getAssertions(JNIEnv*,
                                                            jobject,
                                                            jlong);

/*
 * Class:     cvc5_Solver
 * Method:    getInfo
 * Signature: (JLjava/lang/String;)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_cvc5_Solver_getInfo(JNIEnv*,
                                                   jobject,
                                                   jlong,
                                                   jstring);

/*
 * Class:     cvc5_Solver
 * Method:    getOption
 * Signature: (JLjava/lang/String;)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_cvc5_Solver_getOption(JNIEnv*,
                                                     jobject,
                                                     jlong,
                                                     jstring);

/*
 * Class:     cvc5_Solver
 * Method:    getUnsatAssumptions
 * Signature: (J)[J
 */
JNIEXPORT jlongArray JNICALL Java_cvc5_Solver_getUnsatAssumptions(JNIEnv*,
                                                                  jobject,
                                                                  jlong);

/*
 * Class:     cvc5_Solver
 * Method:    getUnsatCore
 * Signature: (J)[J
 */
JNIEXPORT jlongArray JNICALL Java_cvc5_Solver_getUnsatCore(JNIEnv*,
                                                           jobject,
                                                           jlong);

/*
 * Class:     cvc5_Solver
 * Method:    getValue
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_getValue__JJ(JNIEnv*,
                                                      jobject,
                                                      jlong,
                                                      jlong);

/*
 * Class:     cvc5_Solver
 * Method:    getValue
 * Signature: (J[J)[J
 */
JNIEXPORT jlongArray JNICALL Java_cvc5_Solver_getValue__J_3J(JNIEnv*,
                                                             jobject,
                                                             jlong,
                                                             jlongArray);

/*
 * Class:     cvc5_Solver
 * Method:    getQuantifierElimination
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_getQuantifierElimination(JNIEnv*,
                                                                  jobject,
                                                                  jlong,
                                                                  jlong);

/*
 * Class:     cvc5_Solver
 * Method:    getQuantifierEliminationDisjunct
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_getQuantifierEliminationDisjunct(
    JNIEnv*, jobject, jlong, jlong);

/*
 * Class:     cvc5_Solver
 * Method:    declareSeparationHeap
 * Signature: (JJJ)V
 */
JNIEXPORT void JNICALL
Java_cvc5_Solver_declareSeparationHeap(JNIEnv*, jobject, jlong, jlong, jlong);

/*
 * Class:     cvc5_Solver
 * Method:    getSeparationHeap
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_getSeparationHeap(JNIEnv*,
                                                           jobject,
                                                           jlong);

/*
 * Class:     cvc5_Solver
 * Method:    getSeparationNilTerm
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_getSeparationNilTerm(JNIEnv*,
                                                              jobject,
                                                              jlong);

/*
 * Class:     cvc5_Solver
 * Method:    pop
 * Signature: (JI)V
 */
JNIEXPORT void JNICALL Java_cvc5_Solver_pop(JNIEnv*, jobject, jlong, jint);

/*
 * Class:     cvc5_Solver
 * Method:    getInterpolant
 * Signature: (JJJ)Z
 */
JNIEXPORT jboolean JNICALL
Java_cvc5_Solver_getInterpolant__JJJ(JNIEnv*, jobject, jlong, jlong, jlong);

/*
 * Class:     cvc5_Solver
 * Method:    getInterpolant
 * Signature: (JJJJ)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Solver_getInterpolant__JJJJ(
    JNIEnv*, jobject, jlong, jlong, jlong, jlong);

/*
 * Class:     cvc5_Solver
 * Method:    getAbduct
 * Signature: (JJJ)Z
 */
JNIEXPORT jboolean JNICALL
Java_cvc5_Solver_getAbduct__JJJ(JNIEnv*, jobject, jlong, jlong, jlong);

/*
 * Class:     cvc5_Solver
 * Method:    getAbduct
 * Signature: (JJJJ)Z
 */
JNIEXPORT jboolean JNICALL
Java_cvc5_Solver_getAbduct__JJJJ(JNIEnv*, jobject, jlong, jlong, jlong, jlong);

/*
 * Class:     cvc5_Solver
 * Method:    blockModel
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_cvc5_Solver_blockModel(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Solver
 * Method:    blockModelValues
 * Signature: (J[J)V
 */
JNIEXPORT void JNICALL Java_cvc5_Solver_blockModelValues(JNIEnv*,
                                                         jobject,
                                                         jlong,
                                                         jlongArray);

/*
 * Class:     cvc5_Solver
 * Method:    push
 * Signature: (JI)V
 */
JNIEXPORT void JNICALL Java_cvc5_Solver_push(JNIEnv*, jobject, jlong, jint);

/*
 * Class:     cvc5_Solver
 * Method:    resetAssertions
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_cvc5_Solver_resetAssertions(JNIEnv*,
                                                        jobject,
                                                        jlong);

/*
 * Class:     cvc5_Solver
 * Method:    setInfo
 * Signature: (JLjava/lang/String;Ljava/lang/String;)V
 */
JNIEXPORT void JNICALL
Java_cvc5_Solver_setInfo(JNIEnv*, jobject, jlong, jstring, jstring);

/*
 * Class:     cvc5_Solver
 * Method:    setLogic
 * Signature: (JLjava/lang/String;)V
 */
JNIEXPORT void JNICALL Java_cvc5_Solver_setLogic(JNIEnv* env,
                                                 jobject,
                                                 jlong pointer,
                                                 jstring jLogic)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;

  Solver* solver = (Solver*)pointer;
  const char* cLogic = env->GetStringUTFChars(jLogic, nullptr);
  solver->setLogic(std::string(cLogic));

  CVC5_JAVA_API_TRY_CATCH_END(env);
}

/*
 * Class:     cvc5_Solver
 * Method:    setOption
 * Signature: (JLjava/lang/String;Ljava/lang/String;)V
 */
JNIEXPORT void JNICALL
Java_cvc5_Solver_setOption(JNIEnv*, jobject, jlong, jstring, jstring);

/*
 * Class:     cvc5_Solver
 * Method:    ensureTermSort
 * Signature: (JJJ)J
 */
JNIEXPORT jlong JNICALL
Java_cvc5_Solver_ensureTermSort(JNIEnv*, jobject, jlong, jlong, jlong);

/*
 * Class:     cvc5_Solver
 * Method:    mkSygusVar
 * Signature: (JJLjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL
Java_cvc5_Solver_mkSygusVar(JNIEnv*, jobject, jlong, jlong, jstring);

/*
 * Class:     cvc5_Solver
 * Method:    mkSygusGrammar
 * Signature: (J[J[J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_mkSygusGrammar(
    JNIEnv*, jobject, jlong, jlongArray, jlongArray);

/*
 * Class:     cvc5_Solver
 * Method:    synthFun
 * Signature: (JLjava/lang/String;[JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_synthFun__JLjava_lang_String_2_3JJ(
    JNIEnv*, jobject, jlong, jstring, jlongArray, jlong);

/*
 * Class:     cvc5_Solver
 * Method:    synthFun
 * Signature: (JLjava/lang/String;[JJJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_synthFun__JLjava_lang_String_2_3JJJ(
    JNIEnv*, jobject, jlong, jstring, jlongArray, jlong, jlong);

/*
 * Class:     cvc5_Solver
 * Method:    synthInv
 * Signature: (JLjava/lang/String;[J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_synthInv__JLjava_lang_String_2_3J(
    JNIEnv*, jobject, jlong, jstring, jlongArray);

/*
 * Class:     cvc5_Solver
 * Method:    synthInv
 * Signature: (JLjava/lang/String;[JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_synthInv__JLjava_lang_String_2_3JJ(
    JNIEnv*, jobject, jlong, jstring, jlongArray, jlong);

/*
 * Class:     cvc5_Solver
 * Method:    addSygusConstraint
 * Signature: (JJ)V
 */
JNIEXPORT void JNICALL Java_cvc5_Solver_addSygusConstraint__JJ(JNIEnv*,
                                                               jobject,
                                                               jlong,
                                                               jlong);

/*
 * Class:     cvc5_Solver
 * Method:    addSygusConstraint
 * Signature: (JJJJJ)V
 */
JNIEXPORT void JNICALL Java_cvc5_Solver_addSygusConstraint__JJJJJ(
    JNIEnv*, jobject, jlong, jlong, jlong, jlong, jlong);

/*
 * Class:     cvc5_Solver
 * Method:    checkSynth
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_checkSynth(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Solver
 * Method:    getSynthSolution
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Solver_getSynthSolution(JNIEnv*,
                                                          jobject,
                                                          jlong,
                                                          jlong);

/*
 * Class:     cvc5_Solver
 * Method:    getSynthSolutions
 * Signature: (J[J)[J
 */
JNIEXPORT jlongArray JNICALL Java_cvc5_Solver_getSynthSolutions(JNIEnv*,
                                                                jobject,
                                                                jlong,
                                                                jlongArray);

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