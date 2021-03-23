#include "cvc_Solver.h"

#include "cvc4/api/cvc4cpp.h"
#include "cvcJavaApi.h"

using namespace CVC4::api;

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
  std::cout << "Deleting Solver pointer: " << pointer << std::endl;
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

/*
 * Class:     cvc_Solver
 * Method:    getNullSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_getNullSort(JNIEnv* env,
                                                    jobject,
                                                    jlong solverPointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)solverPointer;
  Sort* sortPointer = new Sort(solver->getNullSort());
  return ((jlong)sortPointer);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    getBooleanSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_getBooleanSort(JNIEnv* env,
                                                       jobject,
                                                       jlong solverPointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)solverPointer;
  Sort* sortPointer = new Sort(solver->getBooleanSort());
  return ((jlong)sortPointer);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    getIntegerSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_getIntegerSort(JNIEnv* env,
                                                       jobject,
                                                       jlong solverPointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)solverPointer;
  Sort* sortPointer = new Sort(solver->getIntegerSort());
  return ((jlong)sortPointer);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    getRealSort
 * Signature: ()Lcvc4/Sort;
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_getRealSort(JNIEnv* env,
                                                    jobject,
                                                    jlong solverPointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)solverPointer;
  Sort* sortPointer = new Sort(solver->getRealSort());
  return ((jlong)sortPointer);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    getRegExpSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_getRegExpSort(JNIEnv* env,
                                                      jobject,
                                                      jlong solverPointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)solverPointer;
  Sort* sortPointer = new Sort(solver->getRegExpSort());
  return ((jlong)sortPointer);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    getRoundingModeSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_getRoundingModeSort(JNIEnv* env,
                                                            jobject,
                                                            jlong solverPointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)solverPointer;
  Sort* sortPointer = new Sort(solver->getRoundingModeSort());
  return ((jlong)sortPointer);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    getStringSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_getStringSort(JNIEnv* env,
                                                      jobject,
                                                      jlong solverPointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)solverPointer;
  Sort* sortPointer = new Sort(solver->getStringSort());
  return ((jlong)sortPointer);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/* Create sorts ------------------------------------------------------- */
// region Create sorts

/*
 * Class:     cvc_Solver
 * Method:    mkSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkSort(JNIEnv* env,
                                               jobject,
                                               jlong pointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Sort* sort = new Sort();
  return (jlong)sort;
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkArraySort
 * Signature: (JJJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkArraySort(JNIEnv* env,
                                                    jobject,
                                                    jlong solverPointer,
                                                    jlong indexSortPointer,
                                                    jlong elementSortPointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)solverPointer;
  Sort* indexSort = (Sort*)indexSortPointer;
  Sort* elementSort = (Sort*)elementSortPointer;
  Sort* sortPointer = new Sort(solver->mkArraySort(*indexSort, *elementSort));
  return ((jlong)sortPointer);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkBitVectorSort
 * Signature: (JI)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkBitVectorSort(JNIEnv* env,
                                                        jobject,
                                                        jlong solverPointer,
                                                        jint size)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)solverPointer;
  Sort* sortPointer = new Sort(solver->mkBitVectorSort((uint32_t)size));
  return ((jlong)sortPointer);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkFloatingPointSort
 * Signature: (JII)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkFloatingPointSort(
    JNIEnv* env, jobject, jlong solverPointer, jint exp, jint sig)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;

  Solver* solver = (Solver*)solverPointer;
  Sort* sortPointer =
      new Sort(solver->mkFloatingPointSort((uint32_t)exp, (uint32_t)sig));
  return ((jlong)sortPointer);

  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkDatatypeSort
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkDatatypeSort(
    JNIEnv* env, jobject, jlong solverPointer, jlong datatypeDeclPointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)solverPointer;
  DatatypeDecl* datatypeDecl = (DatatypeDecl*)datatypeDeclPointer;
  Sort* sort = new Sort(solver->mkDatatypeSort(*datatypeDecl));
  return ((jlong)sort);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkDatatypeSorts
 * Signature: (J[J)[J
 */
JNIEXPORT jlongArray JNICALL Java_cvc_Solver_mkDatatypeSorts__J_3J(
    JNIEnv* env, jobject, jlong pointer, jlongArray declPointers)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  jsize size = env->GetArrayLength(declPointers);
  jlong* elements = env->GetLongArrayElements(declPointers, nullptr);
  if (elements == 0)
  {
    throw CVC4ApiException("Null pointer elements in mkDatatypeSorts");
  }
  std::vector<DatatypeDecl> decls;
  for (jsize i = 0; i < size; i++)
  {
    DatatypeDecl* decl = (DatatypeDecl*)elements[i];
    decls.push_back(*decl);
  }
  env->ReleaseLongArrayElements(declPointers, elements, 0);

  std::vector<Sort> sorts = solver->mkDatatypeSorts(decls);
  std::vector<long> sortPointers(sorts.size());
  for (size_t i = 0; i < sorts.size(); i++)
  {
    sortPointers[i] = (long)new Sort(sorts[i]);
  }

  jlongArray ret = env->NewLongArray(sorts.size());
  env->SetLongArrayRegion(ret, 0, sorts.size(), sortPointers.data());

  return ret;
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     cvc_Solver
 * Method:    mkDatatypeSorts
 * Signature: (J[J[J)[J
 */
JNIEXPORT jlongArray JNICALL
Java_cvc_Solver_mkDatatypeSorts__J_3J_3J(JNIEnv* env,
                                         jobject,
                                         jlong pointer,
                                         jlongArray declPointers,
                                         jlongArray unresolvedPointers)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;

  Solver* solver = (Solver*)pointer;
  jsize declsSize = env->GetArrayLength(declPointers);
  jsize unresolvedSize = env->GetArrayLength(unresolvedPointers);
  jlong* declElements = env->GetLongArrayElements(declPointers, nullptr);
  if (declElements == 0)
  {
    throw CVC4ApiException("Null pointer declElements in mkDatatypeSorts");
  }
  jlong* unresolvedElements =
      env->GetLongArrayElements(unresolvedPointers, nullptr);
  if (unresolvedElements == 0)
  {
    throw CVC4ApiException(
        "Null pointer unresolvedElements in mkDatatypeSorts");
  }

  std::vector<DatatypeDecl> decls;
  for (jsize i = 0; i < declsSize; i++)
  {
    DatatypeDecl* decl = (DatatypeDecl*)declElements[i];
    decls.push_back(*decl);
  }
  env->ReleaseLongArrayElements(declPointers, declElements, 0);

  std::set<Sort> unresolved;
  for (jsize i = 0; i < unresolvedSize; i++)
  {
    Sort* sort = (Sort*)unresolvedElements[i];
    unresolved.insert(*sort);
  }

  env->ReleaseLongArrayElements(unresolvedPointers, unresolvedElements, 0);
  std::vector<Sort> sorts = solver->mkDatatypeSorts(decls, unresolved);
  std::vector<long> sortPointers(sorts.size());
  for (size_t i = 0; i < sorts.size(); i++)
  {
    sortPointers[i] = (long)new Sort(sorts[i]);
  }

  jlongArray ret = env->NewLongArray(sorts.size());
  env->SetLongArrayRegion(ret, 0, sorts.size(), sortPointers.data());

  return ret;

  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     cvc_Solver
 * Method:    mkUninterpretedSort
 * Signature: (JLjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkUninterpretedSort(JNIEnv* env,
                                                            jobject,
                                                            jlong pointer,
                                                            jstring jSymbol)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;

  Solver* solver = (Solver*)pointer;
  const char* cSymbol = env->GetStringUTFChars(jSymbol, nullptr);
  Sort* sort = new Sort(solver->mkUninterpretedSort(std::string(cSymbol)));
  return (jlong)sort;

  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkFunctionSort
 * Signature: (JJJ)J
 */
JNIEXPORT jlong JNICALL
Java_cvc_Solver_mkFunctionSort__JJJ(JNIEnv* env,
                                    jobject,
                                    jlong pointer,
                                    jlong domainPointer,
                                    jlong codomainPointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Sort* domain = (Sort*)domainPointer;
  Sort* codomain = (Sort*)codomainPointer;
  Sort* sort = new Sort(solver->mkFunctionSort(*domain, *codomain));
  return (jlong)sort;
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkFunctionSort
 * Signature: (J[JJ)J
 */
JNIEXPORT jlong JNICALL
Java_cvc_Solver_mkFunctionSort__J_3JJ(JNIEnv* env,
                                      jobject,
                                      jlong pointer,
                                      jlongArray sortPointers,
                                      jlong codomainPointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Sort* codomain = (Sort*)codomainPointer;
  jsize sortsSize = env->GetArrayLength(sortPointers);
  jlong* sortsElements = env->GetLongArrayElements(sortPointers, nullptr);
  if (sortsElements == 0)
  {
    throw CVC4ApiException("Null pointer sortsElements in mkFunctionSort");
  }

  std::vector<Sort> sorts;
  for (jsize i = 0; i < sortsSize; i++)
  {
    Sort* sort = (Sort*)sortsElements[i];
    sorts.push_back(*sort);
  }
  env->ReleaseLongArrayElements(sortPointers, sortsElements, 0);

  Sort* sort = new Sort(solver->mkFunctionSort(sorts, *codomain));
  return (jlong)sort;
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkParamSort
 * Signature: (JLjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkParamSort(JNIEnv* env,
                                                    jobject,
                                                    jlong pointer,
                                                    jstring jSymbol)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  const char* cSymbol = env->GetStringUTFChars(jSymbol, nullptr);
  Sort* sort = new Sort(solver->mkParamSort(cSymbol));
  return (jlong)sort;

  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkPredicateSort
 * Signature: (J[J)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkPredicateSort(JNIEnv* env,
                                                        jobject,
                                                        jlong pointer,
                                                        jlongArray sortPointers)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  jsize sortsSize = env->GetArrayLength(sortPointers);
  jlong* sortsElements = env->GetLongArrayElements(sortPointers, nullptr);
  if (sortsElements == 0)
  {
    throw CVC4ApiException("Null pointer sortsElements in mkPredicateSort");
  }

  std::vector<Sort> sorts;
  for (jsize i = 0; i < sortsSize; i++)
  {
    Sort* sort = (Sort*)sortsElements[i];
    sorts.push_back(*sort);
  }
  env->ReleaseLongArrayElements(sortPointers, sortsElements, 0);

  Sort* sort = new Sort(solver->mkPredicateSort(sorts));
  return (jlong)sort;
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkRecordSort
 * Signature: (J[Lcvc/Pair;)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkRecordSort(JNIEnv* env,
                                                     jobject,
                                                     jlong pointer,
                                                     jobjectArray jFields)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  jsize size = env->GetArrayLength(jFields);
  // Lcvc/Pair; is signature of cvc.Pair<String, Long>
  jclass pairClass = env->FindClass("Lcvc/Pair;");
  jclass longClass = env->FindClass("Ljava/lang/Long;");
  // Ljava/lang/Object; is the signature of cvc.Pair.first field
  jfieldID firstFieldId =
      env->GetFieldID(pairClass, "first", "Ljava/lang/Object;");
  // Ljava/lang/Object; is the signature of cvc.Pair.second field
  jfieldID secondFieldId =
      env->GetFieldID(pairClass, "second", "Ljava/lang/Object;");
  // we need to call method longValue to get long Long object
  jmethodID methodId = env->GetMethodID(longClass, "longValue", "()J");

  std::vector<std::pair<std::string, Sort>> cFields;
  for (jsize i = 0; i < size; i++)
  {
    // get the pair at index i
    jobject object = env->GetObjectArrayElement(jFields, i);

    // get the object at cvc.Pair.first and convert it to char *
    jstring jFirst = (jstring)env->GetObjectField(object, firstFieldId);
    const char* cFirst = env->GetStringUTFChars(jFirst, nullptr);

    // get the object at cvc.Pair.second and convert it to Sort
    jobject jSecond = env->GetObjectField(object, secondFieldId);
    jlong sortPointer = env->CallLongMethod(jSecond, methodId);
    Sort* sort = (Sort*)sortPointer;

    // add the pair to to the list of fields
    cFields.push_back(std::make_pair(std::string(cFirst), *sort));
  }
  // get the record sort from the solver
  Sort* sort = new Sort(solver->mkRecordSort(cFields));
  // return a pointer to the sort
  return (jlong)sort;
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkSetSort
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkSetSort(JNIEnv* env,
                                                  jobject,
                                                  jlong pointer,
                                                  jlong elementSortPointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Sort* elementSort = (Sort*)elementSortPointer;
  Sort* sort = new Sort(solver->mkSetSort(*elementSort));
  return (jlong)sort;
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkBagSort
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkBagSort(JNIEnv* env,
                                                  jobject,
                                                  jlong pointer,
                                                  jlong elementSortPointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Sort* elementSort = (Sort*)elementSortPointer;
  Sort* sort = new Sort(solver->mkBagSort(*elementSort));
  return (jlong)sort;
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkSequenceSort
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkSequenceSort(JNIEnv* env,
                                                       jobject,
                                                       jlong pointer,
                                                       jlong elementSortPointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Sort* elementSort = (Sort*)elementSortPointer;
  Sort* sort = new Sort(solver->mkSequenceSort(*elementSort));
  return (jlong)sort;
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkSortConstructorSort
 * Signature: (JLjava/lang/String;I)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkSortConstructorSort(
    JNIEnv* env, jobject, jlong pointer, jstring jSymbol, jint arity)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  const char* cSymbol = env->GetStringUTFChars(jSymbol, nullptr);
  Sort* sort = new Sort(
      solver->mkSortConstructorSort(std::string(cSymbol), (size_t)arity));
  return (jlong)sort;
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkTupleSort
 * Signature: (J[J)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkTupleSort(JNIEnv* env,
                                                    jobject,
                                                    jlong pointer,
                                                    jlongArray sortPointers)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  jsize sortsSize = env->GetArrayLength(sortPointers);
  jlong* sortsElements = env->GetLongArrayElements(sortPointers, nullptr);
  if (sortsElements == 0)
  {
    throw CVC4ApiException("Null pointer sortsElements in mkTupleSort");
  }

  std::vector<Sort> sorts;
  for (jsize i = 0; i < sortsSize; i++)
  {
    Sort* sort = (Sort*)sortsElements[i];
    sorts.push_back(*sort);
  }
  env->ReleaseLongArrayElements(sortPointers, sortsElements, 0);

  Sort* sort = new Sort(solver->mkTupleSort(sorts));
  return (jlong)sort;
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

// endregion

/*
 * Class:     cvc_Solver
 * Method:    mkConst
 * Signature: (JJLjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkConst(JNIEnv* env,
                                                jobject,
                                                jlong solverPointer,
                                                jlong sortPointer,
                                                jstring jSymbol)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)solverPointer;
  Sort* sort = (Sort*)sortPointer;
  const char* cSymbol = env->GetStringUTFChars(jSymbol, nullptr);
  Term* term = new Term(solver->mkConst((*sort), std::string(cSymbol)));
  return ((jlong)term);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/* .................................................................... */
/* Create Terms                                                         */
/* .................................................................... */
// region Create Terms

/*
 * Class:     cvc_Solver
 * Method:    mkTerm
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkTerm__J(JNIEnv* env, jobject, jlong)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Term* term = new Term();
  return ((jlong)term);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkTermKind
 * Signature: (JI)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkTermKind(JNIEnv* env,
                                                   jobject,
                                                   jlong pointer,
                                                   jint kind)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Term* term = new Term(solver->mkTerm((Kind)kind));
  return ((jlong)term);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkTermChild
 * Signature: (JJJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkTermChild(
    JNIEnv* env, jobject, jlong pointer, jlong kind, jlong childPointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Term* child = (Term*)childPointer;
  Term* term = new Term(solver->mkTerm((Kind)kind, *child));
  return ((jlong)term);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkTerm
 * Signature: (JIJJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkTerm__JIJJ(JNIEnv* env,
                                                     jobject,
                                                     jlong solverPointer,
                                                     jint kind,
                                                     jlong child1Pointer,
                                                     jlong child2Pointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)solverPointer;
  Term* child1 = (Term*)child1Pointer;
  Term* child2 = (Term*)child2Pointer;
  Term* term = new Term(solver->mkTerm((Kind)kind, *child1, *child2));
  return ((jlong)term);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkTerm
 * Signature: (JIJJJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkTerm__JIJJJ(JNIEnv* env,
                                                      jobject,
                                                      jlong solverPointer,
                                                      jint kind,
                                                      jlong child1Pointer,
                                                      jlong child2Pointer,
                                                      jlong child3Pointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)solverPointer;
  Term* child1 = (Term*)child1Pointer;
  Term* child2 = (Term*)child2Pointer;
  Term* child3 = (Term*)child3Pointer;
  Term* term = new Term(solver->mkTerm((Kind)kind, *child1, *child2, *child3));
  return ((jlong)term);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkTerm
 * Signature: (JI[J)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkTerm__JI_3J(
    JNIEnv* env, jobject, jlong pointer, jint kind, jlongArray childrenPointers)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  // get the size of children pointers
  jsize size = env->GetArrayLength(childrenPointers);
  // allocate buffer for the long array
  jlong* buffer = new jlong[size];
  // copy the java array to the buffer
  env->GetLongArrayRegion(childrenPointers, 0, size, buffer);
  // copy the terms into a vector
  std::vector<Term> children;
  for (jsize i = 0; i < size; i++)
  {
    Term* term = (Term*)buffer[i];
    children.push_back(*term);
  }
  // remove the buffer memory
  delete[] buffer;
  Term* term = new Term(solver->mkTerm((Kind)kind, children));
  return ((jlong)term);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    checkSat
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_checkSat(JNIEnv* env,
                                                 jobject,
                                                 jlong solverPointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)solverPointer;
  Result* resultPointer = new Result(solver->checkSat());
  return ((jlong)resultPointer);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    assertFormula
 * Signature: (JJ)V
 */
JNIEXPORT void JNICALL Java_cvc_Solver_assertFormula(JNIEnv* env,
                                                     jobject,
                                                     jlong solverPointer,
                                                     jlong termPointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)solverPointer;
  Term* term = (Term*)termPointer;
  solver->assertFormula(*term);
  CVC_JAVA_API_TRY_CATCH_END(env);
}

/*
 * Class:     cvc_Solver
 * Method:    push
 * Signature: (JI)V
 */
JNIEXPORT void JNICALL Java_cvc_Solver_push(JNIEnv* env,
                                            jobject,
                                            jlong solverPointer,
                                            jint nscopes)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)solverPointer;
  solver->push(nscopes);
  CVC_JAVA_API_TRY_CATCH_END(env);
}

/*
 * Class:     cvc_Solver
 * Method:    checkEntailed
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_checkEntailed(JNIEnv* env,
                                                      jobject,
                                                      jlong solverPointer,
                                                      jlong termPointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)solverPointer;
  Term* term = (Term*)termPointer;
  Result* resultPointer = new Result(solver->checkEntailed(*term));
  return (jlong)resultPointer;
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    pop
 * Signature: (JI)V
 */
JNIEXPORT void JNICALL Java_cvc_Solver_pop(JNIEnv* env,
                                           jobject,
                                           jlong solverPointer,
                                           jint nscopes)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)solverPointer;
  solver->pop(nscopes);
  CVC_JAVA_API_TRY_CATCH_END(env);
}

/*
 * Class:     cvc_Solver
 * Method:    setOption
 * Signature: (JLjava/lang/String;Ljava/lang/String;)V
 */
JNIEXPORT void JNICALL Java_cvc_Solver_setOption(
    JNIEnv* env, jobject, jlong solverPointer, jstring jOption, jstring jValue)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)solverPointer;
  const char* cOption = env->GetStringUTFChars(jOption, nullptr);
  const char* cValue = env->GetStringUTFChars(jValue, nullptr);
  solver->setOption(std::string(cOption), std::string(cValue));
  CVC_JAVA_API_TRY_CATCH_END(env);
}

/*
 * Class:     cvc_Solver
 * Method:    getValue
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_getValue(JNIEnv* env,
                                                 jobject,
                                                 jlong solverPointer,
                                                 jlong termPointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)solverPointer;
  Term* term = (Term*)termPointer;
  Term* ret = new Term(solver->getValue(*term));
  return (jlong)ret;
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    supportsFloatingPoint
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL
Java_cvc_Solver_supportsFloatingPoint(JNIEnv* env, jobject, jlong solverPointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)solverPointer;
  return (jboolean)solver->supportsFloatingPoint();
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, false);
}

/*
 * Class:     cvc_Solver
 * Method:    mkRoundingMode
 * Signature: (JI)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkRoundingMode(JNIEnv* env,
                                                       jobject,
                                                       jlong solverPointer,
                                                       jint rm)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)solverPointer;
  Term* ret = new Term(solver->mkRoundingMode((RoundingMode)rm));
  return (jlong)ret;
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkDatatypeDecl
 * Signature: (JLjava/lang/String;Z)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkDatatypeDecl(JNIEnv* env,
                                                       jobject,
                                                       jlong solverPointer,
                                                       jstring jName,
                                                       jboolean jIsCoDatatype)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)solverPointer;
  const char* cName = env->GetStringUTFChars(jName, nullptr);
  bool cIsCoDatatype = (bool)jIsCoDatatype;
  DatatypeDecl* decl = new DatatypeDecl(
      solver->mkDatatypeDecl(std::string(cName), cIsCoDatatype));
  return (jlong)decl;
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkDatatypeConstructorDecl
 * Signature: (JLjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkDatatypeConstructorDecl(JNIEnv* env,
                                                                  jobject,
                                                                  jlong pointer,
                                                                  jstring jName)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  const char* cName = env->GetStringUTFChars(jName, nullptr);
  DatatypeConstructorDecl* decl = new DatatypeConstructorDecl(
      solver->mkDatatypeConstructorDecl(std::string(cName)));
  return (jlong)decl;
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkOp
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkOp__J(JNIEnv* env,
                                                jobject,
                                                jlong pointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  // create a null pointer (equivalent of Op op();)
  Op* op = new Op();
  return (jlong)op;
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkOp
 * Signature: (JI)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkOp__JI(JNIEnv* env,
                                                 jobject,
                                                 jlong pointer,
                                                 jint kind)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Op* op = new Op(solver->mkOp((Kind)kind));
  return (jlong)op;
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkOp
 * Signature: (JILjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkOp__JILjava_lang_String_2(
    JNIEnv* env, jobject, jlong pointer, jint kind, jstring jArg)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  std::string cArg(env->GetStringUTFChars(jArg, nullptr));
  Op* op = new Op(solver->mkOp((Kind)kind, cArg));
  return (jlong)op;
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkOp
 * Signature: (JII)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkOp__JII(
    JNIEnv* env, jobject, jlong pointer, jint kind, jint arg)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Op* op = new Op(solver->mkOp((Kind)kind, (uint32_t)arg));
  return (jlong)op;
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkOp
 * Signature: (JIII)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkOp__JIII(
    JNIEnv* env, jobject, jlong pointer, jint kind, jint arg1, jint arg2)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Op* op = new Op(solver->mkOp((Kind)kind, (uint32_t)arg1, (uint32_t)arg2));
  return (jlong)op;
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkTrue
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkTrue(JNIEnv* env,
                                               jobject,
                                               jlong pointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Term* term = new Term(solver->mkTrue());
  return ((jlong)term);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkFalse
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkFalse(JNIEnv* env,
                                                jobject,
                                                jlong pointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Term* term = new Term(solver->mkFalse());
  return ((jlong)term);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkBoolean
 * Signature: (JZ)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkBoolean(JNIEnv* env,
                                                  jobject,
                                                  jlong pointer,
                                                  jboolean val)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Term* term = new Term(solver->mkBoolean((bool)val));
  return ((jlong)term);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkPi
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkPi(JNIEnv* env,
                                             jobject,
                                             jlong pointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Term* term = new Term(solver->mkPi());
  return ((jlong)term);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkInteger
 * Signature: (JLjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkInteger__JLjava_lang_String_2(
    JNIEnv* env, jobject, jlong pointer, jstring jS)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  std::string cS(env->GetStringUTFChars(jS, nullptr));
  Term* term = new Term(solver->mkInteger(cS));
  return ((jlong)term);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkInteger
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkInteger__JJ(JNIEnv* env,
                                                      jobject,
                                                      jlong pointer,
                                                      jlong val)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Term* term = new Term(solver->mkInteger((int64_t)val));
  return ((jlong)term);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkReal
 * Signature: (JLjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkReal__JLjava_lang_String_2(
    JNIEnv* env, jobject, jlong pointer, jstring jS)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  std::string cS(env->GetStringUTFChars(jS, nullptr));
  Term* term = new Term(solver->mkReal(cS));
  return ((jlong)term);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkRealVal
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkRealVal(JNIEnv* env,
                                                  jobject,
                                                  jlong pointer,
                                                  jlong val)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Term* term = new Term(solver->mkReal((int64_t)val));
  return ((jlong)term);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkReal
 * Signature: (JJJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkReal__JJJ(
    JNIEnv* env, jobject, jlong pointer, jlong num, jlong den)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Term* term = new Term(solver->mkReal((int64_t)num, (int64_t)den));
  return ((jlong)term);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkRegexpEmpty
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkRegexpEmpty(JNIEnv* env,
                                                      jobject,
                                                      jlong pointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Term* term = new Term(solver->mkRegexpEmpty());
  return ((jlong)term);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkRegexpSigma
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkRegexpSigma(JNIEnv* env,
                                                      jobject,
                                                      jlong pointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Term* term = new Term(solver->mkRegexpSigma());
  return ((jlong)term);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkEmptySet
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkEmptySet(JNIEnv* env,
                                                   jobject,
                                                   jlong pointer,
                                                   jlong sortPointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Sort* sort = (Sort*)sortPointer;
  Term* term = new Term(solver->mkEmptySet(*sort));
  return ((jlong)term);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkEmptyBag
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkEmptyBag(JNIEnv* env,
                                                   jobject,
                                                   jlong pointer,
                                                   jlong sortPointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Sort* sort = (Sort*)sortPointer;
  Term* term = new Term(solver->mkEmptyBag(*sort));
  return ((jlong)term);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkSepNil
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkSepNil(JNIEnv* env,
                                                 jobject,
                                                 jlong pointer,
                                                 jlong sortPointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Sort* sort = (Sort*)sortPointer;
  Term* term = new Term(solver->mkSepNil(*sort));
  return ((jlong)term);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkString
 * Signature: (JLjava/lang/String;Z)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkString__JLjava_lang_String_2Z(
    JNIEnv* env, jobject, jlong pointer, jstring jS, jboolean useEscSequences)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  std::string cS(env->GetStringUTFChars(jS, nullptr));
  Term* term = new Term(solver->mkString(cS, (bool)useEscSequences));
  return ((jlong)term);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkString
 * Signature: (JB)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkString__JB(JNIEnv* env,
                                                     jobject,
                                                     jlong pointer,
                                                     jbyte c)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Term* term = new Term(solver->mkString((char)c));
  return ((jlong)term);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkString
 * Signature: (J[B)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkString__J_3B(JNIEnv* env,
                                                       jobject,
                                                       jlong pointer,
                                                       jbyteArray jS)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  // get the length of the passed array
  jsize size = env->GetArrayLength(jS);
  // allocate buffer for the byte array
  jbyte* buffer = new jbyte[size];
  // copy the java array to the buffer
  env->GetByteArrayRegion(jS, 0, size, buffer);
  // copy from the buffer to a vector of unsigned
  std::vector<unsigned> s;
  for (jsize i = 0; i < size; i++)
  {
    s.push_back((unsigned)buffer[i]);
  }
  // remove the buffer memory
  delete[] buffer;
  // call mkString on the vector
  Term* term = new Term(solver->mkString(s));
  return ((jlong)term);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkChar
 * Signature: (JLjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkChar(JNIEnv* env,
                                               jobject,
                                               jlong pointer,
                                               jstring jS)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  std::string cS(env->GetStringUTFChars(jS, nullptr));
  Term* term = new Term(solver->mkChar(cS));
  return ((jlong)term);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkEmptySequence
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkEmptySequence(JNIEnv* env,
                                                        jobject,
                                                        jlong pointer,
                                                        jlong sortPointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Sort* sort = (Sort*)sortPointer;
  Term* term = new Term(solver->mkEmptySequence(*sort));
  return ((jlong)term);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkBitVector
 * Signature: (JIJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkBitVector__JIJ(
    JNIEnv* env, jobject, jlong pointer, jint size, jlong val)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Term* term = new Term(solver->mkBitVector((uint32_t)size, (uint64_t)val));
  return ((jlong)term);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkBitVector
 * Signature: (JLjava/lang/String;I)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkBitVector__JLjava_lang_String_2I(
    JNIEnv* env, jobject, jlong pointer, jstring jS, jint base)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  const char* cS = env->GetStringUTFChars(jS, nullptr);
  Term* term = new Term(solver->mkBitVector(std::string(cS), (uint32_t)base));
  return ((jlong)term);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkBitVector
 * Signature: (JILjava/lang/String;I)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkBitVector__JILjava_lang_String_2I(
    JNIEnv* env, jobject, jlong pointer, jint size, jstring jS, jint base)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  const char* cS = env->GetStringUTFChars(jS, nullptr);
  Term* term = new Term(
      solver->mkBitVector((uint32_t)size, std::string(cS), (uint32_t)base));
  return ((jlong)term);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkConstArray
 * Signature: (JJJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkConstArray(
    JNIEnv* env, jobject, jlong pointer, jlong sortPointer, jlong termPointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Sort* sort = (Sort*)sortPointer;
  Term* term = (Term*)termPointer;
  Term* ret = new Term(solver->mkConstArray(*sort, *term));
  return ((jlong)ret);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkPosInf
 * Signature: (JII)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkPosInf(
    JNIEnv* env, jobject, jlong pointer, jint exp, jint sig)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Term* ret = new Term(solver->mkPosInf((uint32_t)exp, (uint32_t)sig));
  return ((jlong)ret);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkNegInf
 * Signature: (JII)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkNegInf(
    JNIEnv* env, jobject, jlong pointer, jint exp, jint sig)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Term* ret = new Term(solver->mkNegInf((uint32_t)exp, (uint32_t)sig));
  return ((jlong)ret);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkNaN
 * Signature: (JII)J
 */
JNIEXPORT jlong JNICALL
Java_cvc_Solver_mkNaN(JNIEnv* env, jobject, jlong pointer, jint exp, jint sig)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Term* term = new Term(solver->mkNaN((uint32_t)exp, (uint32_t)sig));
  return ((jlong)term);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkPosZero
 * Signature: (JII)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkPosZero(
    JNIEnv* env, jobject, jlong pointer, jint exp, jint sig)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Term* ret = new Term(solver->mkPosZero((uint32_t)exp, (uint32_t)sig));
  return ((jlong)ret);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkNegZero
 * Signature: (JII)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkNegZero(
    JNIEnv* env, jobject, jlong pointer, jint exp, jint sig)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Term* ret = new Term(solver->mkNegZero((uint32_t)exp, (uint32_t)sig));
  return ((jlong)ret);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkUninterpretedConst
 * Signature: (JJI)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkUninterpretedConst(
    JNIEnv* env, jobject, jlong pointer, jlong sortPointer, jint index)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Sort* sort = (Sort*)sortPointer;
  Term* term = new Term(solver->mkUninterpretedConst(*sort, (int32_t)index));
  return ((jlong)term);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkAbstractValue
 * Signature: (JLjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkAbstractValue__JLjava_lang_String_2(
    JNIEnv* env, jobject, jlong pointer, jstring jIndex)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  std::string cIndex(env->GetStringUTFChars(jIndex, nullptr));
  Term* term = new Term(solver->mkAbstractValue(cIndex));
  return ((jlong)term);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkAbstractValue
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkAbstractValue__JJ(JNIEnv* env,
                                                            jobject,
                                                            jlong pointer,
                                                            jlong index)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Term* term = new Term(solver->mkAbstractValue((uint64_t)index));
  return ((jlong)term);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkFloatingPoint
 * Signature: (JIIJ)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkFloatingPoint(
    JNIEnv* env, jobject, jlong pointer, jint exp, jint sig, jlong termPointer)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;
  Solver* solver = (Solver*)pointer;
  Term* term = (Term*)termPointer;
  Term* ret =
      new Term(solver->mkFloatingPoint((uint32_t)exp, (uint32_t)sig, *term));
  return ((jlong)ret);
  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc_Solver
 * Method:    mkVar
 * Signature: (JJLjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL Java_cvc_Solver_mkVar(
    JNIEnv* env, jobject, jlong pointer, jlong sortPointer, jstring jSymbol)
{
  CVC_JAVA_API_TRY_CATCH_BEGIN;

  Solver* solver = (Solver*)pointer;
  Sort* sort = (Sort*)sortPointer;
  std::string cSymbol(env->GetStringUTFChars(jSymbol, nullptr));
  Term* ret = new Term(solver->mkVar(*sort, cSymbol));
  return ((jlong)ret);

  CVC_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}