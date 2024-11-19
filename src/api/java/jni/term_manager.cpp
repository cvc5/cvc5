/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 Java API.
 */

#include <cvc5/cvc5.h>

#include <iostream>

#include "api/java/jni/api_utilities.h"
#include "api_utilities.h"
#include "io_github_cvc5_TermManager.h"

using namespace cvc5;

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    newTermManager
 * Signature: ()J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_newTermManager(JNIEnv*,
                                                                       jclass)
{
  TermManager* tm = new TermManager();
  return reinterpret_cast<jlong>(tm);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_io_github_cvc5_TermManager_deletePointer(
    JNIEnv* env, jobject, jlong pointer)
{
  ApiManager::currentAM()->deletePointer(env, pointer);
  delete (reinterpret_cast<TermManager*>(pointer));
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    getStatistics
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_getStatistics(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Statistics* retPointer = new Statistics(tm->getStatistics());
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    getBooleanSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_getBooleanSort(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Sort* sortPointer = new Sort(tm->getBooleanSort());
  return reinterpret_cast<jlong>(sortPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    getIntegerSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_getIntegerSort(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Sort* sortPointer = new Sort(tm->getIntegerSort());
  return reinterpret_cast<jlong>(sortPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    getRealSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_TermManager_getRealSort(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Sort* sortPointer = new Sort(tm->getRealSort());
  return reinterpret_cast<jlong>(sortPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    getRegExpSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_getRegExpSort(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Sort* sortPointer = new Sort(tm->getRegExpSort());
  return reinterpret_cast<jlong>(sortPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    getRoundingModeSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_getRoundingModeSort(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Sort* sortPointer = new Sort(tm->getRoundingModeSort());
  return reinterpret_cast<jlong>(sortPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    getStringSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_getStringSort(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Sort* sortPointer = new Sort(tm->getStringSort());
  return reinterpret_cast<jlong>(sortPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkArraySort
 * Signature: (JJJ)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_TermManager_mkArraySort(JNIEnv* env,
                                            jobject,
                                            jlong pointer,
                                            jlong indexSortPointer,
                                            jlong elementSortPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Sort* indexSort = reinterpret_cast<Sort*>(indexSortPointer);
  Sort* elementSort = reinterpret_cast<Sort*>(elementSortPointer);
  Sort* retPointer = new Sort(tm->mkArraySort(*indexSort, *elementSort));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkBitVectorSort
 * Signature: (JI)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkBitVectorSort(
    JNIEnv* env, jobject, jlong pointer, jint size)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Sort* sortPointer = new Sort(tm->mkBitVectorSort((uint32_t)size));
  return reinterpret_cast<jlong>(sortPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkFiniteFieldSort
 * Signature: (JLjava/lang/String)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkFiniteFieldSort(
    JNIEnv* env, jobject, jlong pointer, jstring size, jint base)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  const char* cSize = env->GetStringUTFChars(size, nullptr);
  Sort* sortPointer =
      new Sort(tm->mkFiniteFieldSort(std::string(cSize), (uint32_t)base));
  env->ReleaseStringUTFChars(size, cSize);
  return reinterpret_cast<jlong>(sortPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkFloatingPointSort
 * Signature: (JII)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkFloatingPointSort(
    JNIEnv* env, jobject, jlong pointer, jint exp, jint sig)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Sort* sortPointer =
      new Sort(tm->mkFloatingPointSort((uint32_t)exp, (uint32_t)sig));
  return reinterpret_cast<jlong>(sortPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkDatatypeSort
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkDatatypeSort(
    JNIEnv* env, jobject, jlong pointer, jlong datatypeDeclPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  DatatypeDecl* decl = reinterpret_cast<DatatypeDecl*>(datatypeDeclPointer);
  Sort* retPointer = new Sort(tm->mkDatatypeSort(*decl));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkDatatypeSorts
 * Signature: (J[J)[J
 */
JNIEXPORT jlongArray JNICALL Java_io_github_cvc5_TermManager_mkDatatypeSorts(
    JNIEnv* env, jobject, jlong pointer, jlongArray jDecls)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  std::vector<DatatypeDecl> decls =
      getObjectsFromPointers<DatatypeDecl>(env, jDecls);
  std::vector<Sort> sorts = tm->mkDatatypeSorts(decls);
  std::vector<jlong> sortPointers(sorts.size());

  for (size_t i = 0; i < sorts.size(); i++)
  {
    sortPointers[i] = reinterpret_cast<jlong>(new Sort(sorts[i]));
  }

  jlongArray ret = env->NewLongArray(sorts.size());
  env->SetLongArrayRegion(ret, 0, sorts.size(), sortPointers.data());
  return ret;
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, nullptr);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkFunctionSort
 * Signature: (J[JJ)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_TermManager_mkFunctionSort(JNIEnv* env,
                                               jobject,
                                               jlong pointer,
                                               jlongArray sortPointers,
                                               jlong codomainPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Sort* codomain = reinterpret_cast<Sort*>(codomainPointer);
  std::vector<Sort> sorts = getObjectsFromPointers<Sort>(env, sortPointers);
  Sort* retPointer = new Sort(tm->mkFunctionSort(sorts, *codomain));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkParamSort
 * Signature: (JLjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_TermManager_mkParamSort__JLjava_lang_String_2(
    JNIEnv* env, jobject, jlong pointer, jstring jSymbol)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  const char* s = env->GetStringUTFChars(jSymbol, nullptr);
  std::string cSymbol(s);
  Sort* retPointer = new Sort(tm->mkParamSort(cSymbol));
  env->ReleaseStringUTFChars(jSymbol, s);
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkSkolem
 * Signature: (JI[J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkSkolem(
    JNIEnv* env, jobject, jlong pointer, jint jSkolemId, jlongArray jIndices)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  SkolemId id = static_cast<SkolemId>(jSkolemId);
  std::vector<Term> indices = getObjectsFromPointers<Term>(env, jIndices);
  Term* retPointer = new Term(tm->mkSkolem(id, indices));
  return reinterpret_cast<jlong>(retPointer);

  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    getNumIndicesForSkolemId
 * Signature: (JI)I
 */
JNIEXPORT jint JNICALL Java_io_github_cvc5_TermManager_getNumIndicesForSkolemId(
    JNIEnv* env, jobject, jlong pointer, jint jSkolemId)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  SkolemId id = static_cast<SkolemId>(jSkolemId);
  int numIndices = tm->getNumIndicesForSkolemId(id);
  return numIndices;

  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkParamSort
 * Signature: (JL)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkParamSort__J(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Sort* retPointer = new Sort(tm->mkParamSort());
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkPredicateSort
 * Signature: (J[J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkPredicateSort(
    JNIEnv* env, jobject, jlong pointer, jlongArray sortPointers)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  std::vector<Sort> sorts = getObjectsFromPointers<Sort>(env, sortPointers);
  Sort* retPointer = new Sort(tm->mkPredicateSort(sorts));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkRecordSort
 * Signature: (J[Lio/github/cvc5/Pair;)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkRecordSort(
    JNIEnv* env, jobject, jlong pointer, jobjectArray jFields)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  jsize size = env->GetArrayLength(jFields);
  // Lio/github/cvc5/Pair; is signature of cvc5.Pair<String, Long>
  jclass pairClass = env->FindClass("Lio/github/cvc5/Pair;");
  jclass longClass = env->FindClass("Ljava/lang/Long;");
  // Ljava/lang/Object; is the signature of cvc5.Pair.first field
  jfieldID firstFieldId =
      env->GetFieldID(pairClass, "first", "Ljava/lang/Object;");
  // Ljava/lang/Object; is the signature of cvc5.Pair.second field
  jfieldID secondFieldId =
      env->GetFieldID(pairClass, "second", "Ljava/lang/Object;");
  // we need to call method longValue to get long Long object
  jmethodID methodId = env->GetMethodID(longClass, "longValue", "()J");

  std::vector<std::pair<std::string, Sort>> cFields;
  for (jsize i = 0; i < size; i++)
  {
    // get the pair at index i
    jobject object = env->GetObjectArrayElement(jFields, i);

    // get the object at cvc5.Pair.first and convert it to char *
    jstring jFirst = (jstring)env->GetObjectField(object, firstFieldId);
    const char* cFirst = env->GetStringUTFChars(jFirst, nullptr);

    // get the object at cvc5.Pair.second and convert it to Sort
    jobject jSecond = env->GetObjectField(object, secondFieldId);
    jlong sortPointer = env->CallLongMethod(jSecond, methodId);
    Sort* sort = reinterpret_cast<Sort*>(sortPointer);

    // add the pair to to the list of fields
    cFields.push_back(std::make_pair(std::string(cFirst), *sort));
  }
  // get the record sort from the tm
  Sort* retPointer = new Sort(tm->mkRecordSort(cFields));
  // return a pointer to the sort
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkSetSort
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkSetSort(
    JNIEnv* env, jobject, jlong pointer, jlong elemSortPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Sort* elemSort = reinterpret_cast<Sort*>(elemSortPointer);
  Sort* retPointer = new Sort(tm->mkSetSort(*elemSort));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkBagSort
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkBagSort(
    JNIEnv* env, jobject, jlong pointer, jlong elemSortPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Sort* elemSort = reinterpret_cast<Sort*>(elemSortPointer);
  Sort* retPointer = new Sort(tm->mkBagSort(*elemSort));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkSequenceSort
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkSequenceSort(
    JNIEnv* env, jobject, jlong pointer, jlong elemSortPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Sort* elemSort = reinterpret_cast<Sort*>(elemSortPointer);
  Sort* sortPointer = new Sort(tm->mkSequenceSort(*elemSort));
  return reinterpret_cast<jlong>(sortPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkAbstractSort
 * Signature: (JI)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkAbstractSort(
    JNIEnv* env, jobject, jlong pointer, jint kindValue)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;

  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  SortKind kind = (SortKind)kindValue;
  Sort* sort = new Sort(tm->mkAbstractSort(kind));
  return reinterpret_cast<jlong>(sort);

  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkUninterpretedSort
 * Signature: (JLjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_TermManager_mkUninterpretedSort__JLjava_lang_String_2(
    JNIEnv* env, jobject, jlong pointer, jstring jSymbol)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;

  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  const char* cSymbol = env->GetStringUTFChars(jSymbol, nullptr);
  Sort* sort = new Sort(tm->mkUninterpretedSort(std::string(cSymbol)));
  env->ReleaseStringUTFChars(jSymbol, cSymbol);
  return reinterpret_cast<jlong>(sort);

  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkUninterpretedSort
 * Signature: (JL)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkUninterpretedSort__J(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;

  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Sort* sort = new Sort(tm->mkUninterpretedSort());
  return reinterpret_cast<jlong>(sort);

  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkUnresolvedDatatypeSort
 * Signature: (JLjava/lang/String;I)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_TermManager_mkUnresolvedDatatypeSort(
    JNIEnv* env, jobject, jlong pointer, jstring jSymbol, jint arity)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;

  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  const char* s = env->GetStringUTFChars(jSymbol, nullptr);
  std::string cSymbol(s);
  Sort* retPointer =
      new Sort(tm->mkUnresolvedDatatypeSort(cSymbol, (size_t)arity));
  env->ReleaseStringUTFChars(jSymbol, s);
  return reinterpret_cast<jlong>(retPointer);

  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkUninterpretedSortConstructorSort
 * Signature: (JLIjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_TermManager_mkUninterpretedSortConstructorSort__JILjava_lang_String_2(
    JNIEnv* env, jobject, jlong pointer, jint arity, jstring jSymbol)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;

  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  const char* s = env->GetStringUTFChars(jSymbol, nullptr);
  std::string cSymbol(s);
  Sort* retPointer =
      new Sort(tm->mkUninterpretedSortConstructorSort((size_t)arity, cSymbol));
  env->ReleaseStringUTFChars(jSymbol, s);
  return reinterpret_cast<jlong>(retPointer);

  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkUninterpretedSortConstructorSort
 * Signature: (JLI)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_TermManager_mkUninterpretedSortConstructorSort__JI(
    JNIEnv* env, jobject, jlong pointer, jint arity)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;

  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Sort* retPointer =
      new Sort(tm->mkUninterpretedSortConstructorSort((size_t)arity));
  return reinterpret_cast<jlong>(retPointer);

  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkTupleSort
 * Signature: (J[J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkTupleSort(
    JNIEnv* env, jobject, jlong pointer, jlongArray sortPointers)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  std::vector<Sort> sorts = getObjectsFromPointers<Sort>(env, sortPointers);
  Sort* retPointer = new Sort(tm->mkTupleSort(sorts));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkNullableSort
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkNullableSort(
    JNIEnv* env, jobject, jlong pointer, jlong sortPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Sort* sort = reinterpret_cast<Sort*>(sortPointer);
  Sort* retPointer = new Sort(tm->mkNullableSort(*sort));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkTerm
 * Signature: (JI)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkTerm__JI(
    JNIEnv* env, jobject, jlong pointer, jint kindValue)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Kind kind = (Kind)kindValue;
  Term* retPointer = new Term(tm->mkTerm(kind));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkTerm
 * Signature: (JIJ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkTerm__JIJ(
    JNIEnv* env, jobject, jlong pointer, jint kindValue, jlong childPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Kind kind = (Kind)kindValue;
  Term* child = reinterpret_cast<Term*>(childPointer);
  Term* termPointer = new Term(tm->mkTerm(kind, {*child}));
  return reinterpret_cast<jlong>(termPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkTerm
 * Signature: (JIJJ)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_TermManager_mkTerm__JIJJ(JNIEnv* env,
                                             jobject,
                                             jlong pointer,
                                             jint kindValue,
                                             jlong child1Pointer,
                                             jlong child2Pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Kind kind = (Kind)kindValue;
  Term* child1 = reinterpret_cast<Term*>(child1Pointer);
  Term* child2 = reinterpret_cast<Term*>(child2Pointer);
  Term* termPointer = new Term(tm->mkTerm(kind, {*child1, *child2}));
  return reinterpret_cast<jlong>(termPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkTerm
 * Signature: (JIJJJ)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_TermManager_mkTerm__JIJJJ(JNIEnv* env,
                                              jobject,
                                              jlong pointer,
                                              jint kindValue,
                                              jlong child1Pointer,
                                              jlong child2Pointer,
                                              jlong child3Pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Kind kind = (Kind)kindValue;
  Term* child1 = reinterpret_cast<Term*>(child1Pointer);
  Term* child2 = reinterpret_cast<Term*>(child2Pointer);
  Term* child3 = reinterpret_cast<Term*>(child3Pointer);
  Term* retPointer = new Term(tm->mkTerm(kind, {*child1, *child2, *child3}));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkTerm
 * Signature: (JI[J)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_TermManager_mkTerm__JI_3J(JNIEnv* env,
                                              jobject,
                                              jlong pointer,
                                              jint kindValue,
                                              jlongArray childrenPointers)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Kind kind = (Kind)kindValue;
  std::vector<Term> children =
      getObjectsFromPointers<Term>(env, childrenPointers);
  Term* retPointer = new Term(tm->mkTerm(kind, children));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkTerm
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkTerm__JJ(
    JNIEnv* env, jobject, jlong pointer, jlong opPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Op* op = reinterpret_cast<Op*>(opPointer);
  Term* retPointer = new Term(tm->mkTerm(*op));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkTerm
 * Signature: (JJJ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkTerm__JJJ(
    JNIEnv* env, jobject, jlong pointer, jlong opPointer, jlong childPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Op* op = reinterpret_cast<Op*>(opPointer);
  Term* child = reinterpret_cast<Term*>(childPointer);
  Term* retPointer = new Term(tm->mkTerm(*op, {*child}));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkTerm
 * Signature: (JJJJ)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_TermManager_mkTerm__JJJJ(JNIEnv* env,
                                             jobject,
                                             jlong pointer,
                                             jlong opPointer,
                                             jlong child1Pointer,
                                             jlong child2Pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Op* op = reinterpret_cast<Op*>(opPointer);
  Term* child1 = reinterpret_cast<Term*>(child1Pointer);
  Term* child2 = reinterpret_cast<Term*>(child2Pointer);
  Term* retPointer = new Term(tm->mkTerm(*op, {*child1, *child2}));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkTerm
 * Signature: (JJJJJ)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_TermManager_mkTerm__JJJJJ(JNIEnv* env,
                                              jobject,
                                              jlong pointer,
                                              jlong opPointer,
                                              jlong child1Pointer,
                                              jlong child2Pointer,
                                              jlong child3Pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Op* op = reinterpret_cast<Op*>(opPointer);
  Term* child1 = reinterpret_cast<Term*>(child1Pointer);
  Term* child2 = reinterpret_cast<Term*>(child2Pointer);
  Term* child3 = reinterpret_cast<Term*>(child3Pointer);
  Term* retPointer = new Term(tm->mkTerm(*op, {*child1, *child2, *child3}));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkTerm
 * Signature: (JJ[J)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_TermManager_mkTerm__JJ_3J(JNIEnv* env,
                                              jobject,
                                              jlong pointer,
                                              jlong opPointer,
                                              jlongArray childrenPointers)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Op* op = reinterpret_cast<Op*>(opPointer);
  std::vector<Term> children =
      getObjectsFromPointers<Term>(env, childrenPointers);
  Term* retPointer = new Term(tm->mkTerm(*op, children));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkTuple
 * Signature: (J[J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkTuple(
    JNIEnv* env, jobject, jlong pointer, jlongArray termPointers)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  std::vector<Term> terms = getObjectsFromPointers<Term>(env, termPointers);
  Term* retPointer = new Term(tm->mkTuple(terms));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkNullableSome
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkNullableSome(
    JNIEnv* env, jobject, jlong pointer, jlong termPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Term* term = reinterpret_cast<Term*>(termPointer);
  Term* retPointer = new Term(tm->mkNullableSome(*term));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkNullableVal
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkNullableVal(
    JNIEnv* env, jobject, jlong pointer, jlong termPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Term* term = reinterpret_cast<Term*>(termPointer);
  Term* retPointer = new Term(tm->mkNullableVal(*term));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkNullableIsNull
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkNullableIsNull(
    JNIEnv* env, jobject, jlong pointer, jlong termPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Term* term = reinterpret_cast<Term*>(termPointer);
  Term* retPointer = new Term(tm->mkNullableIsNull(*term));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkNullableIsSome
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkNullableIsSome(
    JNIEnv* env, jobject, jlong pointer, jlong termPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Term* term = reinterpret_cast<Term*>(termPointer);
  Term* retPointer = new Term(tm->mkNullableIsSome(*term));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkNullableNull
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkNullableNull(
    JNIEnv* env, jobject, jlong pointer, jlong sortPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Sort* sort = reinterpret_cast<Sort*>(sortPointer);
  Term* retPointer = new Term(tm->mkNullableNull(*sort));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkNullableLift
 * Signature: (JI[J)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_TermManager_mkNullableLift(JNIEnv* env,
                                               jobject,
                                               jlong pointer,
                                               jint kindValue,
                                               jlongArray termPointers)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Kind kind = (Kind)kindValue;
  std::vector<Term> terms = getObjectsFromPointers<Term>(env, termPointers);
  Term* retPointer = new Term(tm->mkNullableLift(kind, terms));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkOp
 * Signature: (JI)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkOp__JI(JNIEnv* env,
                                                                 jobject,
                                                                 jlong pointer,
                                                                 jint kindValue)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Kind kind = (Kind)kindValue;
  Op* retPointer = new Op(tm->mkOp(kind));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkOp
 * Signature: (JILjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_TermManager_mkOp__JILjava_lang_String_2(
    JNIEnv* env, jobject, jlong pointer, jint kindValue, jstring jArg)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Kind kind = (Kind)kindValue;
  const char* s = env->GetStringUTFChars(jArg, nullptr);
  std::string cArg(s);

  Op* retPointer = new Op(tm->mkOp(kind, cArg));

  env->ReleaseStringUTFChars(jArg, s);
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkOp
 * Signature: (JII)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkOp__JII(
    JNIEnv* env, jobject, jlong pointer, jint kindValue, jint arg)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Kind kind = (Kind)kindValue;
  Op* retPointer = new Op(tm->mkOp(kind, {(uint32_t)arg}));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkOp
 * Signature: (JIII)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkOp__JIII(
    JNIEnv* env, jobject, jlong pointer, jint kindValue, jint arg1, jint arg2)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Kind kind = (Kind)kindValue;
  Op* retPointer = new Op(tm->mkOp(kind, {(uint32_t)arg1, (uint32_t)arg2}));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkOp
 * Signature: (JI[I)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkOp__JI_3I(
    JNIEnv* env, jobject, jlong pointer, jint kindValue, jintArray jArgs)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Kind kind = (Kind)kindValue;

  jsize size = env->GetArrayLength(jArgs);
  jint* argElements = env->GetIntArrayElements(jArgs, nullptr);

  std::vector<uint32_t> cArgs(size);
  for (jsize i = 0; i < size; i++)
  {
    cArgs[i] = (uint32_t)argElements[i];
  }
  env->ReleaseIntArrayElements(jArgs, argElements, 0);

  Op* retPointer = new Op(tm->mkOp(kind, cArgs));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkTrue
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkTrue(JNIEnv* env,
                                                               jobject,
                                                               jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Term* termPointer = new Term(tm->mkTrue());
  return reinterpret_cast<jlong>(termPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkFalse
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkFalse(JNIEnv* env,
                                                                jobject,
                                                                jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Term* termPointer = new Term(tm->mkFalse());
  return reinterpret_cast<jlong>(termPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkBoolean
 * Signature: (JZ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkBoolean(JNIEnv* env,
                                                                  jobject,
                                                                  jlong pointer,
                                                                  jboolean val)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Term* retPointer = new Term(tm->mkBoolean((bool)val));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkPi
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkPi(JNIEnv* env,
                                                             jobject,
                                                             jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Term* retPointer = new Term(tm->mkPi());
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkInteger
 * Signature: (JLjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_TermManager_mkInteger__JLjava_lang_String_2(JNIEnv* env,
                                                                jobject,
                                                                jlong pointer,
                                                                jstring jS)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  const char* s = env->GetStringUTFChars(jS, nullptr);
  std::string cS(s);
  Term* retPointer = new Term(tm->mkInteger(cS));
  env->ReleaseStringUTFChars(jS, s);
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkInteger
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkInteger__JJ(
    JNIEnv* env, jobject, jlong pointer, jlong val)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Term* termPointer = new Term(tm->mkInteger((int64_t)val));
  return reinterpret_cast<jlong>(termPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkReal
 * Signature: (JLjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_TermManager_mkReal__JLjava_lang_String_2(JNIEnv* env,
                                                             jobject,
                                                             jlong pointer,
                                                             jstring jS)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  const char* s = env->GetStringUTFChars(jS, nullptr);
  std::string cS(s);
  Term* retPointer = new Term(tm->mkReal(cS));
  env->ReleaseStringUTFChars(jS, s);
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkRealValue
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkRealValue(
    JNIEnv* env, jobject, jlong pointer, jlong val)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Term* retPointer = new Term(tm->mkReal((int64_t)val));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkReal
 * Signature: (JJJ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkReal__JJJ(
    JNIEnv* env, jobject, jlong pointer, jlong num, jlong den)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Term* retPointer = new Term(tm->mkReal((int64_t)num, (int64_t)den));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkRegexpNone
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkRegexpNone(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Term* retPointer = new Term(tm->mkRegexpNone());
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkRegexpAll
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_TermManager_mkRegexpAll(JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Term* retPointer = new Term(tm->mkRegexpAll());
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkRegexpAllchar
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkRegexpAllchar(
    JNIEnv* env, jobject, jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Term* retPointer = new Term(tm->mkRegexpAllchar());
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkEmptySet
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkEmptySet(
    JNIEnv* env, jobject, jlong pointer, jlong sortPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Sort* sort = reinterpret_cast<Sort*>(sortPointer);
  Term* retPointer = new Term(tm->mkEmptySet(*sort));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkEmptyBag
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkEmptyBag(
    JNIEnv* env, jobject, jlong pointer, jlong sortPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Sort* sort = reinterpret_cast<Sort*>(sortPointer);
  Term* retPointer = new Term(tm->mkEmptyBag(*sort));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkSepEmp
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkSepEmp(JNIEnv* env,
                                                                 jobject,
                                                                 jlong pointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Term* retPointer = new Term(tm->mkSepEmp());
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkSepNil
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkSepNil(
    JNIEnv* env, jobject, jlong pointer, jlong sortPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Sort* sort = reinterpret_cast<Sort*>(sortPointer);
  Term* retPointer = new Term(tm->mkSepNil(*sort));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkString
 * Signature: (JLjava/lang/String;Z)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_TermManager_mkString__JLjava_lang_String_2Z(
    JNIEnv* env, jobject, jlong pointer, jstring jS, jboolean useEscSequences)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  const char* s = env->GetStringUTFChars(jS, nullptr);
  std::string cS(s);
  Term* retPointer = new Term(tm->mkString(cS, (bool)useEscSequences));
  env->ReleaseStringUTFChars(jS, s);
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkEmptySequence
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkEmptySequence(
    JNIEnv* env, jobject, jlong pointer, jlong sortPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Sort* sort = reinterpret_cast<Sort*>(sortPointer);
  Term* retPointer = new Term(tm->mkEmptySequence(*sort));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkUniverseSet
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkUniverseSet(
    JNIEnv* env, jobject, jlong pointer, jlong sortPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Sort* sort = reinterpret_cast<Sort*>(sortPointer);
  Term* retPointer = new Term(tm->mkUniverseSet(*sort));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkBitVector
 * Signature: (JIJ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkBitVector__JIJ(
    JNIEnv* env, jobject, jlong pointer, jint size, jlong val)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Term* retPointer = new Term(tm->mkBitVector((uint32_t)size, (uint64_t)val));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkBitVector
 * Signature: (JILjava/lang/String;I)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_TermManager_mkBitVector__JILjava_lang_String_2I(
    JNIEnv* env, jobject, jlong pointer, jint size, jstring jS, jint base)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  const char* s = env->GetStringUTFChars(jS, nullptr);
  std::string cS(s);
  Term* retPointer =
      new Term(tm->mkBitVector((uint32_t)size, cS, (uint32_t)base));
  env->ReleaseStringUTFChars(jS, s);
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkFiniteFieldElem
 * Signature: (JLjava/lang/String;J)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_TermManager_mkFiniteFieldElem(JNIEnv* env,
                                                  jobject,
                                                  jlong pointer,
                                                  jstring jS,
                                                  jlong sortPointer,
                                                  jint base)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Sort* sort = reinterpret_cast<Sort*>(sortPointer);
  const char* s = env->GetStringUTFChars(jS, nullptr);
  std::string cS(s);
  Term* retPointer = new Term(tm->mkFiniteFieldElem(cS, *sort, (uint32_t)base));
  env->ReleaseStringUTFChars(jS, s);
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkConstArray
 * Signature: (JJJ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkConstArray(
    JNIEnv* env, jobject, jlong pointer, jlong sortPointer, jlong valPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Sort* sort = reinterpret_cast<Sort*>(sortPointer);
  Term* val = reinterpret_cast<Term*>(valPointer);
  Term* retPointer = new Term(tm->mkConstArray(*sort, *val));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkFloatingPointPosInf
 * Signature: (JII)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkFloatingPointPosInf(
    JNIEnv* env, jobject, jlong pointer, jint exp, jint sig)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Term* retPointer =
      new Term(tm->mkFloatingPointPosInf((uint32_t)exp, (uint32_t)sig));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkFloatingPointNegInf
 * Signature: (JII)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkFloatingPointNegInf(
    JNIEnv* env, jobject, jlong pointer, jint exp, jint sig)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Term* retPointer =
      new Term(tm->mkFloatingPointNegInf((uint32_t)exp, (uint32_t)sig));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkFloatingPointNaN
 * Signature: (JII)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkFloatingPointNaN(
    JNIEnv* env, jobject, jlong pointer, jint exp, jint sig)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Term* retPointer =
      new Term(tm->mkFloatingPointNaN((uint32_t)exp, (uint32_t)sig));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkFloatingPointPosZero
 * Signature: (JII)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkFloatingPointPosZero(
    JNIEnv* env, jobject, jlong pointer, jint exp, jint sig)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Term* retPointer =
      new Term(tm->mkFloatingPointPosZero((uint32_t)exp, (uint32_t)sig));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkFloatingPointNegZero
 * Signature: (JII)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkFloatingPointNegZero(
    JNIEnv* env, jobject, jlong pointer, jint exp, jint sig)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Term* retPointer =
      new Term(tm->mkFloatingPointNegZero((uint32_t)exp, (uint32_t)sig));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkRoundingMode
 * Signature: (JI)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkRoundingMode(
    JNIEnv* env, jobject, jlong pointer, jint rm)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Term* retPointer = new Term(tm->mkRoundingMode((RoundingMode)rm));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkFloatingPoint
 * Signature: (JIIJ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkFloatingPoint(
    JNIEnv* env, jobject, jlong pointer, jint exp, jint sig, jlong valPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Term* val = reinterpret_cast<Term*>(valPointer);
  Term* retPointer =
      new Term(tm->mkFloatingPoint((uint32_t)exp, (uint32_t)sig, *val));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkFloatingPoint
 * Signature: (JJJJ)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_TermManager_mkFloatingPointX(JNIEnv* env,
                                                 jobject,
                                                 jlong pointer,
                                                 jlong signPointer,
                                                 jlong expPointer,
                                                 jlong sigPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Term* sign = reinterpret_cast<Term*>(signPointer);
  Term* exp = reinterpret_cast<Term*>(expPointer);
  Term* sig = reinterpret_cast<Term*>(sigPointer);
  Term* retPointer = new Term(tm->mkFloatingPoint(*sign, *exp, *sig));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkCardinalityConstraint
 * Signature: (JJI)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkCardinalityConstraint(
    JNIEnv* env, jobject, jlong pointer, jlong sortPointer, jint upperBound)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Sort* sort = reinterpret_cast<Sort*>(sortPointer);
  Term* retPointer =
      new Term(tm->mkCardinalityConstraint(*sort, (int32_t)upperBound));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkConst
 * Signature: (JJLjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_TermManager_mkConst__JJLjava_lang_String_2(
    JNIEnv* env, jobject, jlong pointer, jlong sortPointer, jstring jSymbol)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Sort* sort = reinterpret_cast<Sort*>(sortPointer);
  const char* s = env->GetStringUTFChars(jSymbol, nullptr);
  std::string cSymbol(s);
  Term* retPointer = new Term(tm->mkConst(*sort, cSymbol));
  env->ReleaseStringUTFChars(jSymbol, s);
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkConst
 * Signature: (JJ)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkConst__JJ(
    JNIEnv* env, jobject, jlong pointer, jlong sortPointer)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Sort* sort = reinterpret_cast<Sort*>(sortPointer);
  Term* retPointer = new Term(tm->mkConst(*sort));
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkVar
 * Signature: (JJLjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL Java_io_github_cvc5_TermManager_mkVar(
    JNIEnv* env, jobject, jlong pointer, jlong sortPointer, jstring jSymbol)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;

  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  Sort* sort = reinterpret_cast<Sort*>(sortPointer);
  const char* s = env->GetStringUTFChars(jSymbol, nullptr);
  std::string cSymbol(s);
  Term* ret = new Term(tm->mkVar(*sort, cSymbol));
  env->ReleaseStringUTFChars(jSymbol, s);
  return reinterpret_cast<jlong>(ret);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkDatatypeConstructorDecl
 * Signature: (JLjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_TermManager_mkDatatypeConstructorDecl(JNIEnv* env,
                                                          jobject,
                                                          jlong pointer,
                                                          jstring jName)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  const char* s = env->GetStringUTFChars(jName, nullptr);
  std::string cName(s);

  DatatypeConstructorDecl* retPointer =
      new DatatypeConstructorDecl(tm->mkDatatypeConstructorDecl(cName));
  env->ReleaseStringUTFChars(jName, s);
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkDatatypeDecl
 * Signature: (JLjava/lang/String;Z)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_TermManager_mkDatatypeDecl__JLjava_lang_String_2Z(
    JNIEnv* env, jobject, jlong pointer, jstring jName, jboolean isCoDatatype)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  const char* s = env->GetStringUTFChars(jName, nullptr);
  std::string cName(s);
  DatatypeDecl* retPointer =
      new DatatypeDecl(tm->mkDatatypeDecl(cName, (bool)isCoDatatype));
  env->ReleaseStringUTFChars(jName, s);
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     io_github_cvc5_TermManager
 * Method:    mkDatatypeDecl
 * Signature: (JLjava/lang/String;[JZ)J
 */
JNIEXPORT jlong JNICALL
Java_io_github_cvc5_TermManager_mkDatatypeDecl__JLjava_lang_String_2_3JZ(
    JNIEnv* env,
    jobject,
    jlong pointer,
    jstring jName,
    jlongArray jParams,
    jboolean isCoDatatype)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  TermManager* tm = reinterpret_cast<TermManager*>(pointer);
  const char* s = env->GetStringUTFChars(jName, nullptr);
  std::string cName(s);
  std::vector<Sort> params = getObjectsFromPointers<Sort>(env, jParams);
  DatatypeDecl* retPointer =
      new DatatypeDecl(tm->mkDatatypeDecl(cName, params, (bool)isCoDatatype));
  env->ReleaseStringUTFChars(jName, s);
  return reinterpret_cast<jlong>(retPointer);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}
