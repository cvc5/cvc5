#include "cvc5_Sort.h"

#include "api/cpp/cvc5.h"
#include "cvc5JavaApi.h"

using namespace cvc5::api;

/*
 * Class:     cvc5_Sort
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_cvc5_Sort_deletePointer(JNIEnv*, jclass, jlong);

/*
 * Class:     cvc5_Sort
 * Method:    equals
 * Signature: (JJ)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_equals(JNIEnv* env,
                                                 jobject,
                                                 jlong pointer1,
                                                 jlong pointer2)
{
  CVC5_JAVA_API_TRY_CATCH_BEGIN;
  Sort sort1 = *(Sort*)pointer1;
  Sort sort2 = *(Sort*)pointer2;
  return (jboolean)(sort1 == sort2);
  CVC5_JAVA_API_TRY_CATCH_END_RETURN(env, 0);
}

/*
 * Class:     cvc5_Sort
 * Method:    compareTo
 * Signature: (JJ)I
 */
JNIEXPORT jint JNICALL Java_cvc5_Sort_compareTo(JNIEnv*, jobject, jlong, jlong);

/*
 * Class:     cvc5_Sort
 * Method:    isNull
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isNull(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Sort
 * Method:    isBoolean
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isBoolean(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Sort
 * Method:    isInteger
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isInteger(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Sort
 * Method:    isReal
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isReal(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Sort
 * Method:    isString
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isString(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Sort
 * Method:    isRegExp
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isRegExp(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Sort
 * Method:    isRoundingMode
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isRoundingMode(JNIEnv*,
                                                         jobject,
                                                         jlong);

/*
 * Class:     cvc5_Sort
 * Method:    isBitVector
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isBitVector(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Sort
 * Method:    isFloatingPoint
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isFloatingPoint(JNIEnv*,
                                                          jobject,
                                                          jlong);

/*
 * Class:     cvc5_Sort
 * Method:    isDatatype
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isDatatype(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Sort
 * Method:    isParametricDatatype
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isParametricDatatype(JNIEnv*,
                                                               jobject,
                                                               jlong);

/*
 * Class:     cvc5_Sort
 * Method:    isConstructor
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isConstructor(JNIEnv*,
                                                        jobject,
                                                        jlong);

/*
 * Class:     cvc5_Sort
 * Method:    isSelector
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isSelector(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Sort
 * Method:    isTester
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isTester(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Sort
 * Method:    isFunction
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isFunction(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Sort
 * Method:    isPredicate
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isPredicate(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Sort
 * Method:    isTuple
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isTuple(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Sort
 * Method:    isRecord
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isRecord(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Sort
 * Method:    isArray
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isArray(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Sort
 * Method:    isSet
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isSet(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Sort
 * Method:    isBag
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isBag(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Sort
 * Method:    isSequence
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isSequence(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Sort
 * Method:    isUninterpretedSort
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isUninterpretedSort(JNIEnv*,
                                                              jobject,
                                                              jlong);

/*
 * Class:     cvc5_Sort
 * Method:    isSortConstructor
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isSortConstructor(JNIEnv*,
                                                            jobject,
                                                            jlong);

/*
 * Class:     cvc5_Sort
 * Method:    isFirstClass
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isFirstClass(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Sort
 * Method:    isFunctionLike
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isFunctionLike(JNIEnv*,
                                                         jobject,
                                                         jlong);

/*
 * Class:     cvc5_Sort
 * Method:    isSubsortOf
 * Signature: (JJ)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isSubsortOf(JNIEnv*,
                                                      jobject,
                                                      jlong,
                                                      jlong);

/*
 * Class:     cvc5_Sort
 * Method:    isComparableTo
 * Signature: (JJ)Z
 */
JNIEXPORT jboolean JNICALL Java_cvc5_Sort_isComparableTo(JNIEnv*,
                                                         jobject,
                                                         jlong,
                                                         jlong);

/*
 * Class:     cvc5_Sort
 * Method:    getDatatype
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Sort_getDatatype(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Sort
 * Method:    instantiate
 * Signature: (J[J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Sort_instantiate(JNIEnv*,
                                                   jobject,
                                                   jlong,
                                                   jlongArray);

/*
 * Class:     cvc5_Sort
 * Method:    substitute
 * Signature: (JJJ)J
 */
JNIEXPORT jlong JNICALL
Java_cvc5_Sort_substitute__JJJ(JNIEnv*, jobject, jlong, jlong, jlong);

/*
 * Class:     cvc5_Sort
 * Method:    substitute
 * Signature: (J[J[J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Sort_substitute__J_3J_3J(
    JNIEnv*, jobject, jlong, jlongArray, jlongArray);

/*
 * Class:     cvc5_Sort
 * Method:    toString
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_cvc5_Sort_toString(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Sort
 * Method:    getConstructorArity
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_cvc5_Sort_getConstructorArity(JNIEnv*,
                                                          jobject,
                                                          jlong);

/*
 * Class:     cvc5_Sort
 * Method:    getConstructorDomainSorts
 * Signature: (J)[J
 */
JNIEXPORT jlongArray JNICALL Java_cvc5_Sort_getConstructorDomainSorts(JNIEnv*,
                                                                      jobject,
                                                                      jlong);

/*
 * Class:     cvc5_Sort
 * Method:    getConstructorCodomainSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Sort_getConstructorCodomainSort(JNIEnv*,
                                                                  jobject,
                                                                  jlong);

/*
 * Class:     cvc5_Sort
 * Method:    getSelectorDomainSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Sort_getSelectorDomainSort(JNIEnv*,
                                                             jobject,
                                                             jlong);

/*
 * Class:     cvc5_Sort
 * Method:    getSelectorCodomainSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Sort_getSelectorCodomainSort(JNIEnv*,
                                                               jobject,
                                                               jlong);

/*
 * Class:     cvc5_Sort
 * Method:    getTesterDomainSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Sort_getTesterDomainSort(JNIEnv*,
                                                           jobject,
                                                           jlong);

/*
 * Class:     cvc5_Sort
 * Method:    getTesterCodomainSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Sort_getTesterCodomainSort(JNIEnv*,
                                                             jobject,
                                                             jlong);

/*
 * Class:     cvc5_Sort
 * Method:    getFunctionArity
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_cvc5_Sort_getFunctionArity(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Sort
 * Method:    getFunctionDomainSorts
 * Signature: (J)[J
 */
JNIEXPORT jlongArray JNICALL Java_cvc5_Sort_getFunctionDomainSorts(JNIEnv*,
                                                                   jobject,
                                                                   jlong);

/*
 * Class:     cvc5_Sort
 * Method:    getFunctionCodomainSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Sort_getFunctionCodomainSort(JNIEnv*,
                                                               jobject,
                                                               jlong);

/*
 * Class:     cvc5_Sort
 * Method:    getArrayIndexSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Sort_getArrayIndexSort(JNIEnv*,
                                                         jobject,
                                                         jlong);

/*
 * Class:     cvc5_Sort
 * Method:    getArrayElementSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Sort_getArrayElementSort(JNIEnv*,
                                                           jobject,
                                                           jlong);

/*
 * Class:     cvc5_Sort
 * Method:    getSetElementSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Sort_getSetElementSort(JNIEnv*,
                                                         jobject,
                                                         jlong);

/*
 * Class:     cvc5_Sort
 * Method:    getBagElementSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Sort_getBagElementSort(JNIEnv*,
                                                         jobject,
                                                         jlong);

/*
 * Class:     cvc5_Sort
 * Method:    getSequenceElementSort
 * Signature: (J)J
 */
JNIEXPORT jlong JNICALL Java_cvc5_Sort_getSequenceElementSort(JNIEnv*,
                                                              jobject,
                                                              jlong);

/*
 * Class:     cvc5_Sort
 * Method:    getUninterpretedSortName
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_cvc5_Sort_getUninterpretedSortName(JNIEnv*,
                                                                  jobject,
                                                                  jlong);

/*
 * Class:     cvc5_Sort
 * Method:    isUninterpretedSortParameterized
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL
Java_cvc5_Sort_isUninterpretedSortParameterized(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Sort
 * Method:    getUninterpretedSortParamSorts
 * Signature: (J)[J
 */
JNIEXPORT jlongArray JNICALL
Java_cvc5_Sort_getUninterpretedSortParamSorts(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Sort
 * Method:    getSortConstructorName
 * Signature: (J)Ljava/lang/String;
 */
JNIEXPORT jstring JNICALL Java_cvc5_Sort_getSortConstructorName(JNIEnv*,
                                                                jobject,
                                                                jlong);

/*
 * Class:     cvc5_Sort
 * Method:    getSortConstructorArity
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_cvc5_Sort_getSortConstructorArity(JNIEnv*,
                                                              jobject,
                                                              jlong);

/*
 * Class:     cvc5_Sort
 * Method:    getBVSize
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_cvc5_Sort_getBVSize(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Sort
 * Method:    getFPExponentSize
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_cvc5_Sort_getFPExponentSize(JNIEnv*,
                                                        jobject,
                                                        jlong);

/*
 * Class:     cvc5_Sort
 * Method:    getFPSignificandSize
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_cvc5_Sort_getFPSignificandSize(JNIEnv*,
                                                           jobject,
                                                           jlong);

/*
 * Class:     cvc5_Sort
 * Method:    getDatatypeParamSorts
 * Signature: (J)[J
 */
JNIEXPORT jlongArray JNICALL Java_cvc5_Sort_getDatatypeParamSorts(JNIEnv*,
                                                                  jobject,
                                                                  jlong);

/*
 * Class:     cvc5_Sort
 * Method:    getDatatypeArity
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_cvc5_Sort_getDatatypeArity(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Sort
 * Method:    getTupleLength
 * Signature: (J)I
 */
JNIEXPORT jint JNICALL Java_cvc5_Sort_getTupleLength(JNIEnv*, jobject, jlong);

/*
 * Class:     cvc5_Sort
 * Method:    getTupleSorts
 * Signature: (J)[J
 */
JNIEXPORT jlongArray JNICALL Java_cvc5_Sort_getTupleSorts(JNIEnv*,
                                                          jobject,
                                                          jlong);
