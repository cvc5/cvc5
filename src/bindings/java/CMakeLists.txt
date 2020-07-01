find_package(Java REQUIRED)
find_package(JNI REQUIRED)
include(UseJava)

include_directories(${JNI_INCLUDE_DIRS})

set(SWIG_MODULE_cvc4jni_EXTRA_DEPS cvc4 cvc4parser)
set_property(SOURCE ${CVC4_SWIG_INTERFACE} PROPERTY CPLUSPLUS ON)
set(CMAKE_SWIG_FLAGS -package edu.stanford.CVC4)

if(${CMAKE_VERSION} VERSION_LESS "3.8.0")
  swig_add_module(cvc4jni Java ${CVC4_SWIG_INTERFACE})
else()
  swig_add_library(cvc4jni LANGUAGE Java SOURCES ${CVC4_SWIG_INTERFACE})
endif()
swig_link_libraries(cvc4jni cvc4 cvc4parser ${JNI_LIBRARIRES})

# Create CVC4.jar from all generated *.java files.
set(gen_java_files
  ${CMAKE_CURRENT_BINARY_DIR}/ArrayStoreAll.java
  ${CMAKE_CURRENT_BINARY_DIR}/ArrayStoreAllHashFunction.java
  ${CMAKE_CURRENT_BINARY_DIR}/ArrayType.java
  ${CMAKE_CURRENT_BINARY_DIR}/AscriptionType.java
  ${CMAKE_CURRENT_BINARY_DIR}/AscriptionTypeHashFunction.java
  ${CMAKE_CURRENT_BINARY_DIR}/BitVector.java
  ${CMAKE_CURRENT_BINARY_DIR}/BitVectorBitOf.java
  ${CMAKE_CURRENT_BINARY_DIR}/BitVectorBitOfHashFunction.java
  ${CMAKE_CURRENT_BINARY_DIR}/BitVectorExtract.java
  ${CMAKE_CURRENT_BINARY_DIR}/BitVectorExtractHashFunction.java
  ${CMAKE_CURRENT_BINARY_DIR}/BitVectorHashFunction.java
  ${CMAKE_CURRENT_BINARY_DIR}/BitVectorRepeat.java
  ${CMAKE_CURRENT_BINARY_DIR}/BitVectorRotateLeft.java
  ${CMAKE_CURRENT_BINARY_DIR}/BitVectorRotateRight.java
  ${CMAKE_CURRENT_BINARY_DIR}/BitVectorSignExtend.java
  ${CMAKE_CURRENT_BINARY_DIR}/BitVectorSize.java
  ${CMAKE_CURRENT_BINARY_DIR}/BitVectorType.java
  ${CMAKE_CURRENT_BINARY_DIR}/BitVectorZeroExtend.java
  ${CMAKE_CURRENT_BINARY_DIR}/BoolHashFunction.java
  ${CMAKE_CURRENT_BINARY_DIR}/BooleanType.java
  ${CMAKE_CURRENT_BINARY_DIR}/CVC4.java
  ${CMAKE_CURRENT_BINARY_DIR}/CVC4IllegalArgumentException.java
  ${CMAKE_CURRENT_BINARY_DIR}/CVC4JNI.java
  ${CMAKE_CURRENT_BINARY_DIR}/CVC4String.java
  ${CMAKE_CURRENT_BINARY_DIR}/CVC4StringHashFunction.java
  ${CMAKE_CURRENT_BINARY_DIR}/Cardinality.java
  ${CMAKE_CURRENT_BINARY_DIR}/CardinalityBeth.java
  ${CMAKE_CURRENT_BINARY_DIR}/CardinalityUnknown.java
  ${CMAKE_CURRENT_BINARY_DIR}/Configuration.java
  ${CMAKE_CURRENT_BINARY_DIR}/ConstructorType.java
  ${CMAKE_CURRENT_BINARY_DIR}/Datatype.java
  ${CMAKE_CURRENT_BINARY_DIR}/DatatypeConstructor.java
  ${CMAKE_CURRENT_BINARY_DIR}/DatatypeConstructorArg.java
  ${CMAKE_CURRENT_BINARY_DIR}/DatatypeHashFunction.java
  ${CMAKE_CURRENT_BINARY_DIR}/DatatypeIndexConstant.java
  ${CMAKE_CURRENT_BINARY_DIR}/DatatypeIndexConstantHashFunction.java
  ${CMAKE_CURRENT_BINARY_DIR}/DatatypeResolutionException.java
  ${CMAKE_CURRENT_BINARY_DIR}/DatatypeSelfType.java
  ${CMAKE_CURRENT_BINARY_DIR}/DatatypeType.java
  ${CMAKE_CURRENT_BINARY_DIR}/DatatypeUnresolvedType.java
  ${CMAKE_CURRENT_BINARY_DIR}/EmptySet.java
  ${CMAKE_CURRENT_BINARY_DIR}/EmptySetHashFunction.java
  ${CMAKE_CURRENT_BINARY_DIR}/Exception.java
  ${CMAKE_CURRENT_BINARY_DIR}/ExportUnsupportedException.java
  ${CMAKE_CURRENT_BINARY_DIR}/Expr.java
  ${CMAKE_CURRENT_BINARY_DIR}/ExprHashFunction.java
  ${CMAKE_CURRENT_BINARY_DIR}/ExprManager.java
  ${CMAKE_CURRENT_BINARY_DIR}/ExprManagerMapCollection.java
  ${CMAKE_CURRENT_BINARY_DIR}/ExprSequence.java
  ${CMAKE_CURRENT_BINARY_DIR}/FloatingPoint.java
  ${CMAKE_CURRENT_BINARY_DIR}/FloatingPointConvertSort.java
  ${CMAKE_CURRENT_BINARY_DIR}/FloatingPointSize.java
  ${CMAKE_CURRENT_BINARY_DIR}/FloatingPointToBV.java
  ${CMAKE_CURRENT_BINARY_DIR}/FloatingPointToFPFloatingPoint.java
  ${CMAKE_CURRENT_BINARY_DIR}/FloatingPointToFPGeneric.java
  ${CMAKE_CURRENT_BINARY_DIR}/FloatingPointToFPIEEEBitVector.java
  ${CMAKE_CURRENT_BINARY_DIR}/FloatingPointToFPReal.java
  ${CMAKE_CURRENT_BINARY_DIR}/FloatingPointToFPSignedBitVector.java
  ${CMAKE_CURRENT_BINARY_DIR}/FloatingPointToFPUnsignedBitVector.java
  ${CMAKE_CURRENT_BINARY_DIR}/FloatingPointToSBV.java
  ${CMAKE_CURRENT_BINARY_DIR}/FloatingPointToUBV.java
  ${CMAKE_CURRENT_BINARY_DIR}/FloatingPointType.java
  ${CMAKE_CURRENT_BINARY_DIR}/FunctionType.java
  ${CMAKE_CURRENT_BINARY_DIR}/InputLanguage.java
  ${CMAKE_CURRENT_BINARY_DIR}/IntAnd.java
  ${CMAKE_CURRENT_BINARY_DIR}/IntToBitVector.java
  ${CMAKE_CURRENT_BINARY_DIR}/Integer.java
  ${CMAKE_CURRENT_BINARY_DIR}/IntegerHashFunction.java
  ${CMAKE_CURRENT_BINARY_DIR}/IntegerType.java
  ${CMAKE_CURRENT_BINARY_DIR}/JavaInputStreamAdapter.java
  ${CMAKE_CURRENT_BINARY_DIR}/JavaIteratorAdapter_Datatype.java
  ${CMAKE_CURRENT_BINARY_DIR}/JavaIteratorAdapter_DatatypeConstructor.java
  ${CMAKE_CURRENT_BINARY_DIR}/JavaIteratorAdapter_Expr.java
  ${CMAKE_CURRENT_BINARY_DIR}/JavaIteratorAdapter_StatisticsBase.java
  ${CMAKE_CURRENT_BINARY_DIR}/JavaIteratorAdapter_UnsatCore.java
  ${CMAKE_CURRENT_BINARY_DIR}/JavaOutputStreamAdapter.java
  ${CMAKE_CURRENT_BINARY_DIR}/Kind.java
  ${CMAKE_CURRENT_BINARY_DIR}/KindHashFunction.java
  ${CMAKE_CURRENT_BINARY_DIR}/LastExceptionBuffer.java
  ${CMAKE_CURRENT_BINARY_DIR}/LogicException.java
  ${CMAKE_CURRENT_BINARY_DIR}/LogicInfo.java
  ${CMAKE_CURRENT_BINARY_DIR}/ModalException.java
  ${CMAKE_CURRENT_BINARY_DIR}/OptionException.java
  ${CMAKE_CURRENT_BINARY_DIR}/Options.java
  ${CMAKE_CURRENT_BINARY_DIR}/OutputLanguage.java
  ${CMAKE_CURRENT_BINARY_DIR}/PrettySExprs.java
  ${CMAKE_CURRENT_BINARY_DIR}/Proof.java
  ${CMAKE_CURRENT_BINARY_DIR}/Rational.java
  ${CMAKE_CURRENT_BINARY_DIR}/RationalHashFunction.java
  ${CMAKE_CURRENT_BINARY_DIR}/RealType.java
  ${CMAKE_CURRENT_BINARY_DIR}/RecoverableModalException.java
  ${CMAKE_CURRENT_BINARY_DIR}/RegExpLoop.java
  ${CMAKE_CURRENT_BINARY_DIR}/RegExpRepeat.java
  ${CMAKE_CURRENT_BINARY_DIR}/RegExpType.java
  ${CMAKE_CURRENT_BINARY_DIR}/Result.java
  ${CMAKE_CURRENT_BINARY_DIR}/RoundingMode.java
  ${CMAKE_CURRENT_BINARY_DIR}/RoundingModeType.java
  ${CMAKE_CURRENT_BINARY_DIR}/SExpr.java
  ${CMAKE_CURRENT_BINARY_DIR}/SExprKeyword.java
  ${CMAKE_CURRENT_BINARY_DIR}/SExprType.java
  ${CMAKE_CURRENT_BINARY_DIR}/SWIGTYPE_p_CVC4__Model.java
  ${CMAKE_CURRENT_BINARY_DIR}/SWIGTYPE_p_CVC4__options__InstFormatMode.java
  ${CMAKE_CURRENT_BINARY_DIR}/SWIGTYPE_p_MaybeT_CVC4__Rational_t.java
  ${CMAKE_CURRENT_BINARY_DIR}/SWIGTYPE_p_Type.java
  ${CMAKE_CURRENT_BINARY_DIR}/SWIGTYPE_p_std__istream.java
  ${CMAKE_CURRENT_BINARY_DIR}/SWIGTYPE_p_std__ostream.java
  ${CMAKE_CURRENT_BINARY_DIR}/SWIGTYPE_p_std__shared_ptrT_CVC4__SygusPrintCallback_t.java
  ${CMAKE_CURRENT_BINARY_DIR}/SWIGTYPE_p_std__string.java
  ${CMAKE_CURRENT_BINARY_DIR}/SWIGTYPE_p_std__vectorT_CVC4__DatatypeConstructorArg_t.java
  ${CMAKE_CURRENT_BINARY_DIR}/SWIGTYPE_p_std__vectorT_std__pairT_CVC4__Expr_CVC4__Expr_t_t.java
  ${CMAKE_CURRENT_BINARY_DIR}/SWIGTYPE_p_std__vectorT_std__vectorT_std__string_t_t.java
  ${CMAKE_CURRENT_BINARY_DIR}/SelectorType.java
  ${CMAKE_CURRENT_BINARY_DIR}/SequenceType.java
  ${CMAKE_CURRENT_BINARY_DIR}/SetType.java
  ${CMAKE_CURRENT_BINARY_DIR}/SmtEngine.java
  ${CMAKE_CURRENT_BINARY_DIR}/SortConstructorType.java
  ${CMAKE_CURRENT_BINARY_DIR}/SortType.java
  ${CMAKE_CURRENT_BINARY_DIR}/Statistic.java
  ${CMAKE_CURRENT_BINARY_DIR}/Statistics.java
  ${CMAKE_CURRENT_BINARY_DIR}/StatisticsBase.java
  ${CMAKE_CURRENT_BINARY_DIR}/StringType.java
  ${CMAKE_CURRENT_BINARY_DIR}/TesterType.java
  ${CMAKE_CURRENT_BINARY_DIR}/TheoryId.java
  ${CMAKE_CURRENT_BINARY_DIR}/TupleUpdate.java
  ${CMAKE_CURRENT_BINARY_DIR}/TupleUpdateHashFunction.java
  ${CMAKE_CURRENT_BINARY_DIR}/Type.java
  ${CMAKE_CURRENT_BINARY_DIR}/TypeCheckingException.java
  ${CMAKE_CURRENT_BINARY_DIR}/TypeConstant.java
  ${CMAKE_CURRENT_BINARY_DIR}/TypeConstantHashFunction.java
  ${CMAKE_CURRENT_BINARY_DIR}/TypeHashFunction.java
  ${CMAKE_CURRENT_BINARY_DIR}/UninterpretedConstant.java
  ${CMAKE_CURRENT_BINARY_DIR}/UninterpretedConstantHashFunction.java
  ${CMAKE_CURRENT_BINARY_DIR}/UnrecognizedOptionException.java
  ${CMAKE_CURRENT_BINARY_DIR}/UnsafeInterruptException.java
  ${CMAKE_CURRENT_BINARY_DIR}/UnsatCore.java
  ${CMAKE_CURRENT_BINARY_DIR}/VariableTypeMap.java
  ${CMAKE_CURRENT_BINARY_DIR}/setOfType.java
  ${CMAKE_CURRENT_BINARY_DIR}/vectorDatatype.java
  ${CMAKE_CURRENT_BINARY_DIR}/vectorDatatypeType.java
  ${CMAKE_CURRENT_BINARY_DIR}/vectorExpr.java
  ${CMAKE_CURRENT_BINARY_DIR}/vectorSExpr.java
  ${CMAKE_CURRENT_BINARY_DIR}/vectorString.java
  ${CMAKE_CURRENT_BINARY_DIR}/vectorType.java
  ${CMAKE_CURRENT_BINARY_DIR}/vectorUnsignedInt.java
  ${CMAKE_CURRENT_BINARY_DIR}/vectorVectorExpr.java
)

if(CVC4_USE_CLN_IMP)
  list(APPEND gen_java_files
    ${CMAKE_CURRENT_BINARY_DIR}/SWIGTYPE_p_cln__cl_I.java
    ${CMAKE_CURRENT_BINARY_DIR}/SWIGTYPE_p_cln__cl_RA.java
  )
elseif(CVC4_USE_GMP_IMP)
  list(APPEND gen_java_files
    ${CMAKE_CURRENT_BINARY_DIR}/SWIGTYPE_p_mpq_class.java
    ${CMAKE_CURRENT_BINARY_DIR}/SWIGTYPE_p_mpz_class.java
  )
endif()

set(CMAKE_JNI_TARGET TRUE)
add_jar(cvc4jar
        SOURCES ${gen_java_files}
        VERSION ${CVC4_MAJOR}.${CVC4_MINOR}.${CVC4_RELEASE}
        OUTPUT_NAME CVC4)
add_dependencies(cvc4jar cvc4jni)
install_jar(cvc4jar DESTINATION share/java/cvc4)
install_jni_symlink(cvc4jar DESTINATION share/java/cvc4)
install(TARGETS cvc4jni
  EXPORT cvc4-targets
  DESTINATION ${LIBRARY_INSTALL_DIR})

install_jar_exports(
  TARGETS cvc4jar
  NAMESPACE CVC4::
  FILE CVC4JavaTargets.cmake
  DESTINATION ${LIBRARY_INSTALL_DIR}/cmake/CVC4
)
