%{
#include "expr/expr_manager.h"
%}

%ignore CVC4::ExprManager::exportType(const Type& t, ExprManager* em, ExprManagerMapCollection& vmap);
%ignore CVC4::stats::getStatisticsRegistry(ExprManager*);
%ignore CVC4::ExprManager::getResourceManager();
%ignore CVC4::ExprManager::mkRecordType(const Record& rec);
%ignore CVC4::ExprManager::safeFlushStatistics(int fd) const;

#ifdef SWIGJAVA

%typemap(javaout) CVC4::Expr {
  return new Expr(this, $jnicall, true);
}

%typemap(javaout) CVC4::Type {
  return new Type(this, $jnicall, true);
}

%typemap(javaout) CVC4::ArrayType {
  return new ArrayType(this, $jnicall, true);
}

%typemap(javaout) CVC4::BitVectorType {
  return new BitVectorType(this, $jnicall, true);
}

%typemap(javaout) CVC4::BooleanType {
  return new BooleanType(this, $jnicall, true);
}

%typemap(javaout) CVC4::ConstructorType {
  return new ConstructorType(this, $jnicall, true);
}

%typemap(javaout) const CVC4::Datatype& {
  return new Datatype(this, $jnicall, false);
}

%typemap(javaout) CVC4::DatatypeType {
  return new DatatypeType(this, $jnicall, true);
}

%typemap(javaout) std::vector<CVC4::DatatypeType> {
  return new vectorDatatypeType(this, $jnicall, true);
}

%typemap(javaout) CVC4::FloatingPointType {
  return new FloatingPointType(this, $jnicall, true);
}

%typemap(javaout) CVC4::FunctionType {
  return new FunctionType(this, $jnicall, true);
}

%typemap(javaout) CVC4::SelectorType {
  return new SelectorType(this, $jnicall, true);
}

%typemap(javaout) CVC4::StringType {
  return new StringType(this, $jnicall, true);
}

%typemap(javaout) CVC4::RegExpType {
  return new RegExpType(this, $jnicall, true);
}

%typemap(javaout) CVC4::RealType {
  return new RealType(this, $jnicall, true);
}

%typemap(javaout) CVC4::SetType {
  return new SetType(this, $jnicall, true);
}

%typemap(javaout) CVC4::SExprType {
  return new SExprType(this, $jnicall, true);
}

%typemap(javaout) CVC4::SortType {
  return new SortType(this, $jnicall, true);
}

%typemap(javaout) CVC4::SortConstructorType {
  return new SortConstructorType(this, $jnicall, true);
}

%typemap(javaout) CVC4::TesterType {
  return new TesterType(this, $jnicall, true);
}

%typemap(javaout) CVC4::IntegerType {
  return new IntegerType(this, $jnicall, true);
}

%typemap(javaout) CVC4::RoundingModeType {
  return new RoundingModeType(this, $jnicall, true);
}

%javamethodmodifiers CVC4::ExprManager::exportType(const Type& t, ExprManager* em, ExprManagerMapCollection& vmap) "public";

#endif /* SWIGJAVA */

%include "expr/expr_manager.h"

%template(mkConst) CVC4::ExprManager::mkConst<CVC4::ArrayStoreAll>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::BitVectorSize>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::AscriptionType>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::BitVectorBitOf>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::BitVectorRepeat>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::BitVectorExtract>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::BitVectorRotateLeft>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::BitVectorSignExtend>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::BitVectorZeroExtend>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::BitVectorRotateRight>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::IntToBitVector>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::FloatingPoint>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::FloatingPointSize>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::FloatingPointToFPIEEEBitVector>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::FloatingPointToFPFloatingPoint>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::FloatingPointToFPReal>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::FloatingPointToFPSignedBitVector>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::FloatingPointToFPUnsignedBitVector>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::FloatingPointToFPGeneric>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::FloatingPointToUBV>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::FloatingPointToSBV>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::UninterpretedConstant>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::kind::Kind_t>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::DatatypeIndexConstant>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::TupleUpdate>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::Rational>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::BitVector>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::EmptySet>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::ExprSequence>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::String>;
#ifdef SWIGPYTHON
/* The python bindings cannot differentiate between bool and other basic
 * types like enum and int. Therefore, we rename mkConst for the bool
 * case into mkBoolConst.
*/
%template(mkBoolConst) CVC4::ExprManager::mkConst<bool>;
%template(mkRoundingMode) CVC4::ExprManager::mkConst<RoundingMode>;

// These cases have trouble too.  Remove them for now.
//%template(mkConst) CVC4::ExprManager::mkConst<CVC4::TypeConstant>;
#else
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::TypeConstant>;
%template(mkConst) CVC4::ExprManager::mkConst<bool>;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::RoundingMode>;
#endif
