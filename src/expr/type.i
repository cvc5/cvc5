%{
#include "expr/type.h"
%}

%ignore CVC4::expr::exportTypeInternal(TypeNode n, NodeManager* from, NodeManager* nm, ExprManagerMapCollection& vmap);

%ignore CVC4::Type::Type(const Type&);
%ignore CVC4::Type::operator=(const Type&);
%ignore CVC4::Type::operator!=(const Type&) const;
%rename(equals) CVC4::Type::operator==(const Type&) const;
%rename(less) CVC4::Type::operator<(const Type&) const;
%rename(lessEqual) CVC4::Type::operator<=(const Type&) const;
%rename(greater) CVC4::Type::operator>(const Type&) const;
%rename(greaterEqual) CVC4::Type::operator>=(const Type&) const;

%ignore CVC4::BitVectorType::BitVectorType();
%ignore CVC4::BitVectorType::BitVectorType(const Type&);

%ignore CVC4::BooleanType::BooleanType();
%ignore CVC4::BooleanType::BooleanType(const Type&);

%ignore CVC4::ConstructorType::ConstructorType();
%ignore CVC4::ConstructorType::ConstructorType(const Type&);

%ignore CVC4::FloatingPointType::FloatingPointType();
%ignore CVC4::FloatingPointType::FloatingPointType(const Type&);

%ignore CVC4::DatatypeType::DatatypeType();
%ignore CVC4::DatatypeType::DatatypeType(const Type&);
%ignore CVC4::DatatypeType::getRecord() const;

%ignore CVC4::FunctionType::FunctionType();
%ignore CVC4::FunctionType::FunctionType(const Type&);

%ignore CVC4::IntegerType::IntegerType();
%ignore CVC4::IntegerType::IntegerType(const Type&);

%ignore CVC4::RealType::RealType();
%ignore CVC4::RealType::RealType(const Type&);

%ignore CVC4::RegExpType::RegExpType();
%ignore CVC4::RegExpType::RegExpType(const Type&);

%ignore CVC4::RoundingModeType::RoundingModeType();
%ignore CVC4::RoundingModeType::RoundingModeType(const Type&);

%ignore CVC4::SelectorType::SelectorType();
%ignore CVC4::SelectorType::SelectorType(const Type&);

%ignore CVC4::SequenceType::SequenceType();
%ignore CVC4::SequenceType::SequenceType(const Type&);

%ignore CVC4::SExprType::SExprType();
%ignore CVC4::SExprType::SExprType(const Type&);

%ignore CVC4::SortType::SortType();
%ignore CVC4::SortType::SortType(const Type&);

%ignore CVC4::SortConstructorType::SortConstructorType();
%ignore CVC4::SortConstructorType::SortConstructorType(const Type&);

%ignore CVC4::StringType::StringType();
%ignore CVC4::StringType::StringType(const Type&);

%ignore CVC4::TesterType::TesterType();
%ignore CVC4::TesterType::TesterType(const Type&);

%ignore CVC4::ArrayType::ArrayType();
%ignore CVC4::ArrayType::ArrayType(const Type&);

%ignore CVC4::SetType::SetType();
%ignore CVC4::SetType::SetType(const Type&);

%ignore CVC4::operator<<(std::ostream&, const Type&);

#ifdef SWIGPYTHON
%rename(doApply) CVC4::TypeHashFunction::operator()(const CVC4::Type&) const;
#else /* SWIGPYTHON */
%rename(apply) CVC4::TypeHashFunction::operator()(const CVC4::Type&) const;
#endif /* SWIGPYTHON */

#ifdef SWIGJAVA

%include "bindings/java/cvc4_std_vector.i"

%typemap(javaout) CVC4::Expr {
  return new Expr(this.em, $jnicall, true);
}

%typemap(javaout) std::vector<CVC4::Type> {
  return new vectorType(this.em, $jnicall, true);
}

%typemap(javabody) CVC4::Type %{
  private long swigCPtr;
  protected boolean swigCMemOwn;
  // Prevent ExprManager from being garbage collected before this instance
  protected ExprManager em;

  protected $javaclassname(ExprManager em, long cPtr, boolean cMemoryOwn) {
    swigCMemOwn = cMemoryOwn;
    swigCPtr = cPtr;
    this.em = em;
  }

  protected static long getCPtr($javaclassname obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }
%}

// Workaround for https://github.com/swig/swig/commit/63a5a8af88271559a7b170794b4c61c30b8934ea
%typemap(javaconstruct) Type {
  this(null, $imcall, true);
}

%typemap(javaconstruct) CVC4::Type {
  this(null, $imcall, true);
}


%typemap(javaout) CVC4::Type {
  return new Type(this.em, $jnicall, true);
}

SWIG_STD_VECTOR_EM(CVC4::Type, const CVC4::Type&)

%typemap(javaout) CVC4::Type {
  return new Type(this.em, $jnicall, true);
}
%typemap(javaout) const CVC4::Type& {
  return new Type(this.em, $jnicall, false);
}
%template(vectorType) std::vector<CVC4::Type>;

%typemap(javabody_derived) CVC4::BitVectorType %{
  private transient long swigCPtr;

  protected $javaclassname(ExprManager em, long cPtr, boolean cMemoryOwn) {
    super(em, CVC4JNI.$javaclassname_SWIGUpcast(cPtr), cMemoryOwn);
    swigCPtr = cPtr;
    swigCMemOwn = cMemoryOwn;
  }

  protected static long getCPtr($javaclassname obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }
%}

%typemap(javabody_derived) CVC4::BooleanType %{
  private transient long swigCPtr;

  protected $javaclassname(ExprManager em, long cPtr, boolean cMemoryOwn) {
    super(em, CVC4JNI.$javaclassname_SWIGUpcast(cPtr), cMemoryOwn);
    swigCPtr = cPtr;
    swigCMemOwn = cMemoryOwn;
  }

  protected static long getCPtr($javaclassname obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }
%}

%typemap(javabody_derived) CVC4::ConstructorType %{
  private transient long swigCPtr;

  protected $javaclassname(ExprManager em, long cPtr, boolean cMemoryOwn) {
    super(em, CVC4JNI.$javaclassname_SWIGUpcast(cPtr), cMemoryOwn);
    swigCPtr = cPtr;
    swigCMemOwn = cMemoryOwn;
  }

  protected static long getCPtr($javaclassname obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }
%}

%typemap(javabody_derived) CVC4::FloatingPointType %{
  private transient long swigCPtr;

  protected $javaclassname(ExprManager em, long cPtr, boolean cMemoryOwn) {
    super(em, CVC4JNI.$javaclassname_SWIGUpcast(cPtr), cMemoryOwn);
    swigCPtr = cPtr;
    swigCMemOwn = cMemoryOwn;
  }

  protected static long getCPtr($javaclassname obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }
%}

%typemap(javabody_derived) CVC4::DatatypeType %{
  private transient long swigCPtr;

  protected $javaclassname(ExprManager em, long cPtr, boolean cMemoryOwn) {
    super(em, CVC4JNI.$javaclassname_SWIGUpcast(cPtr), cMemoryOwn);
    swigCPtr = cPtr;
    swigCMemOwn = cMemoryOwn;
  }

  protected static long getCPtr($javaclassname obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }
%}

SWIG_STD_VECTOR_EM(CVC4::DatatypeType, const CVC4::DatatypeType&)

%typemap(javaout) CVC4::DatatypeType {
  return new DatatypeType(this.em, $jnicall, true);
}
%typemap(javaout) const CVC4::DatatypeType& {
  return new DatatypeType(this.em, $jnicall, false);
}
%template(vectorDatatypeType) std::vector<CVC4::DatatypeType>;

%typemap(javabody_derived) CVC4::FunctionType %{
  private transient long swigCPtr;

  protected $javaclassname(ExprManager em, long cPtr, boolean cMemoryOwn) {
    super(em, CVC4JNI.$javaclassname_SWIGUpcast(cPtr), cMemoryOwn);
    swigCPtr = cPtr;
    swigCMemOwn = cMemoryOwn;
  }

  protected static long getCPtr($javaclassname obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }
%}

%typemap(javabody_derived) CVC4::IntegerType %{
  private transient long swigCPtr;

  protected $javaclassname(ExprManager em, long cPtr, boolean cMemoryOwn) {
    super(em, CVC4JNI.$javaclassname_SWIGUpcast(cPtr), cMemoryOwn);
    swigCPtr = cPtr;
    swigCMemOwn = cMemoryOwn;
  }

  protected static long getCPtr($javaclassname obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }
%}

%typemap(javabody_derived) CVC4::RealType %{
  private transient long swigCPtr;

  protected $javaclassname(ExprManager em, long cPtr, boolean cMemoryOwn) {
    super(em, CVC4JNI.$javaclassname_SWIGUpcast(cPtr), cMemoryOwn);
    swigCPtr = cPtr;
    swigCMemOwn = cMemoryOwn;
  }

  protected static long getCPtr($javaclassname obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }
%}

%typemap(javabody_derived) CVC4::RegExpType %{
  private transient long swigCPtr;

  protected $javaclassname(ExprManager em, long cPtr, boolean cMemoryOwn) {
    super(em, CVC4JNI.$javaclassname_SWIGUpcast(cPtr), cMemoryOwn);
    swigCPtr = cPtr;
    swigCMemOwn = cMemoryOwn;
  }

  protected static long getCPtr($javaclassname obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }
%}

%typemap(javabody_derived) CVC4::RoundingModeType %{
  private transient long swigCPtr;

  protected $javaclassname(ExprManager em, long cPtr, boolean cMemoryOwn) {
    super(em, CVC4JNI.$javaclassname_SWIGUpcast(cPtr), cMemoryOwn);
    swigCPtr = cPtr;
    swigCMemOwn = cMemoryOwn;
  }

  protected static long getCPtr($javaclassname obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }
%}

%typemap(javabody_derived) CVC4::SelectorType %{
  private transient long swigCPtr;

  protected $javaclassname(ExprManager em, long cPtr, boolean cMemoryOwn) {
    super(em, CVC4JNI.$javaclassname_SWIGUpcast(cPtr), cMemoryOwn);
    swigCPtr = cPtr;
    swigCMemOwn = cMemoryOwn;
  }

  protected static long getCPtr($javaclassname obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }
%}

%typemap(javabody_derived) CVC4::SequenceType %{
  private transient long swigCPtr;

  protected $javaclassname(ExprManager em, long cPtr, boolean cMemoryOwn) {
    super(em, CVC4JNI.$javaclassname_SWIGUpcast(cPtr), cMemoryOwn);
    swigCPtr = cPtr;
    swigCMemOwn = cMemoryOwn;
  }

  protected static long getCPtr($javaclassname obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }
%}

%typemap(javabody_derived) CVC4::SExprType %{
  private transient long swigCPtr;

  protected $javaclassname(ExprManager em, long cPtr, boolean cMemoryOwn) {
    super(em, CVC4JNI.$javaclassname_SWIGUpcast(cPtr), cMemoryOwn);
    swigCPtr = cPtr;
    swigCMemOwn = cMemoryOwn;
  }

  protected static long getCPtr($javaclassname obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }
%}

%typemap(javabody_derived) CVC4::SortType %{
  private transient long swigCPtr;

  protected $javaclassname(ExprManager em, long cPtr, boolean cMemoryOwn) {
    super(em, CVC4JNI.$javaclassname_SWIGUpcast(cPtr), cMemoryOwn);
    swigCPtr = cPtr;
    swigCMemOwn = cMemoryOwn;
  }

  protected static long getCPtr($javaclassname obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }
%}

%typemap(javabody_derived) CVC4::SortConstructorType %{
  private transient long swigCPtr;

  protected $javaclassname(ExprManager em, long cPtr, boolean cMemoryOwn) {
    super(em, CVC4JNI.$javaclassname_SWIGUpcast(cPtr), cMemoryOwn);
    swigCPtr = cPtr;
    swigCMemOwn = cMemoryOwn;
  }

  protected static long getCPtr($javaclassname obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }
%}

%typemap(javabody_derived) CVC4::StringType %{
  private transient long swigCPtr;

  protected $javaclassname(ExprManager em, long cPtr, boolean cMemoryOwn) {
    super(em, CVC4JNI.$javaclassname_SWIGUpcast(cPtr), cMemoryOwn);
    swigCPtr = cPtr;
    swigCMemOwn = cMemoryOwn;
  }

  protected static long getCPtr($javaclassname obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }
%}

%typemap(javabody_derived) CVC4::TesterType %{
  private transient long swigCPtr;

  protected $javaclassname(ExprManager em, long cPtr, boolean cMemoryOwn) {
    super(em, CVC4JNI.$javaclassname_SWIGUpcast(cPtr), cMemoryOwn);
    swigCPtr = cPtr;
    swigCMemOwn = cMemoryOwn;
  }

  protected static long getCPtr($javaclassname obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }
%}

%typemap(javabody_derived) CVC4::ArrayType %{
  private transient long swigCPtr;

  protected $javaclassname(ExprManager em, long cPtr, boolean cMemoryOwn) {
    super(em, CVC4JNI.$javaclassname_SWIGUpcast(cPtr), cMemoryOwn);
    swigCPtr = cPtr;
    swigCMemOwn = cMemoryOwn;
  }

  protected static long getCPtr($javaclassname obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }
%}

%typemap(javabody_derived) CVC4::SetType %{
  private transient long swigCPtr;

  protected $javaclassname(ExprManager em, long cPtr, boolean cMemoryOwn) {
    super(em, CVC4JNI.$javaclassname_SWIGUpcast(cPtr), cMemoryOwn);
    swigCMemOwn = cMemoryOwn;
    swigCPtr = cPtr;
  }

  protected static long getCPtr($javaclassname obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }
%}

%typemap(javaout) CVC4::SetType {
  return new SetType(this.em, $jnicall, true);
}

%typemap(javaout) CVC4::BooleanType {
  return new BooleanType(this.em, $jnicall, true);
}

%typemap(javaout) const CVC4::Datatype& {
  return new Datatype(this.em, $jnicall, true);
}

%typemap(javaout) CVC4::DatatypeType {
  return new DatatypeType(this.em, $jnicall, true);
}

%typemap(javaout) CVC4::SortType {
  return new SortType(this.em, $jnicall, true);
}

%typemap(javaout) typeVector {
  return new typeVector(this.em, $jnicall, true);
}

#endif /* SWIGJAVA */

%include "expr/type.h"
