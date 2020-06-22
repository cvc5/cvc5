%{
#include "expr/datatype.h"
%}

%ignore CVC4::Datatype::setRecord();
%ignore CVC4::Datatype::isRecord() const;
%ignore CVC4::Datatype::getRecord() const;
%ignore CVC4::Datatype::operator!=(const Datatype&) const;
%ignore CVC4::Datatype::begin();
%ignore CVC4::Datatype::end();
%ignore CVC4::Datatype::begin() const;
%ignore CVC4::Datatype::end() const;
%ignore CVC4::Datatype::getConstructors() const;
%rename(equals) CVC4::Datatype::operator==(const Datatype&) const;
%rename(get) CVC4::Datatype::operator[](size_t) const;
%rename(get) CVC4::Datatype::operator[](std::string) const;

%ignore CVC4::SygusPrintCallback;

%rename(apply) CVC4::DatatypeHashFunction::operator()(const Datatype&) const;
%ignore CVC4::DatatypeHashFunction::operator()(const Datatype*) const;
%rename(apply) CVC4::DatatypeHashFunction::operator()(const DatatypeConstructor&) const;
%ignore CVC4::DatatypeHashFunction::operator()(const DatatypeConstructor*) const;

%ignore CVC4::DatatypeConstructor::DatatypeConstructor();
%ignore CVC4::DatatypeConstructor::begin();
%ignore CVC4::DatatypeConstructor::end();
%ignore CVC4::DatatypeConstructor::begin() const;
%ignore CVC4::DatatypeConstructor::end() const;
%rename(get) CVC4::DatatypeConstructor::operator[](size_t) const;
%rename(get) CVC4::DatatypeConstructor::operator[](std::string) const;

%ignore CVC4::operator<<(std::ostream&, const Datatype&);
%ignore CVC4::operator<<(std::ostream&, const DatatypeConstructor&);
%ignore CVC4::operator<<(std::ostream&, const DatatypeConstructorArg&);
%ignore CVC4::operator<<(std::ostream& out, const DatatypeIndexConstant& es);

%ignore CVC4::DatatypeConstructorIterator;
%ignore CVC4::DatatypeConstructorArgIterator;

%ignore CVC4::DatatypeIndexConstant::operator!=(const DatatypeIndexConstant&) const;
%rename(equals) CVC4::DatatypeIndexConstant::operator==(const DatatypeIndexConstant&) const;
%rename(less) CVC4::DatatypeIndexConstant::operator<(const DatatypeIndexConstant&) const;
%rename(lessEqual) CVC4::DatatypeIndexConstant::operator<=(const DatatypeIndexConstant&) const;
%rename(greater) CVC4::DatatypeIndexConstant::operator>(const DatatypeIndexConstant&) const;
%rename(greaterEqual) CVC4::DatatypeIndexConstant::operator>=(const DatatypeIndexConstant&) const;
%rename(apply) CVC4::DatatypeIndexConstantFunction::operator()(const DatatypeIndexConstant&) const;

#ifdef SWIGJAVA

%typemap(javaout) CVC4::Expr {
  return new Expr(this.em, $jnicall, true);
}

%typemap(javaout) CVC4::DatatypeType {
  return new DatatypeType(this.em, $jnicall, true);
}

%typemap(javabody) CVC4::Datatype %{
  private long swigCPtr;
  protected boolean swigCMemOwn;
  private ExprManager em;

  protected $javaclassname(ExprManager em, long cPtr, boolean cMemoryOwn) {
    swigCMemOwn = cMemoryOwn;
    swigCPtr = cPtr;
    this.em = em;
  }

  protected static long getCPtr($javaclassname obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }

  public static $javaclassname datatypeOf(Expr item) throws edu.stanford.CVC4.Exception {
    $javaclassname result = datatypeOfInternal(item);
    result.em = item.getExprManager();
    return result;
  }

  public JavaIteratorAdapter_Datatype iterator() {
    return new JavaIteratorAdapter_Datatype(this.em, this);
  }
%}

%javamethodmodifiers CVC4::Datatype::datatypeOf(Expr item) "private";
%rename(datatypeOfInternal) CVC4::Datatype::datatypeOf(Expr item);

%include "bindings/java/cvc4_std_vector.i"

SWIG_STD_VECTOR_EM(CVC4::Datatype, const CVC4::Datatype&)

%extend CVC4::Datatype {
%typemap(javaout) const CVC4::Datatype& {
  return new Datatype(null, $jnicall, false);
}
}

%typemap(javaout) CVC4::Datatype {
  return new Datatype(this.em, $jnicall, true);
}
%typemap(javaout) const CVC4::Datatype& {
  return new Datatype(this.em, $jnicall, false);
}
%template(vectorDatatype) std::vector<CVC4::Datatype>;

%typemap(javaout) typeVector {
  return new typeVector(this.em, $jnicall, true);
}

%typemap(javaout) const CVC4::DatatypeConstructor& {
  return new DatatypeConstructor(this.em, $jnicall, false);
}

%typemap(javabody) CVC4::DatatypeConstructor %{
  private long swigCPtr;
  protected boolean swigCMemOwn;
  private ExprManager em;

  protected $javaclassname(ExprManager em, long cPtr, boolean cMemoryOwn) {
    swigCMemOwn = cMemoryOwn;
    swigCPtr = cPtr;
    this.em = em;
  }

  protected static long getCPtr($javaclassname obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }

  public DatatypeConstructor(ExprManager em, String name) {
    this(name);
    this.em = em;
  }

  public DatatypeConstructor(ExprManager em, String name, long weight) {
    this(name, weight);
    this.em = em;
  }

  public JavaIteratorAdapter_DatatypeConstructor iterator() {
    return new JavaIteratorAdapter_DatatypeConstructor(this.em, this);
  }
%}

// Workaround for https://github.com/swig/swig/commit/63a5a8af88271559a7b170794b4c61c30b8934ea
%typemap(javaconstruct) DatatypeConstructor {
  this(null, $imcall, true);
}

%typemap(javaconstruct) CVC4::DatatypeConstructor {
  this(null, $imcall, true);
}

%javamethodmodifiers CVC4::DatatypeConstructor::DatatypeConstructor(std::string) "private";
%javamethodmodifiers CVC4::DatatypeConstructor::DatatypeConstructor(std::string, unsigned weight) "private";

%typemap(javaout) const CVC4::DatatypeConstructorArg& {
  return new DatatypeConstructorArg(this.em, $jnicall, false);
}

%typemap(javabody) CVC4::DatatypeConstructorArg %{
  private long swigCPtr;
  protected boolean swigCMemOwn;
  private ExprManager em;

  protected $javaclassname(ExprManager em, long cPtr, boolean cMemoryOwn) {
    swigCMemOwn = cMemoryOwn;
    swigCPtr = cPtr;
    this.em = em;
  }

  protected static long getCPtr($javaclassname obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }
%}

%typemap(javaout) CVC4::SelectorType {
  return new SelectorType(this.em, $jnicall, true);
}

%extend CVC4::Datatype {
  std::string toString() const {
    std::stringstream ss;
    ss << *$self;
    return ss.str();
  }
}
%extend CVC4::DatatypeConstructor {
  std::string toString() const {
    std::stringstream ss;
    ss << *$self;
    return ss.str();
  }
}
%extend CVC4::DatatypeConstructorArg {
  std::string toString() const {
    std::stringstream ss;
    ss << *$self;
    return ss.str();
  }
}

// Workaround for https://github.com/swig/swig/commit/63a5a8af88271559a7b170794b4c61c30b8934ea
%typemap(javaconstruct) Datatype {
  this(null, $imcall, true);
}

%typemap(javaconstruct) CVC4::Datatype {
  this(em, $imcall, true);
}

%typemap(javaout) CVC4::DatatypeConstructor {
  return new DatatypeConstructor(this.em, $jnicall, true);
}

%typemap(javaout) CVC4::DatatypeConstructorArg {
  return new DatatypeConstructorArg(this.em, $jnicall, true);
}

SWIG_JAVA_ITERATOR_ADAPTER(CVC4::Datatype, CVC4::DatatypeConstructor)
%template(JavaIteratorAdapter_Datatype) CVC4::JavaIteratorAdapter<CVC4::Datatype, CVC4::DatatypeConstructor>;
SWIG_JAVA_ITERATOR_ADAPTER(CVC4::DatatypeConstructor, CVC4::DatatypeConstructorArg)
%template(JavaIteratorAdapter_DatatypeConstructor) CVC4::JavaIteratorAdapter<CVC4::DatatypeConstructor, CVC4::DatatypeConstructorArg>;

#endif /* SWIGJAVA */

%include "expr/datatype.h"
