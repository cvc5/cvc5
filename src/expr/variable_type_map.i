%{
#include "expr/variable_type_map.h"
%}

#if SWIGJAVA

%typemap(javabody) CVC4::VariableTypeMap %{
  private long swigCPtr;
  protected boolean swigCMemOwn;
  private ExprManager em;

  protected $javaclassname(ExprManager em, long cPtr, boolean cMemoryOwn) {
    swigCMemOwn = cMemoryOwn;
    swigCPtr = cPtr;
    this.em = em;
  }

  public VariableTypeMap(ExprManager em) {
    this();
    this.em = em;
  }

  protected static long getCPtr($javaclassname obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }
%}

// Workaround for https://github.com/swig/swig/commit/63a5a8af88271559a7b170794b4c61c30b8934ea
%typemap(javaconstruct) VariableTypeMap {
  this(null, $imcall, true);
}

%typemap(javaconstruct) CVC4::VariableTypeMap {
  this(null, $imcall, true);
}

%typemap(javaout) CVC4::Expr& {
  return new Expr(this.em, $jnicall, false);
}

%typemap(javaout) CVC4::Type& {
  return new Type(this.em, $jnicall, false);
}

%javamethodmodifiers CVC4::VariableTypeMap::VariableTypeMap() "private";

#endif /* SWIGJAVA */

%rename(get) CVC4::VariableTypeMap::operator[](Expr);
%rename(get) CVC4::VariableTypeMap::operator[](Type);

%ignore CVC4::ExprManagerMapCollection::d_typeMap;
%ignore CVC4::ExprManagerMapCollection::d_to;
%ignore CVC4::ExprManagerMapCollection::d_from;

%include "expr/variable_type_map.h"
