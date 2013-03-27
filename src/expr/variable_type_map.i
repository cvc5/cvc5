%{
#include "expr/variable_type_map.h"
%}

%rename(get) CVC4::VariableTypeMap::operator[](Expr);
%rename(get) CVC4::VariableTypeMap::operator[](Type);

%ignore CVC4::ExprManagerMapCollection::d_typeMap;
%ignore CVC4::ExprManagerMapCollection::d_to;
%ignore CVC4::ExprManagerMapCollection::d_from;

%include "expr/variable_type_map.h"
