%{
#include "expr/variable_type_map.h"
%}

%rename(get) CVC4::VariableTypeMap::operator[](Expr);
%rename(get) CVC4::VariableTypeMap::operator[](Type);

%include "expr/variable_type_map.h"
