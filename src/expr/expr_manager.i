%{
#include "expr/expr_manager.h"
%}

%include "expr/expr_manager.h"

%template(mkConst) CVC4::ExprManager::mkConst< CVC4::Integer >;
%template(mkConst) CVC4::ExprManager::mkConst<CVC4::Rational>;

%include "expr/expr_manager.h"
