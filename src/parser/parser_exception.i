%{
#include "parser/parser_exception.h"
%}

%ignore CVC4::parser::ParserException::ParserException(const char*);
%ignore CVC4::parser::ParserEndOfFileException::ParserEndOfFileException(const char*);

%include "parser/parser_exception.h"
