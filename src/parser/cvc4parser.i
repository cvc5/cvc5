%import "bindings/swig.h"

%module CVC4Parser
// nspace completely broken with Java packaging
//%nspace;

%{
namespace CVC4 {}
using namespace CVC4;
%}

%include "parser/input.i"
%include "parser/parse_op.i"
%include "parser/parser.i"
%include "parser/parser_builder.i"
%include "parser/parser_exception.i"
