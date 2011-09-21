%import "bindings/swig.h"

%module CVC4Parser
// nspace completely broken with Java packaging
//%nspace;

%{
namespace CVC4 {}
using namespace CVC4;
%}

%include "parser/parser_exception.i"
%include "parser/input.i"
%include "parser/parser.i"
%include "parser/parser_builder.i"
