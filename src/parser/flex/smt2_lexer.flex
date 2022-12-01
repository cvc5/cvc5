
%{
#include "parser/flex/smt2_lexer.h"

// Alternatively we could lex simple_symbol as:
//  [a-zA-Z0-9~!@\$%\^&\*+=<>\.\?/_-]+
// ??
%}

%option noyywrap
%option nounput
%option full
%option c++
%option yyclass="cvc5::parser::Smt2Lexer"

%{
#define YY_USER_ACTION add_columns(yyleng);
%}

nl          [\n]+
ws          [ \t\r\f]+
string_literal \"(\"\"|[^"])*\"
unterminated_string_literal \"(\"\"|[^"])*
nat         [0-9]+
decimal     [0-9]+\.[0-9]+
bitstr      #b[01]+
hexstr      #x[0-9a-fA-F]+
simple_symbol [a-zA-Z~!@\$%\^&\*+=<>\.\?/_-][a-zA-Z0-9~!@\$%\^&\*+=<>\.\?/_-]*
quoted_symbol \|[^(\|)]*\|
unterminated_quoted_symbol \|[^(\|)]*

%%

%{
  bump_span();
%}

"assert"   return cvc5::parser::ASSERT_TOK;
"assume"   return cvc5::parser::ASSUME_TOK;
"as"   return cvc5::parser::AS_TOK;
"!"   return cvc5::parser::ATTRIBUTE_TOK;
"block-model"   return cvc5::parser::BLOCK_MODEL_TOK;
"block-model-values"   return cvc5::parser::BLOCK_MODEL_VALUES_TOK;
"check-sat-assuming"   return cvc5::parser::CHECK_SAT_ASSUMING_TOK;
"check-sat"   return cvc5::parser::CHECK_SAT_TOK;
"check-synth-next"   return cvc5::parser::CHECK_SYNTH_NEXT_TOK;
"check-synth"   return cvc5::parser::CHECK_SYNTH_TOK;
"constraint"   return cvc5::parser::CONSTRAINT_TOK;
"declare-codatatypes"   return cvc5::parser::DECLARE_CODATATYPES_TOK;
"declare-codatatype"   return cvc5::parser::DECLARE_CODATATYPE_TOK;
"declare-const"   return cvc5::parser::DECLARE_CONST_TOK;
"declare-datatypes"   return cvc5::parser::DECLARE_DATATYPES_TOK;
"declare-datatype"   return cvc5::parser::DECLARE_DATATYPE_TOK;
"declare-fun"   return cvc5::parser::DECLARE_FUN_TOK;
"declare-heap"   return cvc5::parser::DECLARE_HEAP;
"declare-pool"   return cvc5::parser::DECLARE_POOL;
"declare-sort"   return cvc5::parser::DECLARE_SORT_TOK;
"declare-var"   return cvc5::parser::DECLARE_VAR_TOK;
"define-const"   return cvc5::parser::DEFINE_CONST_TOK;
"define-funs-rec"   return cvc5::parser::DEFINE_FUNS_REC_TOK;
"define-fun-rec"   return cvc5::parser::DEFINE_FUN_REC_TOK;
"define-fun"   return cvc5::parser::DEFINE_FUN_TOK;
"define-sort"   return cvc5::parser::DEFINE_SORT_TOK;
"echo"   return cvc5::parser::ECHO_TOK;
"exit"   return cvc5::parser::EXIT_TOK;
"get-abduct-next"   return cvc5::parser::GET_ABDUCT_NEXT_TOK;
"get-abduct"   return cvc5::parser::GET_ABDUCT_TOK;
"get-assertions"   return cvc5::parser::GET_ASSERTIONS_TOK;
"get-assignment"   return cvc5::parser::GET_ASSIGNMENT_TOK;
"get-difficulty"   return cvc5::parser::GET_DIFFICULTY_TOK;
"get-info"   return cvc5::parser::GET_INFO_TOK;
"get-interpol-next"   return cvc5::parser::GET_INTERPOL_NEXT_TOK;
"get-interpol"   return cvc5::parser::GET_INTERPOL_TOK;
"get-learned-literals"   return cvc5::parser::GET_LEARNED_LITERALS_TOK;
"get-model"   return cvc5::parser::GET_MODEL_TOK;
"get-option"   return cvc5::parser::GET_OPTION_TOK;
"get-proof"   return cvc5::parser::GET_PROOF_TOK;
"get-qe-disjunct"   return cvc5::parser::GET_QE_DISJUNCT_TOK;
"get-qe"   return cvc5::parser::GET_QE_TOK;
"get-unsat-assumptions"   return cvc5::parser::GET_UNSAT_ASSUMPTIONS_TOK;
"get-unsat-core"   return cvc5::parser::GET_UNSAT_CORE_TOK;
"get-value"   return cvc5::parser::GET_VALUE_TOK;
"include"   return cvc5::parser::INCLUDE_TOK;
"_"   return cvc5::parser::INDEX_TOK;
"inv-constraint"   return cvc5::parser::INV_CONSTRAINT_TOK;
"let"   return cvc5::parser::LET_TOK;
"("   return cvc5::parser::LPAREN_TOK;
"match"   return cvc5::parser::MATCH_TOK;
"par"   return cvc5::parser::PAR_TOK;
"pop"   return cvc5::parser::POP_TOK;
"push"   return cvc5::parser::PUSH_TOK;
"reset-assertions"   return cvc5::parser::RESET_ASSERTIONS_TOK;
"reset"   return cvc5::parser::RESET_TOK;
")"   return cvc5::parser::RPAREN_TOK;
"set-feature"   return cvc5::parser::SET_FEATURE_TOK;
"set-info"   return cvc5::parser::SET_INFO_TOK;
"set-logic"   return cvc5::parser::SET_LOGIC_TOK;
"set-option"   return cvc5::parser::SET_OPTION_TOK;
"simplify"   return cvc5::parser::SIMPLIFY_TOK;
"Constant"   return cvc5::parser::SYGUS_CONSTANT_TOK;
"Variable"   return cvc5::parser::SYGUS_VARIABLE_TOK;
"synth-fun"   return cvc5::parser::SYNTH_FUN_TOK;
"synth-inv"   return cvc5::parser::SYNTH_INV_TOK;

{ws}   bump_span();
{nl}   add_lines(yyleng); bump_span();
{string_literal}   return cvc5::parser::STRING_LITERAL;
{unterminated_string_literal}   return cvc5::parser::UNTERMINATED_STRING_LITERAL;
{nat}   return cvc5::parser::INTEGER_LITERAL;
{decimal}   return cvc5::parser::DECIMAL_LITERAL;
{hexstr}   return cvc5::parser::HEX_LITERAL;
{bitstr}   return cvc5::parser::BINARY_LITERAL;
\:{simple_symbol}  return cvc5::parser::KEYWORD;
{quoted_symbol} return cvc5::parser::QUOTED_SYMBOL;
{unterminated_quoted_symbol} return cvc5::parser::UNTERMINATED_QUOTED_SYMBOL;
{simple_symbol} return cvc5::parser::SYMBOL;

";"    {
          int c;
          while((c = yyinput()) != 0)
          {
            if(c == '\n') {
                add_lines(1);
                bump_span();
                break;
            }
          }
        }
. parseError("Error finding token");
%%

namespace cvc5 {
namespace parser {

Smt2Lexer::Smt2Lexer() : Lexer()
{
}

}
}
