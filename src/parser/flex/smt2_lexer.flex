
%{
#include "parser/flex/smt2_lexer.h"
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
ws          [ \t\f]+


%%

%{
  bump_span();
%}

"assert"   return cvc5::parser::ASSERT_TOK;
"assume"   return cvc5::parser::ASSUME_TOK;
"as"   return cvc5::parser::AS_TOK;
":inst-add-to-pool"   return cvc5::parser::ATTRIBUTE_INST_ADD_TO_POOL_TOK;
":named"   return cvc5::parser::ATTRIBUTE_NAMED_TOK;
":no-pattern"   return cvc5::parser::ATTRIBUTE_NO_PATTERN_TOK;
":pattern"   return cvc5::parser::ATTRIBUTE_PATTERN_TOK;
":pool"   return cvc5::parser::ATTRIBUTE_POOL_TOK;
":qid"   return cvc5::parser::ATTRIBUTE_QUANTIFIER_ID_TOK;
":skolem-add-to-pool"   return cvc5::parser::ATTRIBUTE_SKOLEM_ADD_TO_POOL_TOK;
"block-model"   return cvc5::parser::BLOCK_MODEL_TOK;
"block-model-values"   return cvc5::parser::BLOCK_MODEL_VALUES_TOK;
"check-sat-assuming"   return cvc5::parser::CHECK_SAT_ASSUMING_TOK;
"check-sat"   return cvc5::parser::CHECK_SAT_TOK;
"check-synth-next"   return cvc5::parser::CHECK_SYNTH_NEXT_TOK;
"check-synth"   return cvc5::parser::CHECK_SYNTH_TOK;
"constraint"   return cvc5::parser::CONSTRAINT_TOK;
"const"   return cvc5::parser::CONST_TOK;
"declare-codatatypes"   return cvc5::parser::DECLARE_CODATATYPES_TOK;
"declare-codatatype"   return cvc5::parser::DECLARE_CODATATYPE_TOK;
"declare-const"   return cvc5::parser::DECLARE_CONST_TOK;
"declare-datatypes"   return cvc5::parser::DECLARE_DATATYPES_TOK;
"declare-datatype"   return cvc5::parser::DECLARE_DATATYPE_TOK;
"declare-fun"   return cvc5::parser::DECLARE_FUN_TOK;
"declare-heap"   return cvc5::parser::DECLARE_HEAP;
"declare-pool"   return cvc5::parser::DECLARE_POOL;
"declare-var"   return cvc5::parser::DECLARE_VAR_TOK;
"define-const"   return cvc5::parser::DEFINE_CONST_TOK;
"define-funs-rec"   return cvc5::parser::DEFINE_FUNS_REC_TOK;
"define-fun-rec"   return cvc5::parser::DEFINE_FUN_REC_TOK;
"define-fun"   return cvc5::parser::DEFINE_FUN_TOK;
"define-sort"   return cvc5::parser::DEFINE_SORT_TOK;
"echo"   return cvc5::parser::ECHO_TOK;
"exists"   return cvc5::parser::EXISTS_TOK;
"exit"   return cvc5::parser::EXIT_TOK;
"fmf.card"   return cvc5::parser::FMF_CARD_TOK;
"forall"   return cvc5::parser::FORALL_TOK;
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
"set.comprehension"   return cvc5::parser::SET_COMPREHENSION_TOK;
"set-feature"   return cvc5::parser::SET_FEATURE_TOK;
"set-info"   return cvc5::parser::SET_INFO_TOK;
"set-logic"   return cvc5::parser::SET_LOGIC_TOK;
"set-option"   return cvc5::parser::SET_OPTION_TOK;
"simplify"   return cvc5::parser::SIMPLIFY_TOK;
"Constant"   return cvc5::parser::SYGUS_CONSTANT_TOK;
"Variable"   return cvc5::parser::SYGUS_VARIABLE_TOK;
"synth-fun"   return cvc5::parser::SYNTH_FUN_TOK;
"synth-inv"   return cvc5::parser::SYNTH_INV_TOK;
"is"   return cvc5::parser::TESTER_TOK;
"update"   return cvc5::parser::UPDATE_TOK;

{ws}            bump_span();
{nl}            add_lines(yyleng); bump_span();

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
%%

namespace cvc5 {
namespace parser {

Smt2Lexer::Smt2Lexer() : Lexer()
{
}

}
}
