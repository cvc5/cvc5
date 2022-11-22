
%option noyywrap
%option nounput
%option full
%option c++

%{
#include "parser/flex/smt2_lexer.h"
#include <sstream>
#include <cassert>
#include <iostream>
#define YY_USER_ACTION lex->add_columns(yyleng);

%}

nl          [\n]+
ws          [ \t\f]+


%%

%{
  cvc5::parser::Smt2Lexer* lex = cvc5::parser::Smt2Lexer::s_inScope;
  lex->bump_span();
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
"declare-sort"   return cvc5::parser::DECLARE_SORT_TOK;
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

{ws}            lex->bump_span();
{nl}            lex->add_lines(yyleng); lex->bump_span();

";"    {
          int c;
          while((c = yyinput()) != 0)
          {
            if(c == '\n') {
                lex->add_lines(1);
                lex->bump_span();
                break;
            }
          }
        }
%%
//. { cvc5::parser::Smt2Lexer::s_inScope->undefined_token_error(); }

namespace cvc5 {
namespace parser {

Smt2Lexer* Smt2Lexer::s_inScope = nullptr;

Smt2Lexer::Smt2Lexer() : Lexer(), d_lexer(nullptr)
{
  s_inScope = this;
}

void Smt2Lexer::setFileInput(const std::string& filename)
{
  d_inputName = filename;
  d_fs.open(filename, std::fstream::in);
  if (!d_fs.is_open())
  {
    report_error(std::string("Could not open file \"") + filename
                 + std::string("\" for reading.\n"));
  }
  // TODO: make unique ptr
  d_lexer = new yyFlexLexer(&d_fs);
  init_d_span();
}

void Smt2Lexer::setStreamInput(std::istream& input,
                    const std::string& name)
{
  d_inputName = name;
  // TODO: make unique ptr
  d_lexer = new yyFlexLexer(&input);
  init_d_span();
}

void Smt2Lexer::setStringInput(const std::string& input,
                    const std::string& name)
{
  d_inputName = name;
  // TODO
  init_d_span();
}

const char* Smt2Lexer::token_str()
{
  return d_lexer->YYText();
}

Token Smt2Lexer::nextToken()
{
  return Token(d_lexer->yylex());
}

void Smt2Lexer::unexpected_token_error(Token t, const std::string& info)
{
  std::ostringstream o{};
  o << "Scanned token " << t << ", `" << d_lexer->YYText() << "`, which is invalid in this position";
  if (info.length()) {
    o << std::endl << "Note: " << info;
  }
  report_error(o.str());
}

std::string Smt2Lexer::prefix_id() {
  nextToken();
  return d_lexer->YYText();
}

void Smt2Lexer::eat_token(Token t)
{
  auto tt = nextToken();
  if (t != tt) {
    std::ostringstream o{};
    o << "Expected a " << t << ", but got a " << tt << ", `" << d_lexer->YYText() << "`";
    unexpected_token_error(tt, o.str());
  }
}

}
}
