/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Temp
 */

#include "parser/temp_lexer.h"

#include <cstdio>

#include "base/check.h"
#include "parser/flex_lexer.h"

namespace cvc5 {
namespace parser {

TempLexer::TempLexer(FlexLexer& p, bool isSygus, bool isStrict)
    : d_parent(p),
      d_input(nullptr),
      d_peeked(false),
      d_peekedChar(0),
      d_isSygus(isSygus),
      d_isStrict(isStrict)
{
  d_table["assert"] = Token::ASSERT_TOK;
  d_table["as"] = Token::AS_TOK;
  d_table["check-sat-assuming"] = Token::CHECK_SAT_ASSUMING_TOK;
  d_table["check-sat"] = Token::CHECK_SAT_TOK;
  d_table["declare-codatatypes"] = Token::DECLARE_CODATATYPES_TOK;
  d_table["declare-codatatype"] = Token::DECLARE_CODATATYPE_TOK;
  d_table["declare-const"] = Token::DECLARE_CONST_TOK;
  d_table["declare-datatypes"] = Token::DECLARE_DATATYPES_TOK;
  d_table["declare-datatype"] = Token::DECLARE_DATATYPE_TOK;
  d_table["declare-fun"] = Token::DECLARE_FUN_TOK;
  d_table["declare-sort"] = Token::DECLARE_SORT_TOK;
  d_table["define-const"] = Token::DEFINE_CONST_TOK;
  d_table["define-funs-rec"] = Token::DEFINE_FUNS_REC_TOK;
  d_table["define-fun-rec"] = Token::DEFINE_FUN_REC_TOK;
  d_table["define-fun"] = Token::DEFINE_FUN_TOK;
  d_table["define-sort"] = Token::DEFINE_SORT_TOK;
  d_table["echo"] = Token::ECHO_TOK;
  d_table["exit"] = Token::EXIT_TOK;
  d_table["get-assertions"] = Token::GET_ASSERTIONS_TOK;
  d_table["get-assignment"] = Token::GET_ASSIGNMENT_TOK;
  d_table["get-info"] = Token::GET_INFO_TOK;
  d_table["get-model"] = Token::GET_MODEL_TOK;
  d_table["get-option"] = Token::GET_OPTION_TOK;
  d_table["get-proof"] = Token::GET_PROOF_TOK;
  d_table["get-timeout-core"] = Token::GET_TIMEOUT_CORE_TOK;
  d_table["get-unsat-assumptions"] = Token::GET_UNSAT_ASSUMPTIONS_TOK;
  d_table["get-unsat-core"] = Token::GET_UNSAT_CORE_TOK;
  d_table["get-value"] = Token::GET_VALUE_TOK;
  d_table["let"] = Token::LET_TOK;
  d_table["match"] = Token::MATCH_TOK;
  d_table["par"] = Token::PAR_TOK;
  d_table["pop"] = Token::POP_TOK;
  d_table["push"] = Token::PUSH_TOK;
  d_table["reset-assertions"] = Token::RESET_ASSERTIONS_TOK;
  d_table["reset"] = Token::RESET_TOK;
  d_table["set-info"] = Token::SET_INFO_TOK;
  d_table["set-logic"] = Token::SET_LOGIC_TOK;
  d_table["set-option"] = Token::SET_OPTION_TOK;

  // initialize the tokens
  if (!d_isStrict)
  {
    d_table["block-model"] = Token::BLOCK_MODEL_TOK;
    d_table["block-model-values"] = Token::BLOCK_MODEL_VALUES_TOK;
    d_table["declare-heap"] = Token::DECLARE_HEAP;
    d_table["declare-pool"] = Token::DECLARE_POOL;
    d_table["get-abduct-next"] = Token::GET_ABDUCT_NEXT_TOK;
    d_table["get-abduct"] = Token::GET_ABDUCT_TOK;
    d_table["get-difficulty"] = Token::GET_DIFFICULTY_TOK;
    d_table["get-interpolant-next"] = Token::GET_INTERPOL_NEXT_TOK;
    d_table["get-interpolant"] = Token::GET_INTERPOL_TOK;
    d_table["get-learned-literals"] = Token::GET_LEARNED_LITERALS_TOK;
    d_table["get-qe-disjunct"] = Token::GET_QE_DISJUNCT_TOK;
    d_table["get-qe"] = Token::GET_QE_TOK;
    d_table["include"] = Token::INCLUDE_TOK;
    d_table["simplify"] = Token::SIMPLIFY_TOK;
    d_table["Constant"] = Token::SYGUS_CONSTANT_TOK;
    d_table["Variable"] = Token::SYGUS_VARIABLE_TOK;
  }
  if (d_isSygus)
  {
    d_table["assume"] = Token::ASSUME_TOK;
    d_table["check-synth-next"] = Token::CHECK_SYNTH_NEXT_TOK;
    d_table["check-synth"] = Token::CHECK_SYNTH_TOK;
    d_table["constraint"] = Token::CONSTRAINT_TOK;
    d_table["declare-var"] = Token::DECLARE_VAR_TOK;
    d_table["inv-constraint"] = Token::INV_CONSTRAINT_TOK;
    d_table["set-feature"] = Token::SET_FEATURE_TOK;
    d_table["synth-fun"] = Token::SYNTH_FUN_TOK;
    d_table["synth-inv"] = Token::SYNTH_INV_TOK;
  }
}

void TempLexer::initialize(std::istream* input) { d_input = input; }

const char* TempLexer::tokenStr() const
{
  Assert(!d_token.empty() && d_token.back() == 0);
  return d_token.data();
}

bool TempLexer::isCharacterClass(int32_t ch, CharacterClass cc)
{
  switch (cc)
  {
    case CharacterClass::DECIMAL_DIGIT: return (ch >= '0' && ch <= '9');
    case CharacterClass::HEXADECIMAL_DIGIT:
      return (ch >= '0' && ch <= '9') || (ch >= 'a' && ch <= 'f')
             || (ch >= 'A' && ch <= 'F');
    case CharacterClass::BIT: return ch == '0' || ch == '1';
    case CharacterClass::SYMBOL_START:
    {
      static const std::string symstartchars =
          "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ~!@$%^&*+=<>.?/"
          "_-";
      return symstartchars.find(ch) != std::string::npos;
    }
    case CharacterClass::SYMBOL:
      static const std::string symchars =
          "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789~!@$%^"
          "&*+=<>.?/_-";
      return symchars.find(ch) != std::string::npos;
    default: break;
  }
  return false;
}

Token TempLexer::nextToken()
{
  d_token.clear();
  Token ret = nextTokenInternal();
  // null terminate?
  d_token.push_back(0);
  return ret;
}

Token TempLexer::nextTokenInternal()
{
  int32_t ch;
  // NOTE: we store d_token only if there are multiple choices for what it
  // could contain for the returned token.

  // skip whitespace and comments
  for (;;)
  {
    do
    {
      if ((ch = nextChar()) == EOF)
      {
        return Token::EOF_TOK;
      }
    } while (std::isspace(ch));  // NOTE: bitwuzla checks printable?

    if (ch != ';')
    {
      break;
    }
    while ((ch = nextChar()) != '\n')
    {
      if (ch == EOF)
      {
        return Token::EOF_TOK;
      }
    }
  }
  switch (ch)
  {
    case '!': return Token::ATTRIBUTE_TOK;
    case '(': return Token::LPAREN_TOK;
    case ')': return Token::RPAREN_TOK;
    case '_': return Token::INDEX_TOK;
    case '|':
      pushToToken(ch);
      do
      {
        ch = nextChar();
        if (ch == EOF)
        {
          return Token::UNTERMINATED_QUOTED_SYMBOL;
        }
        pushToToken(ch);
      } while (ch != '|');
      return Token::QUOTED_SYMBOL;
    case '#':
      pushToToken(ch);
      ch = nextChar();
      switch (ch)
      {
        case 'b':
          // parse [01]+
          if (!parseNonEmptyCharList(CharacterClass::BIT))
          {
            return Token::NONE;
          }
          return Token::BINARY_LITERAL;
        case 'x':
          // parse [0-9a-fA-F]+
          if (!parseNonEmptyCharList(CharacterClass::HEXADECIMAL_DIGIT))
          {
            return Token::NONE;
          }
          return Token::HEX_LITERAL;
        case 'f':
          // parse [0-9]+m[0-9]+
          if (!parseNonEmptyCharList(CharacterClass::DECIMAL_DIGIT))
          {
            return Token::NONE;
          }
          if (!parseLiteralChar('m'))
          {
            return Token::NONE;
          }
          if (!parseNonEmptyCharList(CharacterClass::DECIMAL_DIGIT))
          {
            return Token::NONE;
          }
          return Token::FIELD_LITERAL;
        default:
          // otherwise error
          return Token::NONE;
      }
      break;
    case '"':
      pushToToken(ch);
      for (;;)
      {
        ch = nextChar();
        if (ch == EOF)
        {
          return Token::UNTERMINATED_STRING_LITERAL;
        }
        else if (ch == '"')
        {
          pushToToken(ch);
          ch = nextChar();
          // "" denotes the escape sequence for "
          if (ch != '"')
          {
            saveChar(ch);
            return Token::STRING_LITERAL;
          }
        }
        pushToToken(ch);
      }
      break;
    case ':':
      // parse a simple symbol
      if (!parseChar(CharacterClass::SYMBOL_START))
      {
        return Token::NONE;
      }
      parseNonEmptyCharList(CharacterClass::SYMBOL);
      return Token::KEYWORD;
    default:
      pushToToken(ch);
      if (isCharacterClass(ch, CharacterClass::DECIMAL_DIGIT))
      {
        Token res = Token::INTEGER_LITERAL;
        // parse [0-9]*
        parseCharList(CharacterClass::DECIMAL_DIGIT);
        // maybe .[0-9]+
        ch = nextChar();
        if (ch == '.')
        {
          res = Token::DECIMAL_LITERAL;
          // parse [0-9]+
          if (!parseNonEmptyCharList(CharacterClass::DECIMAL_DIGIT))
          {
            return Token::NONE;
          }
        }
        else
        {
          // otherwise, undo
          saveChar(ch);
        }
        return res;
      }
      else if (isCharacterClass(ch, CharacterClass::SYMBOL_START))
      {
        // otherwise, we are a simple symbol or standard alphanumeric token
        // note that we group the case when `:` is here.
        parseNonEmptyCharList(CharacterClass::SYMBOL);
        // tokenize what is stored in d_token
        return tokenizeCurrent();
      }
      // otherwise error
      break;
  }

  return Token::NONE;
}

int32_t TempLexer::nextChar()
{
  int32_t res;
  if (d_peeked)
  {
    res = d_peekedChar;
    d_peeked = false;
  }
  else
  {
    res = d_input->get();
  }
  if (res == '\n')
  {
    d_parent.addLines(1);
  }
  else
  {
    d_parent.addColumns(1);
  }
  return res;
}

void TempLexer::saveChar(int32_t ch)
{
  Assert(!d_peeked);
  d_peeked = true;
  d_peekedChar = ch;
}

void TempLexer::pushToToken(int32_t ch)
{
  Assert(ch != EOF);
  Assert(ch >= 0 && ch < 256);
  d_token.push_back(static_cast<char>(ch));
}

bool TempLexer::parseLiteralChar(int32_t chc)
{
  int32_t ch = nextChar();
  if (ch != chc)
  {
    // will be an error
    return false;
  }
  pushToToken(ch);
  return true;
}

bool TempLexer::parseChar(CharacterClass cc)
{
  int32_t ch = nextChar();
  if (!isCharacterClass(ch, cc))
  {
    // will be an error
    return false;
  }
  pushToToken(ch);
  return true;
}

bool TempLexer::parseNonEmptyCharList(CharacterClass cc)
{
  // must contain at least one character
  int32_t ch = nextChar();
  if (!isCharacterClass(ch, cc))
  {
    // will be an error
    return false;
  }
  pushToToken(ch);
  parseCharList(cc);
  return true;
}

void TempLexer::parseCharList(CharacterClass cc)
{
  int32_t ch;
  for (;;)
  {
    ch = nextChar();
    if (!isCharacterClass(ch, cc))
    {
      // failed, we are done, put the character back
      saveChar(ch);
      return;
    }
    pushToToken(ch);
  }
}

constexpr std::size_t constlength(const char* s)
{
  return std::string::traits_type::length(s);
}

Token TempLexer::tokenizeCurrent() const
{
  std::string curr(tokenStr());
  std::map<std::string, Token>::const_iterator it = d_table.find(curr);
  if (it != d_table.end())
  {
    return it->second;
  }
  return SYMBOL;
}

}  // namespace parser
}  // namespace cvc5
