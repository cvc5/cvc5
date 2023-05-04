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

#include "parser/smt2/smt2_lexer_new.h"

#include <cstdio>

#include "base/check.h"
#include "base/output.h"
#include "parser/flex_lexer.h"

namespace cvc5 {
namespace parser {

Smt2LexerNew::Smt2LexerNew(bool isStrict, bool isSygus)
    : FlexLexer(),
      d_peekedChar(false),
      d_chPeeked(0),
      d_isStrict(isStrict),
      d_isSygus(isSygus)
{
  for (size_t i = 0; i < 256; i++)
  {
    d_symcTable[i] = false;
  }
  for (char ch = 'a'; ch <= 'z'; ++ch)
  {
    d_symcTable[static_cast<size_t>(ch)] = true;
  }
  for (char ch = 'A'; ch <= 'Z'; ++ch)
  {
    d_symcTable[static_cast<size_t>(ch)] = true;
  }
  // SMT2 "Symbols": ~ ! @ $ % ^ & * _ - + = < > . ? /
  d_symcTable[static_cast<size_t>('~')] = true;
  d_symcTable[static_cast<size_t>('!')] = true;
  d_symcTable[static_cast<size_t>('@')] = true;
  d_symcTable[static_cast<size_t>('$')] = true;
  d_symcTable[static_cast<size_t>('%')] = true;
  d_symcTable[static_cast<size_t>('^')] = true;
  d_symcTable[static_cast<size_t>('&')] = true;
  d_symcTable[static_cast<size_t>('*')] = true;
  d_symcTable[static_cast<size_t>('_')] = true;
  d_symcTable[static_cast<size_t>('-')] = true;
  d_symcTable[static_cast<size_t>('+')] = true;
  d_symcTable[static_cast<size_t>('=')] = true;
  d_symcTable[static_cast<size_t>('<')] = true;
  d_symcTable[static_cast<size_t>('>')] = true;
  d_symcTable[static_cast<size_t>('.')] = true;
  d_symcTable[static_cast<size_t>('?')] = true;
  d_symcTable[static_cast<size_t>('/')] = true;
  d_symcTable[static_cast<size_t>(',')] = true;

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
  d_table["_"] = Token::INDEX_TOK;

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

const char* Smt2LexerNew::tokenStr() const
{
  Assert(!d_token.empty() && d_token.back() == 0);
  return d_token.data();
}

bool Smt2LexerNew::isStrict() const { return d_isStrict; }

bool Smt2LexerNew::isSygus() const { return d_isSygus; }

bool Smt2LexerNew::isCharacterClass(int32_t ch, CharacterClass cc)
{
  switch (cc)
  {
    case CharacterClass::DECIMAL_DIGIT: return (ch >= '0' && ch <= '9');
    case CharacterClass::HEXADECIMAL_DIGIT:
      return (ch >= '0' && ch <= '9') || (ch >= 'a' && ch <= 'f')
             || (ch >= 'A' && ch <= 'F');
    case CharacterClass::BIT: return ch == '0' || ch == '1';
    case CharacterClass::SYMBOL_START:
      return ch >= 0 && ch < 256 && d_symcTable[static_cast<size_t>(ch)];
    case CharacterClass::SYMBOL:
      return ch >= 0 && ch < 256
             && (d_symcTable[static_cast<size_t>(ch)]
                 || (ch >= '0' && ch <= '9'));
    default: break;
  }
  return false;
}

Token Smt2LexerNew::nextTokenInternal()
{
  Trace("lexer-debug") << "Call nextToken" << std::endl;
  d_token.clear();
  Token ret = computeNextToken();
  // null terminate?
  d_token.push_back(0);
  Trace("lexer-debug") << "Return nextToken " << ret << " / " << tokenStr()
                       << std::endl;
  return ret;
}

Token Smt2LexerNew::computeNextToken()
{
  bumpSpan();
  int32_t ch;

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
  bumpSpan();
  pushToToken(ch);
  switch (ch)
  {
    case '!': return Token::ATTRIBUTE_TOK;
    case '(': return Token::LPAREN_TOK;
    case ')': return Token::RPAREN_TOK;
    case '|':
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
      ch = nextChar();
      switch (ch)
      {
        case 'b':
          pushToToken(ch);
          // parse [01]+
          if (!parseNonEmptyCharList(CharacterClass::BIT))
          {
            return Token::NONE;
          }
          return Token::BINARY_LITERAL;
        case 'x':
          pushToToken(ch);
          // parse [0-9a-fA-F]+
          if (!parseNonEmptyCharList(CharacterClass::HEXADECIMAL_DIGIT))
          {
            return Token::NONE;
          }
          return Token::HEX_LITERAL;
        case 'f':
          pushToToken(ch);
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
      if (isCharacterClass(ch, CharacterClass::DECIMAL_DIGIT))
      {
        Token res = Token::INTEGER_LITERAL;
        // parse [0-9]*
        parseCharList(CharacterClass::DECIMAL_DIGIT);
        // maybe .[0-9]+
        ch = nextChar();
        if (ch == '.')
        {
          pushToToken(ch);
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
        parseCharList(CharacterClass::SYMBOL);
        //std::string curr(tokenStr());
        Token ret = tokenizeCurrentSymbol();
        return ret;
       // return tokenize(curr);
      }
      // otherwise error
      break;
  }
  return Token::NONE;
}

int32_t Smt2LexerNew::nextChar()
{
  int32_t res;
  if (d_peekedChar)
  {
    res = d_chPeeked;
    d_peekedChar = false;
  }
  else
  {
    res = readNextChar();
    if (res == '\n')
    {
      d_span.d_end.d_line++;
      d_span.d_end.d_column = 0;
    }
    else
    {
      d_span.d_end.d_column++;
    }
  }
  return res;
}

void Smt2LexerNew::saveChar(int32_t ch)
{
  Assert(!d_peekedChar);
  d_peekedChar = true;
  d_chPeeked = ch;
}

void Smt2LexerNew::pushToToken(int32_t ch)
{
  Assert(ch != EOF);
  Assert(ch >= 0 && ch < 256);
  d_token.push_back(static_cast<char>(ch));
}

bool Smt2LexerNew::parseLiteralChar(int32_t chc)
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

bool Smt2LexerNew::parseChar(CharacterClass cc)
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

bool Smt2LexerNew::parseNonEmptyCharList(CharacterClass cc)
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

void Smt2LexerNew::parseCharList(CharacterClass cc)
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

Token Smt2LexerNew::tokenize(const std::string& curr) const
{
  std::map<std::string, Token>::const_iterator it = d_table.find(curr);
  if (it != d_table.end())
  {
    return it->second;
  }
  return SYMBOL;
}

Token Smt2LexerNew::tokenizeCurrentSymbol() const
{
  Assert(!d_token.empty());
  switch (d_token[0])
  {
    case 'a':
      if (d_token.size() == 2 && d_token[1] == 's')
      {
        return Token::AS_TOK;
      }
      break;
    case 'p':
      if (d_token.size() == 3 && d_token[1] == 'a' && d_token[2] == 'r')
      {
        return Token::PAR_TOK;
      }
      break;
    case 'l':
      if (d_token.size() == 3 && d_token[1] == 'e' && d_token[2] == 't')
      {
        return Token::LET_TOK;
      }
      break;
    case 'm':
      if (d_token.size() == 5 && d_token[1] == 'a' && d_token[2] == 't' && d_token[3] == 'c'
          && d_token[4] == 'h')
      {
        return Token::MATCH_TOK;
      }
      break;
    case 'C':
      if ((d_isSygus || !d_isStrict) && d_token.size() == 8 && d_token[1] == 'o' && d_token[2] == 'n'
          && d_token[3] == 's' && d_token[4] == 't' && d_token[5] == 'a'
          && d_token[6] == 'n' && d_token[7] == 't')
      {
        return Token::SYGUS_CONSTANT_TOK;
      }
      break;
    case 'V':
      if ((d_isSygus || !d_isStrict) && d_token.size() == 8 && d_token[1] == 'a' && d_token[2] == 'r'
          && d_token[3] == 'i' && d_token[4] == 'a' && d_token[5] == 'b'
          && d_token[6] == 'l' && d_token[7] == 'e')
      {
        return Token::SYGUS_VARIABLE_TOK;
      }
      break;
    case '_':
      if (d_token.size() == 1)
      {
        return Token::INDEX_TOK;
      }
      break;
    default: break;
  }
  return Token::SYMBOL;
}

}  // namespace parser
}  // namespace cvc5
