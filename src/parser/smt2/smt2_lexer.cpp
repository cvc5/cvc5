/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The lexer for smt2
 */

#include "parser/smt2/smt2_lexer.h"

#include <cstdio>

#include "base/output.h"
#include "parser/lexer.h"

namespace cvc5 {
namespace parser {

Smt2Lexer::Smt2Lexer(bool isStrict, bool isSygus)
    : Lexer(),
      d_isStrict(isStrict),
      d_isSygus(isSygus)
{
  for (char ch = 'a'; ch <= 'z'; ++ch)
  {
    d_charClass[ch] |= static_cast<uint32_t>(CharacterClass::SYMBOL_START);
    d_charClass[ch] |= static_cast<uint32_t>(CharacterClass::SYMBOL);
  }
  for (char ch = 'a'; ch <= 'f'; ++ch)
  {
    d_charClass[ch] |= static_cast<uint32_t>(CharacterClass::HEXADECIMAL_DIGIT);
  }
  for (char ch = 'A'; ch <= 'Z'; ++ch)
  {
    d_charClass[ch] |= static_cast<uint32_t>(CharacterClass::SYMBOL_START);
    d_charClass[ch] |= static_cast<uint32_t>(CharacterClass::SYMBOL);
  }
  for (char ch = 'A'; ch <= 'F'; ++ch)
  {
    d_charClass[ch] |= static_cast<uint32_t>(CharacterClass::HEXADECIMAL_DIGIT);
  }
  for (char ch = '0'; ch <= '9'; ++ch)
  {
    d_charClass[ch] |= static_cast<uint32_t>(CharacterClass::HEXADECIMAL_DIGIT);
    d_charClass[ch] |= static_cast<uint32_t>(CharacterClass::DECIMAL_DIGIT);
    d_charClass[ch] |= static_cast<uint32_t>(CharacterClass::SYMBOL);
  }
  d_charClass['0'] |= static_cast<uint32_t>(CharacterClass::BIT);
  d_charClass['1'] |= static_cast<uint32_t>(CharacterClass::BIT);
  // ~!@$%^&*_-+|=<>.?/
  for (char ch : s_extraSymbolChars)
  {
    d_charClass[ch] |= static_cast<uint32_t>(CharacterClass::SYMBOL_START);
    d_charClass[ch] |= static_cast<uint32_t>(CharacterClass::SYMBOL);
  }
  // whitespace
  d_charClass[' '] |= static_cast<uint32_t>(CharacterClass::WHITESPACE);
  d_charClass['\t'] |= static_cast<uint32_t>(CharacterClass::WHITESPACE);
  d_charClass['\r'] |= static_cast<uint32_t>(CharacterClass::WHITESPACE);
  d_charClass['\n'] |= static_cast<uint32_t>(CharacterClass::WHITESPACE);
}

const char* Smt2Lexer::tokenStr() const
{
  Assert(!d_token.empty() && d_token.back() == 0);
  return d_token.data();
}
bool Smt2Lexer::isStrict() const { return d_isStrict; }
bool Smt2Lexer::isSygus() const { return d_isSygus; }

Token Smt2Lexer::nextTokenInternal()
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

Token Smt2Lexer::computeNextToken()
{
  bumpSpan();
  char ch;
  // skip whitespace and comments
  for (;;)
  {
    do
    {
      if ((ch = nextChar()) == EOF)
      {
        return Token::EOF_TOK;
      }
    } while (isCharacterClass(ch, CharacterClass::WHITESPACE));

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
            parseError("Error expected bit string");
          }
          return Token::BINARY_LITERAL;
        case 'x':
          pushToToken(ch);
          // parse [0-9a-fA-F]+
          if (!parseNonEmptyCharList(CharacterClass::HEXADECIMAL_DIGIT))
          {
            parseError("Error expected hexidecimal string");
          }
          return Token::HEX_LITERAL;
        case 'f':
          pushToToken(ch);
          // parse [0-9]+m[0-9]+
          if (!parseNonEmptyCharList(CharacterClass::DECIMAL_DIGIT))
          {
            parseError("Error expected decimal for finite field value");
          }
          if (!parseLiteralChar('m'))
          {
            parseError("Error bad syntax for finite field value");
          }
          if (!parseNonEmptyCharList(CharacterClass::DECIMAL_DIGIT))
          {
            parseError("Error expected decimal for finite field size");
          }
          return Token::FIELD_LITERAL;
        default:
          // otherwise error
          parseError("Error finding token following #");
          break;
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
        parseError("Error expected symbol following :");
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
            parseError("Error expected decimal string following .");
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
        // tokenize the current symbol, which may be a special case
        return tokenizeCurrentSymbol();
      }
      // otherwise error
      break;
  }
  parseError("Error finding token");
  return Token::NONE;
}

bool Smt2Lexer::parseLiteralChar(char chc)
{
  char ch = nextChar();
  if (ch != chc)
  {
    // will be an error
    return false;
  }
  pushToToken(ch);
  return true;
}

bool Smt2Lexer::parseChar(CharacterClass cc)
{
  char ch = nextChar();
  if (!isCharacterClass(ch, cc))
  {
    // will be an error
    return false;
  }
  pushToToken(ch);
  return true;
}

bool Smt2Lexer::parseNonEmptyCharList(CharacterClass cc)
{
  // must contain at least one character
  char ch = nextChar();
  if (!isCharacterClass(ch, cc))
  {
    // will be an error
    return false;
  }
  pushToToken(ch);
  parseCharList(cc);
  return true;
}

void Smt2Lexer::parseCharList(CharacterClass cc)
{
  char ch;
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

Token Smt2Lexer::tokenizeCurrentSymbol() const
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
      if (d_token.size() == 5 && d_token[1] == 'a' && d_token[2] == 't'
          && d_token[3] == 'c' && d_token[4] == 'h')
      {
        return Token::MATCH_TOK;
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
  // otherwise not a special symbol
  return Token::SYMBOL;
}

}  // namespace parser
}  // namespace cvc5
