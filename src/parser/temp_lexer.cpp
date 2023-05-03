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

#include "base/check.h"
#include "parser/flex_lexer.h"

namespace cvc5 {
namespace parser {

TempLexer::TempLexer(FlexLexer& p)
    : d_parent(p), d_input(nullptr), d_peeked(false), d_peekedChar(0)
{
}

void TempLexer::initialize(std::istream* input) { d_input = input; }

const char* TempLexer::tokenStr() { return d_token.data(); }

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
       "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ~!@$%^&*+=<>.?/_-";
      return symstartchars.find(ch)!=std::string::npos;
    }
    case CharacterClass::SYMBOL:  
      static const std::string symchars = 
        "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789~!@$%^&*+=<>.?/_-";
      return symchars.find(ch)!=std::string::npos;
    default: break;
  }
  return false;
}

Token TempLexer::nextToken()
{
  int32_t ch;
  d_token.clear();

  // NOTE: when to store d_token?

  // skip whitespace and comments
  for (;;)
  {
    do
    {
      if ((ch = nextChar()) == EOF)
      {
        d_token.push_back(0);
        return EOF_TOK;
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
        d_token.push_back(0);
        return EOF_TOK;
      }
    }
  }
  switch (ch)
  {
    case '|':
      pushToToken(ch);
      do
      {
        ch = nextChar();
        if (ch == EOF)
        {
          d_token.push_back(0);
          return UNTERMINATED_QUOTED_SYMBOL;
        }
        pushToToken(ch);
      } while (ch != '|');
      d_token.push_back(0);
      return QUOTED_SYMBOL;
    case '!': return ATTRIBUTE_TOK;
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
          break;
        case 'x':
          // parse [0-9a-fA-F]+
          if (!parseNonEmptyCharList(CharacterClass::HEXADECIMAL_DIGIT))
          {
            return Token::NONE;
          }
          break;
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
          break;
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
          d_token.push_back(0);
          return UNTERMINATED_STRING_LITERAL;
        }
        else if (ch == '"')
        {
          pushToToken(ch);
          ch = nextChar();
          // "" denotes the escape sequence for "
          if (ch != '"')
          {
            saveChar(ch);
            d_token.push_back(0);
            return STRING_LITERAL;
          }
        }
        pushToToken(ch);
      }
      break;
    case '(': return LPAREN_TOK;
    case ')': return RPAREN_TOK;
    case '_': return INDEX_TOK;
    case ':':
      if (!parseChar(CharacterClass::SYMBOL_START))
      {
        return Token::NONE;
      }
      parseNonEmptyCharList(CharacterClass::SYMBOL);
      return KEYWORD;
    default:
      pushToToken(ch);
      if (isCharacterClass(ch, CharacterClass::DECIMAL_DIGIT))
      {
        Token res = INTEGER_LITERAL;
        // parse [0-9]*
        parseCharList(CharacterClass::DECIMAL_DIGIT);
        // maybe .[0-9]+
        ch = nextChar();
        if (ch == '.')
        {
          res = DECIMAL_LITERAL;
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
        d_token.push_back(0);
        return res;
      }
      else if (isCharacterClass(ch, CharacterClass::SYMBOL_START))
      {
        // otherwise, we are a simple symbol or standard alphanumeric token
        // note that we group the case when `:` is here.
        parseNonEmptyCharList(CharacterClass::SYMBOL);
        return SYMBOL;
      }
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

}  // namespace parser
}  // namespace cvc5
