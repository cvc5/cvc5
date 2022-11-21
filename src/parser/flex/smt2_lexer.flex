   // An example of using the flex C++ scanner class.

%option noyywrap
%option nounput
%option full
%option c++

%{
#include "lexer.h"
#include <sstream>
#include <cassert>
#include <iostream>
#define YY_USER_ACTION add_columns(yyleng);

%}


%%

%{
    bump_span();
%}


"mp_add"        return Token::SET_LOGIC;

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

Smt2Lexer::Smt2Lexer() : d_lexer(nullptr)
{
}


/*
void reinsert_token(Token t)
{
  if (d_peeked[0] == TokenErr)
  {
    d_peeked[0] = t;
  }
  else if (d_peeked[1] == TokenErr)
  {
    d_peeked[1] = d_peeked[0];
    d_peeked[0] = t;
  }
  else
  {
    assert(false);
  }
}
*/

const char* Smt2Lexer::token_str()
{
  return d_lexer->YYText();
}

Token Smt2Lexer::next_token()
{
  return Token(d_lexer->yylex());
  /*
  Token t;
  if (d_peeked[0] == TokenErr)
  {
    t = Token(d_lexer->yylex());
  }
  else
  {
    t = d_peeked[0];
    d_peeked[0] = d_peeked[1];
    d_peeked[1] = TokenErr;
  }
    switch (t) {
      case Token::Provided: {
        t = Token::Caret;
        break;
      }
      case Token::Forall: {
        t = Token::Bang;
        break;
      }
      case Token::Lam: {
        t = Token::ReverseSolidus;
        break;
      }
      case Token::Let: {
        t = Token::At;
        break;
      }
      default: break;
    }
  return t;
  */
}

void Smt2Lexer::report_error(const std::string &msg)
{
  if (d_filename.length())
  {
    std::cerr << "Error: " << d_filename << " at " << d_span;
  }
  std::cerr << std::endl << msg << std::endl;
  exit(1);
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

std::string prefix_id() {
  next_token();
  return d_lexer->YYText();
}

void Smt2Lexer::eat_token(Token t)
{
  auto tt = next_token();
  if (t != tt) {
    std::ostringstream o{};
    o << "Expected a " << t << ", but got a " << tt << ", `" << d_lexer->YYText() << "`";
    unexpected_token_error(tt, o.str());
  }
}

void Smt2Lexer::init_d_span()
{
    d_span.start.line = 1;
    d_span.start.column = 1;
    d_span.end.line = 1;
    d_span.end.column = 1;
}
void Smt2Lexer::bump_span()
{
    d_span.start.line = d_span.end.line;
    d_span.start.column = d_span.end.column;
}
void Smt2Lexer::add_columns(uint32_t columns)
{
    d_span.end.column += columns;
}
void Smt2Lexer::add_lines(uint32_t lines)
{
    d_span.end.line += lines;
    d_span.end.column = 1;
}
std::ostream& operator<<(std::ostream& o, const Location& l)
{
    return o << l.line << ":" << l.column;
}
std::ostream& operator<<(std::ostream& o, const Span& l)
{
    return o << l.start << "-" << l.end;
}
