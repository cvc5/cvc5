#include "parser/flex/lexer.h"

Lexer::Lexer()
{
}

void Lexer::report_error(const std::string &msg)
{
  if (d_inputName.length())
  {
    std::cerr << "Error: " << d_inputName << " at " << d_span;
  }
  std::cerr << std::endl << msg << std::endl;
  exit(1);
}

void Lexer::init_d_span()
{
    d_span.d_start.d_line = 1;
    d_span.d_start.d_column = 1;
    d_span.d_end.d_line = 1;
    d_span.d_end.d_column = 1;
}
void Lexer::bump_span()
{
    d_span.d_start.d_line = d_span.d_end.d_line;
    d_span.d_start.d_column = d_span.d_end.d_column;
}
void Lexer::add_columns(uint32_t columns)
{
    d_span.d_end.d_column += columns;
}
void Lexer::add_lines(uint32_t lines)
{
    d_span.d_end.d_line += lines;
    d_span.d_end.d_column = 1;
}
std::ostream& operator<<(std::ostream& o, const Location& l)
{
    return o << l.d_line << ":" << l.d_column;
}
std::ostream& operator<<(std::ostream& o, const Span& l)
{
    return o << l.d_start << "-" << l.d_end;
}

}
}
