%{
#include "parser/parser.h"
%}

namespace CVC4 {
  namespace parser {
    enum DeclarationCheck;
    enum SymbolType;
    %ignore operator<<(std::ostream&, DeclarationCheck);
    %ignore operator<<(std::ostream&, SymbolType);

    class ParserExprStream : public CVC4::ExprStream {
      Parser* d_parser;
    public:
      ParserExprStream(Parser* parser) : d_parser(parser) {}
      ~ParserExprStream() { delete d_parser; }
      Expr nextExpr() { return d_parser->nextExpression(); }
    };/* class Parser::ExprStream */
  }/* namespace CVC4::parser */
}/* namespace CVC4 */

%ignore CVC4::parser::Parser::ExprStream;

%include "parser/parser.h"

%{
namespace CVC4 {
  namespace parser {
    typedef CVC4::parser::Parser::ExprStream ParserExprStream;
  }
}
%}
