%{
#include "parser/parser.h"
%}

namespace CVC4 {
  namespace parser {
    enum DeclarationCheck;
    enum SymbolType;
    %ignore operator<<(std::ostream&, DeclarationCheck);
    %ignore operator<<(std::ostream&, SymbolType);
  }/* namespace CVC4::parser */
}/* namespace CVC4 */

%include "parser/parser.h"
