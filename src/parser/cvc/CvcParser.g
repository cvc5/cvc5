header "post_include_hpp" {
#include "parser/antlr_parser.h"
}

header "post_include_cpp" {
#include <vector> 

using namespace std;
using namespace CVC4;
using namespace CVC4::parser;
}
    
options {
  language = "Cpp";                  // C++ output for antlr
  namespaceStd = "std";              // Cosmetic option to get rid of long defines in generated code
  namespaceAntlr = "antlr";          // Cosmetic option to get rid of long defines in generated code
  namespace = "CVC4::parser";        // Wrap everything in the smtparser namespace
}
 
/**
 * AntlrCvcParser class is the parser for the files in CVC format. 
 */
class AntlrCvcParser extends Parser("AntlrParser");
options {
  genHashLines = true;              // Include line number information
  importVocab = CvcVocabulary;      // Import the common vocabulary
  defaultErrorHandler = false;      // Skip the defaul error handling, just break with exceptions
  k = 2;
}
 
/**
 * Matches a command of the input. If a declaration, it will return an empty 
 * command.
 */
command returns [CVC4::Command* cmd = 0]
{
  Expr f;
  vector<string> ids;
}
  : ASSERT   f = formula  { cmd = new AssertCommand(f);   }
  | QUERY    f = formula  { cmd = new QueryCommand(f);    }
  | CHECKSAT f = formula  { cmd = new CheckSatCommand(f); }
  | CHECKSAT              { cmd = new CheckSatCommand();  }
  | identifierList[ids] COLON type { 
      newPredicates(ids); 
      cmd = new EmptyCommand("Declaration"); 
    }
  | EOF 
  ;

identifierList[std::vector<std::string>& id_list]
  : id1:IDENTIFIER { id_list.push_back(id1->getText()); } 
    (
      COMMA 
      id2:IDENTIFIER { id_list.push_back(id2->getText()); }
    )*
  ;
 
type
  : BOOLEAN
  ;

formula returns [CVC4::Expr formula]
  :  formula = bool_formula
  ;

bool_formula returns [CVC4::Expr formula] 
{
  vector<Expr> formulas;
  vector<Kind> kinds;
  Expr f1, f2;
  Kind k;
}
  : f1 = primary_bool_formula { formulas.push_back(f1); } 
      ( k = bool_operator { kinds.push_back(k); } f2 = primary_bool_formula { formulas.push_back(f2); } )* 
    { 
      // Create the expression based on precedences
      formula = createPrecedenceExpr(formulas, kinds);
    }
  ;
  
primary_bool_formula returns [CVC4::Expr formula]
  : formula = bool_atom
  | NOT formula = primary_bool_formula { formula = newExpression(CVC4::NOT, formula); }
  | LPAREN formula = bool_formula RPAREN
  ;

bool_operator returns [CVC4::Kind kind]
  : IMPLIES  { kind = CVC4::IMPLIES; }
  | AND      { kind = CVC4::AND;     }
  | OR       { kind = CVC4::OR;      }
  | XOR      { kind = CVC4::XOR;     }
  | IFF      { kind = CVC4::IFF;     }
  ;
    
bool_atom returns [CVC4::Expr atom]
{
  string p;
}
  : p = predicate_sym {isDeclared(p, SYM_VARIABLE)}? { atom = getVariable(p); }
      exception catch [antlr::SemanticException ex] {
        rethrow(ex, "Undeclared variable " + p);
      }
  | TRUE  { atom = getTrueExpr(); }
  | FALSE { atom = getFalseExpr(); }
  ;
 
predicate_sym returns [std::string p]
  : id:IDENTIFIER { p = id->getText(); }
  ;
 