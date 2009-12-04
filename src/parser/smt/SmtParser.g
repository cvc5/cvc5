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
  namespace = "CVC4::parser";        // Wrap everything in the smtparser namespace
  namespaceStd = "std";              // Cosmetic option to get rid of long defines in generated code
  namespaceAntlr = "antlr";          // Cosmetic option to get rid of long defines in generated code
}
 
/**
 * SmtParser class is the parser for the SMT-LIB files. 
 */
class SmtParser extends Parser("AntlrParser");
options {
  genHashLines = true;              // Include line number information
  importVocab = SmtVocabulary;      // Export the common vocabulary
  defaultErrorHandler = false;      // Skip the defaul error handling, just break with exceptions
  k = 2;
}
 
/**
 * Matches an attribute name from the input (:attribute_name).
 */ 
attribute 
  :  C_IDENTIFIER
  ;
  
/**
 * Matches the sort symbol, which can be an arbitrary identifier.
 */
sort_symb returns [std::string s] 
  : id:IDENTIFIER { s = id->getText(); }
  ;
  
/**
 * Matches an annotation, which is an attribute name, with an optional user value. 
 */
annotation 
  : attribute (USER_VALUE)?
  ;
  
/**
 * Matches a predicate symbol from the input. 
 */
pred_symb returns [std::string p]
  :  id:IDENTIFIER { p = id->getText(); }
  ;
  

/**
 * Matches a propositional atom from the input. 
 */
prop_atom returns [CVC4::Expr atom]
{
  std::string p;
} 
   : p = pred_symb { atom = getVariable(p, boolType()); }
   | TRUE          { atom = getTrueExpr(); }
   | FALSE         { atom = getFalseExpr(); }
   ;
    
/**
 * Matches an annotated proposition atom which is either a propositional atom, 
 * or built of other atoms using a predicate symbol. Annotation can be added if
 * enclosed in brackets. The prop_atom rule from the original SMT grammar is inlined
 * here in order to get rid of the ugly antlr non-determinism warrnings. 
 */
an_atom returns [CVC4::Expr atom] 
  : atom = prop_atom  
  ;
  
/**
 * Matches on of the unary Boolean conectives.  
 */
connective returns [CVC4::Kind kind]
  : NOT      { kind = CVC4::NOT;     } 
  | IMPLIES  { kind = CVC4::IMPLIES; }
  | AND      { kind = CVC4::AND;     }
  | OR       { kind = CVC4::OR;      }
  | XOR      { kind = CVC4::XOR;     }
  | IFF      { kind = CVC4::IFF;     }
  ;
  
/** 
 * Matches an annotated formula. 
 */
an_formula returns [CVC4::Expr formula] 
{ 
  Kind kind; 
  vector<Expr> children;
}
  :  formula = an_atom 
  |  LPAREN kind = connective an_formulas[children] RPAREN { formula = newExpression(kind, children);  }    
  ;
  
an_formulas[std::vector<Expr>& formulas]
{
  Expr f;
}
  : ( f = an_formula { formulas.push_back(f); } )+
  ;
   
/**
 * Matches the declaration of a predicate symbol.
 */
pred_symb_decl
{
  string p_name;
  vector<string> p_sorts;
}
  :  LPAREN p_name = pred_symb sort_symbs[p_sorts] RPAREN { newPredicate(p_name, p_sorts); } 
  ;
  
/**
 * Matches a sequence of sort symbols and fills them into the given vector.
 */
sort_symbs[std::vector<std::string>& sorts]
{
  std::string type;
}
  : ( type = sort_symb { sorts.push_back(type); })* 
  ;
    
/**
 * Matches the status of the benchmark, one of 'sat', 'unsat' or 'unknown'.
 */
status returns [ SmtParser::BenchmarkStatus status ]
  : SAT       { status = SMT_SATISFIABLE;    }
  | UNSAT     { status = SMT_UNSATISFIABLE;  }
  | UNKNOWN   { status = SMT_UNKNOWN;        }
  ;
  
/**
 * Matches a benchmark attribute, sucha as ':logic', ':formula', etc.
 */
bench_attribute returns [ Command* smt_command ]
{
  smt_command = 0;
  BenchmarkStatus b_status = SMT_UNKNOWN;
  Expr formula;  
  vector<string> sorts;
}
  : C_LOGIC       IDENTIFIER      
  | C_ASSUMPTION  formula = an_formula                { smt_command = new AssertCommand(formula);   }       
  | C_FORMULA     formula = an_formula                { smt_command = new CheckSatCommand(formula); }
  | C_STATUS      b_status = status                   { setBenchmarkStatus(b_status);               }        
  | C_EXTRASORTS  LPAREN sort_symbs[sorts] RPAREN     { addExtraSorts(sorts);                       }     
  | C_EXTRAPREDS  LPAREN (pred_symb_decl)+ RPAREN  
  | C_NOTES       STRING_LITERAL        
  | annotation
  ;

/**
 * Returns a pointer to a command sequence command.
 */
bench_attributes returns [CVC4::CommandSequence* cmd_seq = new CommandSequence()]
{
  Command* cmd;
}
  : (cmd = bench_attribute { cmd_seq->addCommand(cmd); } )+ 
  ;
  
/**
 * Matches the whole SMT-LIB benchmark.
 */  
benchmark 
{
  Command* cmd_seq;
}
  : LPAREN BENCHMARK IDENTIFIER cmd_seq = bench_attributes RPAREN { addCommand(cmd_seq); }
  ;
