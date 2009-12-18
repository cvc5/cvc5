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
 * AntlrSmtParser class is the parser for the SMT-LIB files. 
 */
class AntlrSmtParser extends Parser("AntlrParser");
options {
  genHashLines = true;              // Include line number information
  importVocab = SmtVocabulary;      // Import the common vocabulary
  defaultErrorHandler = false;      // Skip the defaul error handling, just break with exceptions
  k = 2;
}

/**
 * Parses an expression.
 * @return the parsed expression
 */
parseExpr returns [CVC4::Expr expr]
  : expr = annotatedFormula
  ;

/**
 * Parses a command (the whole benchmark)
 * @return the command of the benchmark
 */
parseCommand returns [CVC4::Command* cmd]
  : cmd = benchmark
  ; 
 
/**
 * Matches the whole SMT-LIB benchmark.
 * @return the sequence command containing the whole problem
 */  
benchmark returns [Command* cmd]
  : LPAREN BENCHMARK IDENTIFIER cmd = benchAttributes RPAREN
  | EOF { cmd = 0; } 
  ;

/**
 * Matchecs sequence of benchmark attributes and returns a pointer to a command 
 * sequence command.
 * @return the command sequence 
 */
benchAttributes returns [CVC4::CommandSequence* cmd_seq = new CommandSequence()]
{
  Command* cmd;
}
  : (cmd = benchAttribute { if (cmd) cmd_seq->addCommand(cmd); } )+ 
  ;
  
/**
 * Matches a benchmark attribute, sucha as ':logic', ':formula', and returns 
 * a corresponding command
 * @retrurn a command corresponding to the attribute
 */
benchAttribute returns [ Command* smt_command = 0]
{
  Expr formula;  
  string logic; 
  SetBenchmarkStatusCommand::BenchmarkStatus b_status = SetBenchmarkStatusCommand::SMT_UNKNOWN;
}
  : C_LOGIC       logic = identifier                  { smt_command = new SetBenchmarkLogicCommand(logic);   }      
  | C_ASSUMPTION  formula = annotatedFormula          { smt_command = new AssertCommand(formula);   }       
  | C_FORMULA     formula = annotatedFormula          { smt_command = new CheckSatCommand(formula); }
  | C_STATUS      b_status = status                   { smt_command = new SetBenchmarkStatusCommand(b_status); }        
  | C_EXTRAPREDS  LPAREN (pred_symb_decl)+ RPAREN  
  | C_NOTES       STRING_LITERAL        
  | annotation
  ;

/**
 * Matches an identifier and returns a string.
 * @param check what kinds of check to do on the symbol
 * @return the id string
 */
identifier[DeclarationCheck check = CHECK_NONE] returns [std::string id]
  : x:IDENTIFIER { checkDeclation(x->getText(), check) }?
    { 
      id = x->getText(); 
    } 
    exception catch [antlr::SemanticException& ex] {
      switch (check) {
        case CHECK_DECLARED: rethrow(ex, "Symbol " + id + " not declared");
        case CHECK_UNDECLARED: rethrow(ex, "Symbol " + id + " already declared");
        default: throw ex;
      }          
    }    
  ;

/** 
 * Matches an annotated formula.
 * @return the expression representing the formula 
 */
annotatedFormula returns [CVC4::Expr formula] 
{ 
  Kind kind; 
  vector<Expr> children;
}
  :  formula = annotatedAtom 
  |  LPAREN kind = boolConnective annotatedFormulas[children] RPAREN { formula = mkExpr(kind, children);  }    
  ;

/**
 * Matches an annotated proposition atom, which is either a propositional atom 
 * or built of other atoms using a predicate symbol.  
 */
annotatedAtom returns [CVC4::Expr atom] 
  : atom = propositionalAtom  
  ;





 
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
 * Matches a predicate symbol. 
 */
pred_symb returns [std::string p]
  :  id:IDENTIFIER { p = id->getText(); }
  ;
  

/**
 * Matches a propositional atom. 
 */
propositionalAtom returns [CVC4::Expr atom]
{
  std::string p;
} 
   : p = pred_symb {isDeclared(p, SYM_VARIABLE)}? { atom = getVariable(p); }
      exception catch [antlr::SemanticException ex] {
        rethrow(ex, "Undeclared variable " + p);
      }   
   | TRUE          { atom = getTrueExpr(); }
   | FALSE         { atom = getFalseExpr(); }
   ;
      
/**
 * Matches on of the unary Boolean connectives.  
 */
boolConnective returns [CVC4::Kind kind]
  : NOT      { kind = CVC4::NOT;     } 
  | IMPLIES  { kind = CVC4::IMPLIES; }
  | AND      { kind = CVC4::AND;     }
  | OR       { kind = CVC4::OR;      }
  | XOR      { kind = CVC4::XOR;     }
  | IFF      { kind = CVC4::IFF;     }
  ;
    
annotatedFormulas[std::vector<Expr>& formulas]
{
  Expr f;
}
  : ( f = annotatedFormula { formulas.push_back(f); } )+
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
status returns [ SetBenchmarkStatusCommand::BenchmarkStatus status ]
  : SAT       { status = SetBenchmarkStatusCommand::SMT_SATISFIABLE;    }
  | UNSAT     { status = SetBenchmarkStatusCommand::SMT_UNSATISFIABLE;  }
  | UNKNOWN   { status = SetBenchmarkStatusCommand::SMT_UNKNOWN;        }
  ;