/* *******************                                                        */
/*  smt_parser.g
 ** Original author: dejan
 ** Major contributors: mdeters, cconway
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Parser for SMT-LIB input language.
 **/

header "post_include_hpp" {
#include "parser/antlr_parser.h"
#include "expr/command.h"
}

header "post_include_cpp" {
#include "expr/type.h"
#include "util/output.h"
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
  | EOF
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
 * Matches a sequence of benchmark attributes and returns a pointer to a
 * command sequence.
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
benchAttribute returns [Command* smt_command = 0]
{
  Expr formula;
  string logic;
  SetBenchmarkStatusCommand::BenchmarkStatus b_status = SetBenchmarkStatusCommand::SMT_UNKNOWN;
}
  : LOGIC_ATTR logic = identifier
    { smt_command = new SetBenchmarkLogicCommand(logic);   }
  | ASSUMPTION_ATTR formula = annotatedFormula
    { smt_command = new AssertCommand(formula);   }
  | FORMULA_ATTR formula = annotatedFormula
    { smt_command = new CheckSatCommand(formula); }
  | STATUS_ATTR b_status = status                   
    { smt_command = new SetBenchmarkStatusCommand(b_status); }        
  | EXTRAFUNS_ATTR LPAREN (functionDeclaration)+ RPAREN  
  | EXTRAPREDS_ATTR LPAREN (predicateDeclaration)+ RPAREN  
  | EXTRASORTS_ATTR LPAREN (sortDeclaration)+ RPAREN  
  | NOTES_ATTR STRING_LITERAL        
  | annotation
  ;

/**
 * Matches an annotated formula.
 * @return the expression representing the formula
 */
annotatedFormula returns [CVC4::Expr formula]
{
  Debug("parser") << "annotated formula: " << LT(1)->getText() << endl;
  Kind kind = UNDEFINED_KIND;
  vector<Expr> args; 
}
  : /* a built-in operator application */
    LPAREN kind = builtinOp annotatedFormulas[args] RPAREN 
    { args.size() >= minArity(kind) 
      && args.size() <= maxArity(kind) }?
    { formula = mkExpr(kind,args); }
      exception catch [antlr::SemanticException& ex] {
        stringstream ss;
        ss << "Expected ";
        if( args.size() < minArity(kind) ) {
          ss << "at least " << minArity(kind) << " ";
        } else {
          ss << "at most " << maxArity(kind) << " ";
        }
        ss << "arguments for operator '" << kind << "'. ";
        ss << "Found: " << args.size();
        rethrow(ex, ss.str());
      }

  | /* A non-built-in function application */
    { isFunction(LT(2)->getText()) }? 
    { Expr f; }
    LPAREN f = functionSymbol
    { args.push_back(f); }
    annotatedFormulas[args] RPAREN
    // TODO: check arity
    { formula = mkExpr(CVC4::APPLY,args); }

  | /* An ite expression */
    LPAREN (ITE | IF_THEN_ELSE) 
    { Expr test, trueExpr, falseExpr; }
    test = annotatedFormula 
    trueExpr = annotatedFormula
    falseExpr = annotatedFormula
    RPAREN
    { formula = mkExpr(CVC4::ITE, test, trueExpr, falseExpr); }

  | /* a parenthesized sub-formula */
    LPAREN formula = annotatedFormula RPAREN

  | /* a variable */
    { std::string name; }
    name = identifier[CHECK_DECLARED]
    { formula = getVariable(name); }

    /* constants */
  | TRUE          { formula = getTrueExpr(); }
  | FALSE         { formula = getFalseExpr(); }
    /* TODO: let, flet, quantifiers, arithmetic constants */
  ;

/**
 * Matches a sequence of annotaed formulas and puts them into the formulas
 * vector.
 * @param formulas the vector to fill with formulas
 */   
annotatedFormulas[std::vector<Expr>& formulas]
{
  Expr f;
}
  : ( f = annotatedFormula { formulas.push_back(f); } )+
  ;

/**
* Matches on of the unary Boolean connectives.
* @return the kind of the Bollean connective
*/
builtinOp returns [CVC4::Kind kind]
{
  Debug("parser") << "builtin: " << LT(1)->getText() << endl;
}
  : NOT      { kind = CVC4::NOT;     }
  | IMPLIES  { kind = CVC4::IMPLIES; }
  | AND      { kind = CVC4::AND;     }
  | OR       { kind = CVC4::OR;      }
  | XOR      { kind = CVC4::XOR;     }
  | IFF      { kind = CVC4::IFF;     }
  | EQUAL    { kind = CVC4::EQUAL;   }
    /* TODO: lt, gt, plus, minus, etc. */
  ;

/**
 * Matches a (possibly undeclared) predicate identifier (returning the string). 
 * @param check what kind of check to do with the symbol
 */
predicateName[DeclarationCheck check = CHECK_NONE] returns [std::string p]
  :  p = identifier[check]
  ;

/**
 * Matches a (possibly undeclared) function identifier (returning the string)
 * @param check what kind of check to do with the symbol
 */
functionName[DeclarationCheck check = CHECK_NONE] returns [std::string name]
  :  name = identifier[check,SYM_FUNCTION]
  ;

/**
 * Matches an previously declared function symbol (returning an Expr)
 */
functionSymbol returns [CVC4::Expr fun]
{ 
  string name;
}
  : name = functionName[CHECK_DECLARED]
    { fun = getFunction(name); }
  ;
  
/**
 * Matches an attribute name from the input (:attribute_name).
 */
attribute
  :  C_IDENTIFIER
  ;

/**
 * Matches the sort symbol, which can be an arbitrary identifier.
 * @param check the check to perform on the name
 */
sortName[DeclarationCheck check = CHECK_NONE] returns [std::string name] 
  : name = identifier[check,SYM_SORT] 
  ;

sortSymbol returns [const CVC4::Type* t]
{ 
  std::string name;
}
  : name = sortName { t = getSort(name); }
  ;

functionDeclaration
{
  string name;
  const Type* t;
  std::vector<const Type*> sorts;
}
  : LPAREN name = functionName[CHECK_UNDECLARED] 
      t = sortSymbol // require at least one sort
    { sorts.push_back(t); }
      sortList[sorts] RPAREN
    { t = functionType(sorts);
      mkVar(name, t); } 
  ;
              
/**
 * Matches the declaration of a predicate and declares it
 */
predicateDeclaration
{
  string p_name;
  std::vector<const Type*> p_sorts;
  const Type *t;
}
  : LPAREN p_name = predicateName[CHECK_UNDECLARED] sortList[p_sorts] RPAREN
    { t = predicateType(p_sorts);
      mkVar(p_name, t); } 
  ;

sortDeclaration 
{
  string name;
}
  : name = sortName[CHECK_UNDECLARED]
    { newSort(name); }
  ;
  
/**
 * Matches a sequence of sort symbols and fills them into the given vector.
 */
sortList[std::vector<const Type*>& sorts]
{
  const Type* t;
}
  : ( t = sortSymbol { sorts.push_back(t); })* 
  ;

/**
 * Matches the status of the benchmark, one of 'sat', 'unsat' or 'unknown'.
 */
status returns [ SetBenchmarkStatusCommand::BenchmarkStatus status ]
  : SAT       { status = SetBenchmarkStatusCommand::SMT_SATISFIABLE;    }
  | UNSAT     { status = SetBenchmarkStatusCommand::SMT_UNSATISFIABLE;  }
  | UNKNOWN   { status = SetBenchmarkStatusCommand::SMT_UNKNOWN;        }
  ;

/**
 * Matches an annotation, which is an attribute name, with an optional user
 */
annotation
  : attribute (USER_VALUE)?
  ;

/**
 * Matches an identifier and returns a string.
 * @param check what kinds of check to do on the symbol
 * @return the id string
 */
identifier[DeclarationCheck check = CHECK_NONE, 
           SymbolType type = SYM_VARIABLE] 
returns [std::string id]
{
  Debug("parser") << "identifier: " << LT(1)->getText() 
                  << " check? " << toString(check)
                  << " type? " << toString(type) << endl;
}
  : x:IDENTIFIER
    { id = x->getText(); }
    { checkDeclaration(id, check,type) }?
    exception catch [antlr::SemanticException& ex] {
      switch (check) {
        case CHECK_DECLARED: rethrow(ex, "Symbol " + id + " not declared");
        case CHECK_UNDECLARED: rethrow(ex, "Symbol " + id + " already declared");
        default: throw ex;
      }
    }
  ;

