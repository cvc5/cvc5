/* *******************                                           -*- C++ -*-  */
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
#include "util/command.h"
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
 * Matches an identifier and returns a string.
 * @param check what kinds of check to do on the symbol
 * @return the id string
 */
identifier[DeclarationCheck check = CHECK_NONE] returns [std::string id]
  : x:IDENTIFIER
    { id = x->getText(); }
    { checkDeclaration(id, check) }?
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
  |  LPAREN kind = boolConnective annotatedFormulas[children] RPAREN 
    { formula = mkExpr(kind, children);  }    
    /* TODO: let, flet, quantifiers */
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
 * Matches an annotated proposition atom, which is either a propositional atom 
 * or built of other atoms using a predicate symbol.  
 * @return expression representing the atom
 */
annotatedAtom returns [CVC4::Expr atom] 
{ 
  Kind kind;
  string predName;
  Expr pred;
  vector<Expr> children;
}
  : atom = propositionalAtom  
  | LPAREN kind = arithPredicate annotatedTerms[children] RPAREN
    { atom = mkExpr(kind,children); }
  | LPAREN pred = predicateSymbol
    { children.push_back(pred); }
    annotatedTerms[children] RPAREN
    { atom = mkExpr(CVC4::APPLY,children); }
  ;

/** 
 * Matches an annotated term.
 * @return the expression representing the term 
 */
annotatedTerm returns [CVC4::Expr term] 
{ 
  Kind kind;
  Expr f, t1, t2;
  vector<Expr> children;
}
  : term = baseTerm
  | LPAREN f = functionSymbol
    { children.push_back(f); }
    annotatedTerms[children] RPAREN 
    { term = mkExpr(CVC4::APPLY, children);  }
  // | LPAREN kind = arithFunction annotatedTerms[children] RPAREN
  //   { term = mkExpr(kind,children); }
  | LPAREN ITE 
    f = annotatedFormula 
    t1 = annotatedTerm 
    t2 = annotatedTerm RPAREN
    { term = mkExpr(CVC4::ITE, f, t1, t2); }
  ;

/**
 * Matches a sequence of annotaed formulas and puts them into the formulas
 * vector.
 * @param formulas the vector to fill with formulas
 */   
annotatedTerms[std::vector<Expr>& terms]
{
  Expr t;
}
  : ( t = annotatedFormula { terms.push_back(t); } )+
  ;

baseTerm returns [CVC4::Expr term]
{
  string name;
}
  : name = identifier[CHECK_DECLARED] { term = getVariable(name); }
    /* TODO: constants */
  ;

/**
* Matches on of the unary Boolean connectives.
* @return the kind of the Bollean connective
*/
boolConnective returns [CVC4::Kind kind]
  : NOT      { kind = CVC4::NOT;     }
  | IMPLIES  { kind = CVC4::IMPLIES; }
  | AND      { kind = CVC4::AND;     }
  | OR       { kind = CVC4::OR;      }
  | XOR      { kind = CVC4::XOR;     }
  | IFF      { kind = CVC4::IFF;     }
  ;

/**
 * Matches a propositional atom and returns the expression of the atom.
 * @return atom the expression of the atom
 */
propositionalAtom returns [CVC4::Expr atom]
{
  std::string p;
}
   : atom = predicateSymbol
   | TRUE          { atom = getTrueExpr(); }
   | FALSE         { atom = getFalseExpr(); }
   ;

arithPredicate returns [CVC4::Kind kind]
  : EQUAL { kind = CVC4::EQUAL; }
    /* TODO: lt, gt */
  ;

/**
 * Matches a (possibly undeclared) predicate identifier (returning the string). 
 * @param check what kind of check to do with the symbol
 */
predicateName[DeclarationCheck check = CHECK_NONE] returns [std::string p]
  :  p = identifier[check]
  ;

/**
 * Matches an previously declared predicate symbol (returning an Expr)
 */
predicateSymbol returns [CVC4::Expr pred]
{ 
  string name;
}
  : name = predicateName[CHECK_DECLARED]
    { pred = getVariable(name); }
  ;

/**
 * Matches a (possibly undeclared) function identifier (returning the string)
 * @param check what kind of check to do with the symbol
 */
functionName[DeclarationCheck check = CHECK_NONE] returns [std::string name]
  :  name = identifier[check]
  ;

/**
 * Matches an previously declared function symbol (returning an Expr)
 */
functionSymbol returns [CVC4::Expr fun]
{ 
  string name;
}
  : name = functionName[CHECK_DECLARED]
    { fun = getVariable(name); }
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
  : name = identifier[CHECK_NONE] 
    /* We pass CHECK_NONE to identifier, because identifier checks
       in the variable namespace, not the sorts namespace. */
    { checkSort(name,check) }?
  ;

functionDeclaration
{
  string name;
  vector<string> sorts;
}
  : LPAREN name = functionName[CHECK_UNDECLARED]
        sortNames[sorts, CHECK_DECLARED] RPAREN
    { newFunction(name, sorts); } 
  ;
              
/**
 * Matches the declaration of a predicate and declares it
 */
predicateDeclaration
{
  string p_name;
  vector<string> p_sorts;
}
  : LPAREN p_name = predicateName[CHECK_UNDECLARED] 
        sortNames[p_sorts, CHECK_DECLARED] RPAREN
    { newPredicate(p_name, p_sorts); } 
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
sortNames[std::vector<std::string>& sorts,DeclarationCheck check = CHECK_NONE]
{
  std::string name;
}
  : ( name = sortName[check] 
      { sorts.push_back(name); })* 
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

