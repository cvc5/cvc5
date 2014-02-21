/* *******************                                                        */
/*! \file Smt2.g
 ** \verbatim
 ** Original author: Christopher L. Conway
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): Dejan Jovanovic, Tianyi Liang, Andrew Reynolds, Francois Bobot
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Parser for SMT-LIB v2 input language
 **
 ** Parser for SMT-LIB v2 input language.
 **/

grammar Smt2;

options {
  // C output for antlr
  language = 'C';

  // Skip the default error handling, just break with exceptions
  // defaultErrorHandler = false;

  // Only lookahead of <= k requested (disable for LL* parsing)
  // Note that CVC4's BoundedTokenBuffer requires a fixed k !
  // If you change this k, change it also in smt2_input.cpp !
  k = 2;
}/* options */

@header {
/**
 ** This file is part of CVC4.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **/
}/* @header */

@lexer::includes {

/** This suppresses warnings about the redefinition of token symbols between
  * different parsers. The redefinitions should be harmless as long as no
  * client: (a) #include's the lexer headers for two grammars AND (b) uses the
  * token symbol definitions.
  */
#pragma GCC system_header

#if defined(CVC4_COMPETITION_MODE) && !defined(CVC4_SMTCOMP_APPLICATION_TRACK)
/* This improves performance by ~10 percent on big inputs.
 * This option is only valid if we know the input is ASCII (or some 8-bit encoding).
 * If we know the input is UTF-16, we can use ANTLR3_INLINE_INPUT_UTF16.
 * Otherwise, we have to let the lexer detect the encoding at runtime.
 */
#  define ANTLR3_INLINE_INPUT_ASCII
#  define ANTLR3_INLINE_INPUT_8BIT
#endif /* CVC4_COMPETITION_MODE && !CVC4_SMTCOMP_APPLICATION_TRACK */

#include "parser/antlr_tracing.h"

}/* @lexer::includes */

@lexer::postinclude {
#include <stdint.h>

#include "parser/smt2/smt2.h"
#include "parser/antlr_input.h"

using namespace CVC4;
using namespace CVC4::parser;

#undef PARSER_STATE
#define PARSER_STATE ((Smt2*)LEXER->super)
}/* @lexer::postinclude */

@parser::includes {
#include "expr/command.h"
#include "parser/parser.h"
#include "parser/antlr_tracing.h"

namespace CVC4 {
  class Expr;

  namespace parser {
    namespace smt2 {
      /**
       * Just exists to provide the uintptr_t constructor that ANTLR
       * requires.
       */
      struct myExpr : public CVC4::Expr {
        myExpr() : CVC4::Expr() {}
        myExpr(void*) : CVC4::Expr() {}
        myExpr(const Expr& e) : CVC4::Expr(e) {}
        myExpr(const myExpr& e) : CVC4::Expr(e) {}
      };/* struct myExpr */
    }/* CVC4::parser::smt2 namespace */
  }/* CVC4::parser namespace */
}/* CVC4 namespace */

}/* @parser::includes */

@parser::postinclude {

#include "expr/expr.h"
#include "expr/kind.h"
#include "expr/type.h"
#include "parser/antlr_input.h"
#include "parser/parser.h"
#include "parser/smt2/smt2.h"
#include "util/integer.h"
#include "util/output.h"
#include "util/rational.h"
#include "util/hash.h"
#include <vector>
#include <set>
#include <string>
#include <sstream>

using namespace CVC4;
using namespace CVC4::parser;

/* These need to be macros so they can refer to the PARSER macro, which
 * will be defined by ANTLR *after* this section. (If they were functions,
 * PARSER would be undefined.) */
#undef PARSER_STATE
#define PARSER_STATE ((Smt2*)PARSER->super)
#undef EXPR_MANAGER
#define EXPR_MANAGER PARSER_STATE->getExprManager()
#undef MK_EXPR
#define MK_EXPR EXPR_MANAGER->mkExpr
#undef MK_CONST
#define MK_CONST EXPR_MANAGER->mkConst
#define UNSUPPORTED PARSER_STATE->unimplementedFeature

static bool isClosed(Expr e, std::set<Expr>& free, std::hash_set<Expr, ExprHashFunction>& closedCache) {
  if(closedCache.find(e) != closedCache.end()) {
    return true;
  }

  if(e.getKind() == kind::FORALL || e.getKind() == kind::EXISTS || e.getKind() == kind::LAMBDA) {
    isClosed(e[1], free, closedCache);
    for(Expr::const_iterator i = e[0].begin(); i != e[0].end(); ++i) {
      free.erase(*i);
    }
  } else if(e.getKind() == kind::BOUND_VARIABLE) {
    free.insert(e);
    return false;
  } else {
    if(e.hasOperator()) {
      isClosed(e.getOperator(), free, closedCache);
    }
    for(Expr::const_iterator i = e.begin(); i != e.end(); ++i) {
      isClosed(*i, free, closedCache);
    }
  }

  if(free.empty()) {
    closedCache.insert(e);
    return true;
  } else {
    return false;
  }
}

static inline bool isClosed(Expr e, std::set<Expr>& free) {
  std::hash_set<Expr, ExprHashFunction> cache;
  return isClosed(e, free, cache);
}

}/* parser::postinclude */

/**
 * Parses an expression.
 * @return the parsed expression, or the Null Expr if we've reached the
 * end of the input
 */
parseExpr returns [CVC4::parser::smt2::myExpr expr]
@declarations {
  Expr expr2;
}
  : term[expr, expr2]
  | EOF
  ;

/**
 * Parses a command
 * @return the parsed command, or NULL if we've reached the end of the input
 */
parseCommand returns [CVC4::Command* cmd = NULL]
@declarations {
  std::string name;
}
  : LPAREN_TOK c = command RPAREN_TOK { $cmd = c; }

    /* This extended command has to be in the outermost production so that
     * the RPAREN_TOK is properly eaten and we are in a good state to read
     * the included file's tokens. */
  | LPAREN_TOK INCLUDE_TOK str[name,true] RPAREN_TOK
    { if(!PARSER_STATE->canIncludeFile()) {
        PARSER_STATE->parseError("include-file feature was disabled for this run.");
      }
      if(PARSER_STATE->strictModeEnabled()) {
        PARSER_STATE->parseError("Extended commands are not permitted while operating in strict compliance mode.");
      }
      PARSER_STATE->includeFile(name);
      // The command of the included file will be produced at the next parseCommand() call
      cmd = new EmptyCommand("include::" + name);
    }

  | EOF { $cmd = 0; }
  ;

/**
 * Parse the internal portion of the command, ignoring the surrounding
 * parentheses.
 */
command returns [CVC4::Command* cmd = NULL]
@declarations {
  std::string name;
  std::vector<std::string> names;
  Expr expr, expr2;
  Type t;
  std::vector<Expr> terms;
  std::vector<Type> sorts;
  std::vector<std::pair<std::string, Type> > sortedVarNames;
  SExpr sexpr;
}
  : /* set the logic */
    SET_LOGIC_TOK symbol[name,CHECK_NONE,SYM_SORT]
    { Debug("parser") << "set logic: '" << name << "'" << std::endl;
      if( PARSER_STATE->logicIsSet() ) {
        PARSER_STATE->parseError("Only one set-logic is allowed.");
      }
      PARSER_STATE->setLogic(name);
      $cmd = new SetBenchmarkLogicCommand(name); }
  | SET_INFO_TOK KEYWORD symbolicExpr[sexpr]
    { name = AntlrInput::tokenText($KEYWORD);
      if(name == ":cvc4-logic" || name == ":cvc4_logic") {
        PARSER_STATE->setLogic(sexpr.getValue());
      }
      PARSER_STATE->setInfo(name.c_str() + 1, sexpr);
      cmd = new SetInfoCommand(name.c_str() + 1, sexpr); }
  | /* get-info */
    GET_INFO_TOK KEYWORD
    { cmd = new GetInfoCommand(AntlrInput::tokenText($KEYWORD).c_str() + 1); }
  | /* set-option */
    SET_OPTION_TOK keyword[name] symbolicExpr[sexpr]
    { PARSER_STATE->setOption(name.c_str() + 1, sexpr);
      cmd = new SetOptionCommand(name.c_str() + 1, sexpr); }
  | /* get-option */
    GET_OPTION_TOK KEYWORD
    { cmd = new GetOptionCommand(AntlrInput::tokenText($KEYWORD).c_str() + 1); }
  | /* sort declaration */
    DECLARE_SORT_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    symbol[name,CHECK_UNDECLARED,SYM_SORT]
    { PARSER_STATE->checkUserSymbol(name); }
    n=INTEGER_LITERAL
    { Debug("parser") << "declare sort: '" << name
                      << "' arity=" << n << std::endl;
      unsigned arity = AntlrInput::tokenToUnsigned(n);
      if(arity == 0) {
        Type type = PARSER_STATE->mkSort(name);
        $cmd = new DeclareTypeCommand(name, 0, type);
      } else {
        Type type = PARSER_STATE->mkSortConstructor(name, arity);
        $cmd = new DeclareTypeCommand(name, arity, type);
      }
    }
  | /* sort definition */
    DEFINE_SORT_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    symbol[name,CHECK_UNDECLARED,SYM_SORT]
    { PARSER_STATE->checkUserSymbol(name); }
    LPAREN_TOK symbolList[names,CHECK_NONE,SYM_SORT] RPAREN_TOK
    { PARSER_STATE->pushScope(true);
      for(std::vector<std::string>::const_iterator i = names.begin(),
            iend = names.end();
          i != iend;
          ++i) {
        sorts.push_back(PARSER_STATE->mkSort(*i));
      }
    }
    sortSymbol[t,CHECK_DECLARED]
    { PARSER_STATE->popScope();
      // Do NOT call mkSort, since that creates a new sort!
      // This name is not its own distinct sort, it's an alias.
      PARSER_STATE->defineParameterizedType(name, sorts, t);
      $cmd = new DefineTypeCommand(name, sorts, t);
    }
  | /* function declaration */
    DECLARE_FUN_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    symbol[name,CHECK_UNDECLARED,SYM_VARIABLE]
    { PARSER_STATE->checkUserSymbol(name); }
    LPAREN_TOK sortList[sorts] RPAREN_TOK
    sortSymbol[t,CHECK_DECLARED]
    { Debug("parser") << "declare fun: '" << name << "'" << std::endl;
      if( sorts.size() > 0 ) {
        t = EXPR_MANAGER->mkFunctionType(sorts, t);
      }
      Expr func = PARSER_STATE->mkVar(name, t);
      $cmd = new DeclareFunctionCommand(name, func, t); }
  | /* function definition */
    DEFINE_FUN_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    symbol[name,CHECK_UNDECLARED,SYM_VARIABLE]
    { PARSER_STATE->checkUserSymbol(name); }
    LPAREN_TOK sortedVarList[sortedVarNames] RPAREN_TOK
    sortSymbol[t,CHECK_DECLARED]
    { /* add variables to parser state before parsing term */
      Debug("parser") << "define fun: '" << name << "'" << std::endl;
      if( sortedVarNames.size() > 0 ) {
        std::vector<CVC4::Type> sorts;
        sorts.reserve(sortedVarNames.size());
        for(std::vector<std::pair<std::string, CVC4::Type> >::const_iterator i =
              sortedVarNames.begin(), iend = sortedVarNames.end();
            i != iend;
            ++i) {
          sorts.push_back((*i).second);
        }
        t = EXPR_MANAGER->mkFunctionType(sorts, t);
      }
      PARSER_STATE->pushScope(true);
      for(std::vector<std::pair<std::string, CVC4::Type> >::const_iterator i =
            sortedVarNames.begin(), iend = sortedVarNames.end();
          i != iend;
          ++i) {
        terms.push_back(PARSER_STATE->mkBoundVar((*i).first, (*i).second));
      }
    }
    term[expr, expr2]
    { PARSER_STATE->popScope();
      // declare the name down here (while parsing term, signature
      // must not be extended with the name itself; no recursion
      // permitted)
      Expr func = PARSER_STATE->mkFunction(name, t, ExprManager::VAR_FLAG_DEFINED);
      $cmd = new DefineFunctionCommand(name, func, terms, expr);
    }
  | /* value query */
    GET_VALUE_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    ( LPAREN_TOK termList[terms,expr] RPAREN_TOK
      { $cmd = new GetValueCommand(terms); }
    | ~LPAREN_TOK
      { PARSER_STATE->parseError("The get-value command expects a list of terms.  Perhaps you forgot a pair of parentheses?"); } )
  | /* get-assignment */
    GET_ASSIGNMENT_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    { cmd = new GetAssignmentCommand(); }
  | /* assertion */
    ASSERT_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    term[expr, expr2]
    { cmd = new AssertCommand(expr); }
  | /* check-sat */
    CHECKSAT_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    ( term[expr, expr2]
      { if(PARSER_STATE->strictModeEnabled()) {
          PARSER_STATE->parseError("Extended commands (such as check-sat with an argument) are not permitted while operating in strict compliance mode.");
        }
      }
    | { expr = MK_CONST(bool(true)); } )
    { cmd = new CheckSatCommand(expr); }
  | /* get-assertions */
    GET_ASSERTIONS_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    { cmd = new GetAssertionsCommand(); }
  | /* get-proof */
    GET_PROOF_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    { cmd = new GetProofCommand(); }
  | /* get-unsat-core */
    GET_UNSAT_CORE_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    { cmd = new GetUnsatCoreCommand(); }
  | /* push */
    PUSH_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    ( k=INTEGER_LITERAL
      { unsigned n = AntlrInput::tokenToUnsigned(k);
        if(n == 0) {
          cmd = new EmptyCommand();
        } else if(n == 1) {
          PARSER_STATE->pushScope();
          cmd = new PushCommand();
        } else {
          CommandSequence* seq = new CommandSequence();
          do {
            PARSER_STATE->pushScope();
            Command* c = new PushCommand();
            c->setMuted(n > 1);
            seq->addCommand(c);
          } while(--n > 0);
          cmd = seq;
        }
      }
    | { if(PARSER_STATE->strictModeEnabled()) {
          PARSER_STATE->parseError("Strict compliance mode demands an integer to be provided to PUSH.  Maybe you want (push 1)?");
        } else {
          cmd = new PushCommand();
        }
      } )
  | POP_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    ( k=INTEGER_LITERAL
      { unsigned n = AntlrInput::tokenToUnsigned(k);
        if(n > PARSER_STATE->scopeLevel()) {
          PARSER_STATE->parseError("Attempted to pop above the top stack frame.");
        }
        if(n == 0) {
          cmd = new EmptyCommand();
        } else if(n == 1) {
          PARSER_STATE->popScope();
          cmd = new PopCommand();
        } else {
          CommandSequence* seq = new CommandSequence();
          do {
            PARSER_STATE->popScope();
            Command* c = new PopCommand();
            c->setMuted(n > 1);
            seq->addCommand(c);
          } while(--n > 0);
          cmd = seq;
        }
      }
    | { if(PARSER_STATE->strictModeEnabled()) {
          PARSER_STATE->parseError("Strict compliance mode demands an integer to be provided to POP.  Maybe you want (pop 1)?");
        } else {
          cmd = new PopCommand();
        }
      } )
  | EXIT_TOK
    { cmd = new QuitCommand(); }

    /* CVC4-extended SMT-LIB commands */
  | extendedCommand[cmd]
    { if(PARSER_STATE->strictModeEnabled()) {
        PARSER_STATE->parseError("Extended commands are not permitted while operating in strict compliance mode.");
      }
    }

    /* error handling */
  | SIMPLE_SYMBOL
    { std::string id = AntlrInput::tokenText($SIMPLE_SYMBOL);
      if(id == "benchmark") {
        PARSER_STATE->parseError("In SMT-LIBv2 mode, but got something that looks like SMT-LIBv1.  Use --lang smt1 for SMT-LIBv1.");
      } else {
        PARSER_STATE->parseError("expected SMT-LIBv2 command, got `" + id + "'.");
      }
    }
  ;

extendedCommand[CVC4::Command*& cmd]
@declarations {
  std::vector<CVC4::Datatype> dts;
  Type t;
  Expr e, e2;
  SExpr sexpr;
  std::string name;
  std::vector<std::string> names;
  std::vector<Expr> terms;
  std::vector<Type> sorts;
  std::vector<std::pair<std::string, Type> > sortedVarNames;
}
    /* Extended SMT-LIB set of commands syntax, not permitted in
     * --smtlib2 compliance mode. */
  : DECLARE_DATATYPES_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    { /* open a scope to keep the UnresolvedTypes contained */
      PARSER_STATE->pushScope(true); }
    LPAREN_TOK /* parametric sorts */
      ( symbol[name,CHECK_UNDECLARED,SYM_SORT] {
        sorts.push_back( PARSER_STATE->mkSort(name) ); }
      )*
    RPAREN_TOK
    LPAREN_TOK ( LPAREN_TOK datatypeDef[dts, sorts] RPAREN_TOK )+ RPAREN_TOK
    { PARSER_STATE->popScope();
      cmd = new DatatypeDeclarationCommand(PARSER_STATE->mkMutualDatatypeTypes(dts)); }
  | /* get model */
    GET_MODEL_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    { cmd = new GetModelCommand(); }
  | ECHO_TOK
    ( simpleSymbolicExpr[sexpr]
      { std::stringstream ss;
        ss << sexpr;
        cmd = new EchoCommand(ss.str());
      }
    | { cmd = new EchoCommand(); }
    )
  | rewriterulesCommand[cmd]

    /* Support some of Z3's extended SMT-LIB commands */

  | DECLARE_CONST_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    symbol[name,CHECK_UNDECLARED,SYM_VARIABLE]
    { PARSER_STATE->checkUserSymbol(name); }
    sortSymbol[t,CHECK_DECLARED]
    { Expr c = PARSER_STATE->mkVar(name, t);
      $cmd = new DeclareFunctionCommand(name, c, t); }

  | DECLARE_SORTS_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    { $cmd = new CommandSequence(); }
    LPAREN_TOK
    ( symbol[name,CHECK_UNDECLARED,SYM_SORT]
      { PARSER_STATE->checkUserSymbol(name);
        Type type = PARSER_STATE->mkSort(name);
        static_cast<CommandSequence*>($cmd)->addCommand(new DeclareTypeCommand(name, 0, type));
      }
    )+
    RPAREN_TOK

  | DECLARE_FUNS_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    { $cmd = new CommandSequence(); }
    LPAREN_TOK
    ( LPAREN_TOK symbol[name,CHECK_UNDECLARED,SYM_VARIABLE]
      { PARSER_STATE->checkUserSymbol(name); }
      nonemptySortList[sorts] RPAREN_TOK
      { Type t;
        if(sorts.size() > 1) {
          t = EXPR_MANAGER->mkFunctionType(sorts);
        } else {
          t = sorts[0];
        }
        Expr func = PARSER_STATE->mkVar(name, t);
        static_cast<CommandSequence*>($cmd)->addCommand(new DeclareFunctionCommand(name, func, t));
      }
    )+
    RPAREN_TOK

  | DECLARE_PREDS_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    { $cmd = new CommandSequence(); }
    LPAREN_TOK
    ( LPAREN_TOK symbol[name,CHECK_UNDECLARED,SYM_VARIABLE]
      { PARSER_STATE->checkUserSymbol(name); }
      sortList[sorts] RPAREN_TOK
      { Type t = EXPR_MANAGER->booleanType();
        if(sorts.size() > 0) {
          t = EXPR_MANAGER->mkFunctionType(sorts, t);
        }
        Expr func = PARSER_STATE->mkVar(name, t);
        static_cast<CommandSequence*>($cmd)->addCommand(new DeclareFunctionCommand(name, func, t));
      }
    )+
    RPAREN_TOK

  | DEFINE_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    ( symbol[name,CHECK_UNDECLARED,SYM_VARIABLE]
      { PARSER_STATE->checkUserSymbol(name); }
      term[e,e2]
      { Expr func = PARSER_STATE->mkFunction(name, e.getType(), ExprManager::VAR_FLAG_DEFINED);
        $cmd = new DefineFunctionCommand(name, func, e);
      }
    | LPAREN_TOK
      symbol[name,CHECK_UNDECLARED,SYM_VARIABLE]
      { PARSER_STATE->checkUserSymbol(name); }
      sortedVarList[sortedVarNames] RPAREN_TOK
      { /* add variables to parser state before parsing term */
        Debug("parser") << "define fun: '" << name << "'" << std::endl;
        PARSER_STATE->pushScope(true);
        for(std::vector<std::pair<std::string, CVC4::Type> >::const_iterator i =
              sortedVarNames.begin(), iend = sortedVarNames.end();
            i != iend;
            ++i) {
          terms.push_back(PARSER_STATE->mkBoundVar((*i).first, (*i).second));
        }
      }
      term[e,e2]
      { PARSER_STATE->popScope();
        // declare the name down here (while parsing term, signature
        // must not be extended with the name itself; no recursion
        // permitted)
        Type t = e.getType();
        if( sortedVarNames.size() > 0 ) {
          std::vector<CVC4::Type> sorts;
          sorts.reserve(sortedVarNames.size());
          for(std::vector<std::pair<std::string, CVC4::Type> >::const_iterator i =
                sortedVarNames.begin(), iend = sortedVarNames.end();
              i != iend;
              ++i) {
            sorts.push_back((*i).second);
          }
          t = EXPR_MANAGER->mkFunctionType(sorts, t);
        }
        Expr func = PARSER_STATE->mkFunction(name, t, ExprManager::VAR_FLAG_DEFINED);
        $cmd = new DefineFunctionCommand(name, func, terms, e);
      }
    )

  | SIMPLIFY_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    term[e,e2]
    { cmd = new SimplifyCommand(e); }
  ;

rewriterulesCommand[CVC4::Command*& cmd]
@declarations {
  std::vector<std::pair<std::string, Type> > sortedVarNames;
  std::vector<Expr> args, guards, heads, triggers;
  Expr head, body, expr, expr2, bvl;
  Kind kind;
}
  : /* rewrite rules */
    REWRITE_RULE_TOK
    LPAREN_TOK sortedVarList[sortedVarNames] RPAREN_TOK
    {
      kind = CVC4::kind::RR_REWRITE;
      PARSER_STATE->pushScope(true);
      for(std::vector<std::pair<std::string, CVC4::Type> >::const_iterator i =
            sortedVarNames.begin(), iend = sortedVarNames.end();
          i != iend;
          ++i) {
        args.push_back(PARSER_STATE->mkBoundVar((*i).first, (*i).second));
      }
      bvl = MK_EXPR(kind::BOUND_VAR_LIST, args);
    }
    LPAREN_TOK ( pattern[expr] { triggers.push_back( expr ); } )* RPAREN_TOK
    LPAREN_TOK (termList[guards,expr])? RPAREN_TOK
    term[head, expr2] term[body, expr2]
    {
      args.clear();
      args.push_back(head);
      args.push_back(body);
      /* triggers */
      if( !triggers.empty() ){
        expr2 = MK_EXPR(kind::INST_PATTERN_LIST, triggers);
        args.push_back(expr2);
      };
      expr = MK_EXPR(kind, args);
      args.clear();
      args.push_back(bvl);
      /* guards */
      switch( guards.size() ){
      case 0:
        args.push_back(MK_CONST(bool(true))); break;
      case 1:
        args.push_back(guards[0]); break;
      default:
        expr2 = MK_EXPR(kind::AND, guards);
        args.push_back(expr2); break;
      };
      args.push_back(expr);
      expr = MK_EXPR(CVC4::kind::REWRITE_RULE, args);
      cmd = new AssertCommand(expr); }
    /* propagation rule */
  | rewritePropaKind[kind]
    LPAREN_TOK sortedVarList[sortedVarNames] RPAREN_TOK
    {
      PARSER_STATE->pushScope(true);
      for(std::vector<std::pair<std::string, CVC4::Type> >::const_iterator i =
            sortedVarNames.begin(), iend = sortedVarNames.end();
          i != iend;
          ++i) {
        args.push_back(PARSER_STATE->mkBoundVar((*i).first, (*i).second));
      }
      bvl = MK_EXPR(kind::BOUND_VAR_LIST, args);
    }
    LPAREN_TOK ( pattern[expr] { triggers.push_back( expr ); } )* RPAREN_TOK
    LPAREN_TOK (termList[guards,expr])? RPAREN_TOK
    LPAREN_TOK (termList[heads,expr])? RPAREN_TOK
    term[body, expr2]
    {
      args.clear();
      /* heads */
      switch( heads.size() ){
      case 0:
        args.push_back(MK_CONST(bool(true))); break;
      case 1:
        args.push_back(heads[0]); break;
      default:
        expr2 = MK_EXPR(kind::AND, heads);
        args.push_back(expr2); break;
      };
      args.push_back(body);
      /* triggers */
      if( !triggers.empty() ){
        expr2 = MK_EXPR(kind::INST_PATTERN_LIST, triggers);
        args.push_back(expr2);
      };
      expr = MK_EXPR(kind, args);
      args.clear();
      args.push_back(bvl);
      /* guards */
      switch( guards.size() ){
      case 0:
        args.push_back(MK_CONST(bool(true))); break;
      case 1:
        args.push_back(guards[0]); break;
      default:
        expr2 = MK_EXPR(kind::AND, guards);
        args.push_back(expr2); break;
      };
      args.push_back(expr);
      expr = MK_EXPR(CVC4::kind::REWRITE_RULE, args);
      cmd = new AssertCommand(expr); }
  ;

rewritePropaKind[CVC4::Kind& kind]
  :
  REDUCTION_RULE_TOK    { $kind = CVC4::kind::RR_REDUCTION; }
  | PROPAGATION_RULE_TOK  { $kind = CVC4::kind::RR_DEDUCTION; }
  ;

pattern[CVC4::Expr& expr]
@declarations {
  std::vector<Expr> patexpr;
}
  : LPAREN_TOK termList[patexpr,expr] RPAREN_TOK
    {
      expr = MK_EXPR(kind::INST_PATTERN, patexpr);
    }
  ;

simpleSymbolicExprNoKeyword[CVC4::SExpr& sexpr]
@declarations {
  CVC4::Kind k;
  std::string s;
  std::vector<unsigned int> s_vec;
}
  : INTEGER_LITERAL
    { sexpr = SExpr(Integer(AntlrInput::tokenText($INTEGER_LITERAL))); }
  | DECIMAL_LITERAL
    { sexpr = SExpr(AntlrInput::tokenToRational($DECIMAL_LITERAL)); }
  | str[s,false]
    { sexpr = SExpr(s); }
//  | LPAREN_TOK STRCST_TOK
//      ( INTEGER_LITERAL {
//	    s_vec.push_back( atoi( AntlrInput::tokenText($INTEGER_LITERAL) ) + 65 );
//	  } )* RPAREN_TOK
//   {
//	sexpr = SExpr( MK_CONST( ::CVC4::String(s_vec) ) );
//	}
  | symbol[s,CHECK_NONE,SYM_SORT]
    { sexpr = SExpr(SExpr::Keyword(s)); }
  | tok=(ASSERT_TOK | CHECKSAT_TOK | DECLARE_FUN_TOK | DECLARE_SORT_TOK | DEFINE_FUN_TOK | DEFINE_SORT_TOK | GET_VALUE_TOK | GET_ASSIGNMENT_TOK | GET_ASSERTIONS_TOK | GET_PROOF_TOK | GET_UNSAT_CORE_TOK | EXIT_TOK | SET_LOGIC_TOK | SET_INFO_TOK | GET_INFO_TOK | SET_OPTION_TOK | GET_OPTION_TOK | PUSH_TOK | POP_TOK | DECLARE_DATATYPES_TOK | GET_MODEL_TOK | ECHO_TOK | REWRITE_RULE_TOK | REDUCTION_RULE_TOK | PROPAGATION_RULE_TOK | SIMPLIFY_TOK)
    { sexpr = SExpr(SExpr::Keyword(AntlrInput::tokenText($tok))); }
  | builtinOp[k]
    { std::stringstream ss;
      ss << Expr::setlanguage(CVC4::language::output::LANG_SMTLIB_V2) << EXPR_MANAGER->mkConst(k);
      sexpr = SExpr(ss.str());
    }
  ;

keyword[std::string& s]
  : KEYWORD
    { s = AntlrInput::tokenText($KEYWORD); }
  ;

simpleSymbolicExpr[CVC4::SExpr& sexpr]
  : simpleSymbolicExprNoKeyword[sexpr]
  | KEYWORD
    { sexpr = SExpr(AntlrInput::tokenText($KEYWORD)); }
  ;

symbolicExpr[CVC4::SExpr& sexpr]
@declarations {
  std::vector<SExpr> children;
}
  : simpleSymbolicExpr[sexpr]
  | LPAREN_TOK
    (symbolicExpr[sexpr] { children.push_back(sexpr); } )*
  	RPAREN_TOK
    { sexpr = SExpr(children); }
  ;

/**
 * Matches a term.
 * @return the expression representing the formula
 */
term[CVC4::Expr& expr, CVC4::Expr& expr2]
@init {
  Debug("parser") << "term: " << AntlrInput::tokenText(LT(1)) << std::endl;
  Kind kind = kind::NULL_EXPR;
  Expr op;
  std::string name;
  std::vector<Expr> args;
  SExpr sexpr;
  std::vector< std::pair<std::string, Type> > sortedVarNames;
  Expr f, f2;
  std::string attr;
  Expr attexpr;
  std::vector<Expr> patexprs;
  std::hash_set<std::string, StringHashFunction> names;
  std::vector< std::pair<std::string, Expr> > binders;
  Type type;
  std::string s;
}
  : /* a built-in operator application */
    LPAREN_TOK builtinOp[kind] termList[args,expr] RPAREN_TOK
    {
      if( kind == CVC4::kind::EQUAL &&
          args.size() > 0 &&
          args[0].getType() == EXPR_MANAGER->booleanType() ) {
        /* Use IFF for boolean equalities. */
        kind = CVC4::kind::IFF;
      }

      if( !PARSER_STATE->strictModeEnabled() &&
          (kind == CVC4::kind::AND || kind == CVC4::kind::OR) &&
          args.size() == 1) {
        /* Unary AND/OR can be replaced with the argument.
         * It just so happens expr should already be the only argument. */
        assert( expr == args[0] );
      } else if( CVC4::kind::isAssociative(kind) &&
                 args.size() > EXPR_MANAGER->maxArity(kind) ) {
    	/* Special treatment for associative operators with lots of children */
        expr = EXPR_MANAGER->mkAssociative(kind, args);
      } else if( kind == CVC4::kind::MINUS && args.size() == 1 ) {
        expr = MK_EXPR(CVC4::kind::UMINUS, args[0]);
      } else if( ( kind == CVC4::kind::XOR || kind == CVC4::kind::MINUS ) &&
                 args.size() > 2 ) {
        /* left-associative, but CVC4 internally only supports 2 args */
        expr = args[0];
        for(size_t i = 1; i < args.size(); ++i) {
          expr = MK_EXPR(kind, expr, args[i]);
        }
      } else if( kind == CVC4::kind::IMPLIES && args.size() > 2 ) {
        /* right-associative, but CVC4 internally only supports 2 args */
        expr = args[args.size() - 1];
        for(size_t i = args.size() - 1; i > 0;) {
          expr = MK_EXPR(kind, args[--i], expr);
        }
      } else if( ( kind == CVC4::kind::IFF || kind == CVC4::kind::EQUAL ||
                   kind == CVC4::kind::LT || kind == CVC4::kind::GT ||
                   kind == CVC4::kind::LEQ || kind == CVC4::kind::GEQ ) &&
                 args.size() > 2 ) {
        /* "chainable", but CVC4 internally only supports 2 args */
        expr = MK_EXPR(MK_CONST(Chain(kind)), args);
      } else if( PARSER_STATE->strictModeEnabled() && kind == CVC4::kind::ABS &&
                 args.size() == 1 && !args[0].getType().isInteger() ) {
        /* first, check that ABS is even defined in this logic */
        PARSER_STATE->checkOperator(kind, args.size());
        PARSER_STATE->parseError("abs can only be applied to Int, not Real, while in strict SMT-LIB compliance mode");
      } else {
        PARSER_STATE->checkOperator(kind, args.size());
        expr = MK_EXPR(kind, args);
      }
    }
  | LPAREN_TOK AS_TOK term[f, f2] sortSymbol[type, CHECK_DECLARED] RPAREN_TOK
    {
      if(f.getKind() == CVC4::kind::APPLY_CONSTRUCTOR && type.isDatatype()) {
        std::vector<CVC4::Expr> v;
        Expr e = f.getOperator();
        const DatatypeConstructor& dtc = Datatype::datatypeOf(e)[Datatype::indexOf(e)];
        v.push_back(MK_EXPR( CVC4::kind::APPLY_TYPE_ASCRIPTION,
                             MK_CONST(AscriptionType(dtc.getSpecializedConstructorType(type))), f.getOperator() ));
        v.insert(v.end(), f.begin(), f.end());
        expr = MK_EXPR(CVC4::kind::APPLY_CONSTRUCTOR, v);
      } else if(f.getKind() == CVC4::kind::EMPTYSET) {
        Debug("parser") << "Empty set encountered: " << f << " "
                          << f2 << " " << type <<  std::endl;
        // TODO: what is f2 about, should we add some assertions?
        expr = MK_CONST( ::CVC4::EmptySet(type) );
      } else {
        if(f.getType() != type) {
          PARSER_STATE->parseError("Type ascription not satisfied.");
        }
      }
    }
  | LPAREN_TOK quantOp[kind]
    LPAREN_TOK sortedVarList[sortedVarNames] RPAREN_TOK
    {
      PARSER_STATE->pushScope(true);
      for(std::vector<std::pair<std::string, CVC4::Type> >::const_iterator i =
            sortedVarNames.begin(), iend = sortedVarNames.end();
          i != iend;
          ++i) {
        args.push_back(PARSER_STATE->mkBoundVar((*i).first, (*i).second));
      }
      Expr bvl = MK_EXPR(kind::BOUND_VAR_LIST, args);
      args.clear();
      args.push_back(bvl);
    }
    term[f, f2] RPAREN_TOK
    {
      PARSER_STATE->popScope();
      switch(f.getKind()) {
      case CVC4::kind::RR_REWRITE:
      case CVC4::kind::RR_REDUCTION:
      case CVC4::kind::RR_DEDUCTION:
        if(kind == CVC4::kind::EXISTS) {
          PARSER_STATE->parseError("Use Exists instead of Forall for a rewrite rule.");
        }
        args.push_back(f2); // guards
        args.push_back(f); // rule
        expr = MK_EXPR(CVC4::kind::REWRITE_RULE, args);
        break;
      default:
        args.push_back(f);
        if(! f2.isNull()){
          args.push_back(f2);
        }
        expr = MK_EXPR(kind, args);
      }
    }
  | /* A non-built-in function application */
    LPAREN_TOK
    functionName[name, CHECK_DECLARED]
    { PARSER_STATE->checkFunctionLike(name);
      const bool isDefinedFunction =
        PARSER_STATE->isDefinedFunction(name);
      if(isDefinedFunction) {
        expr = PARSER_STATE->getFunction(name);
        kind = CVC4::kind::APPLY;
      } else {
        expr = PARSER_STATE->getVariable(name);
        Type t = expr.getType();
        if(t.isConstructor()) {
          kind = CVC4::kind::APPLY_CONSTRUCTOR;
        } else if(t.isSelector()) {
          kind = CVC4::kind::APPLY_SELECTOR;
        } else if(t.isTester()) {
          kind = CVC4::kind::APPLY_TESTER;
        } else {
          kind = CVC4::kind::APPLY_UF;
        }
      }
      args.push_back(expr);
    }
    termList[args,expr] RPAREN_TOK
    { Debug("parser") << "args has size " << args.size() << std::endl << "expr is " << expr << std::endl;
      for(std::vector<Expr>::iterator i = args.begin(); i != args.end(); ++i)
        Debug("parser") << "++ " << *i << std::endl;
      expr = MK_EXPR(kind, args); }

  | /* An indexed function application */
    LPAREN_TOK indexedFunctionName[op] termList[args,expr] RPAREN_TOK
    { expr = MK_EXPR(op, args);
      PARSER_STATE->checkOperator(expr.getKind(), args.size());
    }
  | /* a let binding */
    LPAREN_TOK LET_TOK LPAREN_TOK
    { PARSER_STATE->pushScope(true); }
    ( LPAREN_TOK symbol[name,CHECK_NONE,SYM_VARIABLE] term[expr, f2] RPAREN_TOK
      // this is a parallel let, so we have to save up all the contributions
      // of the let and define them only later on
      { if(names.count(name) == 1) {
          std::stringstream ss;
          ss << "warning: symbol `" << name << "' bound multiple times by let; the last binding will be used, shadowing earlier ones";
          PARSER_STATE->warning(ss.str());
        } else {
          names.insert(name);
        }
        binders.push_back(std::make_pair(name, expr)); } )+
    { // now implement these bindings
      for(std::vector< std::pair<std::string, Expr> >::iterator i = binders.begin(); i != binders.end(); ++i) {
        PARSER_STATE->defineVar((*i).first, (*i).second);
      }
    }
    RPAREN_TOK
    term[expr, f2]
    RPAREN_TOK
    { PARSER_STATE->popScope(); }

    /* a variable */
  | symbol[name,CHECK_DECLARED,SYM_VARIABLE]
    { const bool isDefinedFunction =
        PARSER_STATE->isDefinedFunction(name);
      if(PARSER_STATE->isAbstractValue(name)) {
        expr = PARSER_STATE->mkAbstractValue(name);
      } else if(isDefinedFunction) {
        expr = MK_EXPR(CVC4::kind::APPLY,
                       PARSER_STATE->getFunction(name));
      } else {
        expr = PARSER_STATE->getVariable(name);
        Type t = PARSER_STATE->getType(name);
        if(t.isConstructor() && ConstructorType(t).getArity() == 0) {
          // don't require parentheses, immediately turn it into an apply
          expr = MK_EXPR(CVC4::kind::APPLY_CONSTRUCTOR, expr);
        }
      }
    }

    /* attributed expressions */
  | LPAREN_TOK ATTRIBUTE_TOK term[expr, f2]
    ( attribute[expr, attexpr,attr]
      { if( attr == ":pattern" && ! attexpr.isNull()) {
          patexprs.push_back( attexpr );
        }
      }
    )+ RPAREN_TOK
    {
      if(attr == ":rewrite-rule") {
        Expr guard;
        Expr body;
        if(expr[1].getKind() == kind::IMPLIES ||
           expr[1].getKind() == kind::IFF ||
           expr[1].getKind() == kind::EQUAL) {
          guard = expr[0];
          body = expr[1];
        } else {
          guard = MK_CONST(bool(true));
          body = expr;
        }
        expr2 = guard;
        args.push_back(body[0]);
        args.push_back(body[1]);
        if(!f2.isNull()) {
          args.push_back(f2);
        }

        if     ( body.getKind()==kind::IMPLIES )    kind = kind::RR_DEDUCTION;
        else if( body.getKind()==kind::IFF )        kind = kind::RR_REDUCTION;
        else if( body.getKind()==kind::EQUAL )      kind = kind::RR_REWRITE;
        else PARSER_STATE->parseError("Error parsing rewrite rule.");

        expr = MK_EXPR( kind, args );
      } else if(! patexprs.empty()) {
        if( !f2.isNull() && f2.getKind()==kind::INST_PATTERN_LIST ){
          for( size_t i=0; i<f2.getNumChildren(); i++ ){
            patexprs.push_back( f2[i] );
          }
        }
        expr2 = MK_EXPR(kind::INST_PATTERN_LIST, patexprs);
      }else{
        expr2 = f2;
      }
    }
    /* constants */
  | INTEGER_LITERAL
    { expr = MK_CONST( AntlrInput::tokenToInteger($INTEGER_LITERAL) ); }

  | DECIMAL_LITERAL
    { // FIXME: This doesn't work because an SMT rational is not a
      // valid GMP rational string
      expr = MK_CONST( AntlrInput::tokenToRational($DECIMAL_LITERAL) ); }

  | LPAREN_TOK INDEX_TOK bvLit=SIMPLE_SYMBOL size=INTEGER_LITERAL RPAREN_TOK
    { if(AntlrInput::tokenText($bvLit).find("bv") == 0) {
        expr = MK_CONST( AntlrInput::tokenToBitvector($bvLit, $size) );
      } else {
        PARSER_STATE->parseError("Unexpected symbol `" + AntlrInput::tokenText($bvLit) + "'");
      }
    }

  | HEX_LITERAL
    { assert( AntlrInput::tokenText($HEX_LITERAL).find("#x") == 0 );
      std::string hexString = AntlrInput::tokenTextSubstr($HEX_LITERAL, 2);
      expr = MK_CONST( BitVector(hexString, 16) ); }

  | BINARY_LITERAL
    { assert( AntlrInput::tokenText($BINARY_LITERAL).find("#b") == 0 );
      std::string binString = AntlrInput::tokenTextSubstr($BINARY_LITERAL, 2);
      expr = MK_CONST( BitVector(binString, 2) ); }

  | str[s,false]
    { expr = MK_CONST( ::CVC4::String(s) ); }

  | EMPTYSET_TOK
    { expr = MK_CONST( ::CVC4::EmptySet()); }

    // NOTE: Theory constants go here
  ;

/**
 * Read attribute
 */
attribute[CVC4::Expr& expr,CVC4::Expr& retExpr, std::string& attr]
@init {
  SExpr sexpr;
  Expr patexpr;
  std::vector<Expr> patexprs;
  Expr e2;
  bool hasValue = false;
}
  : KEYWORD ( simpleSymbolicExprNoKeyword[sexpr] { hasValue = true; } )?
  {
    attr = AntlrInput::tokenText($KEYWORD);
    // EXPR_MANAGER->setNamedAttribute( expr, attr );
    if(attr == ":rewrite-rule") {
      if(hasValue) {
        std::stringstream ss;
        ss << "warning: Attribute " << attr << " does not take a value (ignoring)";
        PARSER_STATE->warning(ss.str());
      }
      // do nothing
    } else if(attr == ":axiom" || attr == ":conjecture") {
      if(hasValue) {
        std::stringstream ss;
        ss << "warning: Attribute " << attr << " does not take a value (ignoring)";
        PARSER_STATE->warning(ss.str());
      }
      std::string attr_name = attr;
      attr_name.erase( attr_name.begin() );
      Command* c = new SetUserAttributeCommand( attr_name, expr );
      c->setMuted(true);
      PARSER_STATE->preemptCommand(c);
    } else {
      PARSER_STATE->attributeNotSupported(attr);
    }
  }
  | ATTRIBUTE_PATTERN_TOK LPAREN_TOK ( term[patexpr, e2] { patexprs.push_back( patexpr ); }  )+ RPAREN_TOK
    {
      attr = std::string(":pattern");
      retExpr = MK_EXPR(kind::INST_PATTERN, patexprs);
    }
  | ATTRIBUTE_NO_PATTERN_TOK LPAREN_TOK term[patexpr, e2]+ RPAREN_TOK
    {
      attr = std::string(":no-pattern");
      PARSER_STATE->attributeNotSupported(attr);
    }
  | ATTRIBUTE_NAMED_TOK symbolicExpr[sexpr]
    {
      attr = std::string(":named");
      if(!sexpr.isKeyword()) {
        PARSER_STATE->parseError("improperly formed :named annotation");
      }
      std::string name = sexpr.getValue();
      PARSER_STATE->checkUserSymbol(name);
      // ensure expr is a closed subterm
      std::set<Expr> freeVars;
      if(!isClosed(expr, freeVars)) {
        assert(!freeVars.empty());
        std::stringstream ss;
        ss << ":named annotations can only name terms that are closed; this one contains free variables:";
        for(std::set<Expr>::const_iterator i = freeVars.begin(); i != freeVars.end(); ++i) {
          ss << " " << *i;
        }
        PARSER_STATE->parseError(ss.str());
      }
      // check that sexpr is a fresh function symbol, and reserve it
      PARSER_STATE->reserveSymbolAtAssertionLevel(name);
      // define it
      Expr func = PARSER_STATE->mkFunction(name, expr.getType());
      // bind name to expr with define-fun
      Command* c =
        new DefineNamedFunctionCommand(name, func, std::vector<Expr>(), expr);
      c->setMuted(true);
      PARSER_STATE->preemptCommand(c);
    }
  ;

/**
 * Matches a bit-vector operator (the ones parametrized by numbers)
 */
indexedFunctionName[CVC4::Expr& op]
  : LPAREN_TOK INDEX_TOK
    ( 'extract' n1=INTEGER_LITERAL n2=INTEGER_LITERAL
      { op = MK_CONST(BitVectorExtract(AntlrInput::tokenToUnsigned($n1),
                                       AntlrInput::tokenToUnsigned($n2))); }
    | 'repeat' n=INTEGER_LITERAL
      { op = MK_CONST(BitVectorRepeat(AntlrInput::tokenToUnsigned($n))); }
    | 'zero_extend' n=INTEGER_LITERAL
      { op = MK_CONST(BitVectorZeroExtend(AntlrInput::tokenToUnsigned($n))); }
    | 'sign_extend' n=INTEGER_LITERAL
      { op = MK_CONST(BitVectorSignExtend(AntlrInput::tokenToUnsigned($n))); }
    | 'rotate_left' n=INTEGER_LITERAL
      { op = MK_CONST(BitVectorRotateLeft(AntlrInput::tokenToUnsigned($n))); }
    | 'rotate_right' n=INTEGER_LITERAL
      { op = MK_CONST(BitVectorRotateRight(AntlrInput::tokenToUnsigned($n))); }
    | DIVISIBLE_TOK n=INTEGER_LITERAL
      { op = MK_CONST(Divisible(AntlrInput::tokenToUnsigned($n))); }
    | INT2BV_TOK n=INTEGER_LITERAL
      { op = MK_CONST(IntToBitVector(AntlrInput::tokenToUnsigned($n)));
        if(PARSER_STATE->strictModeEnabled()) {
          PARSER_STATE->parseError("bv2nat and int2bv are not part of SMT-LIB, and aren't available in SMT-LIB strict compliance mode");
        } }
    | badIndexedFunctionName
   )
    RPAREN_TOK
  ;

/**
 * Matches an erroneous indexed function name (and args) for better
 * error reporting.
 */
badIndexedFunctionName
@declarations {
  std::string name;
}
  : symbol[name,CHECK_NONE,SYM_VARIABLE] INTEGER_LITERAL+
      { PARSER_STATE->parseError(std::string("Unknown indexed function `") + name + "'"); }
  ;

/**
 * Matches a sequence of terms and puts them into the formulas
 * vector.
 * @param formulas the vector to fill with terms
 * @param expr an Expr reference for the elements of the sequence
 */
/* NOTE: We pass an Expr in here just to avoid allocating a fresh Expr every
 * time through this rule. */
termList[std::vector<CVC4::Expr>& formulas, CVC4::Expr& expr]
@declarations {
  Expr expr2;
}
  : ( term[expr, expr2] { formulas.push_back(expr); } )+
  ;

/**
 * Matches a string, and strips off the quotes.
 */
str[std::string& s, bool fsmtlib]
  : STRING_LITERAL
    { s = AntlrInput::tokenText($STRING_LITERAL);
      /* strip off the quotes */
      s = s.substr(1, s.size() - 2);
	  if(fsmtlib) {
		  /* handle SMT-LIB standard escapes '\\' and '\"' */
		  char* p_orig = strdup(s.c_str());
		  char *p = p_orig, *q = p_orig;
		  while(*q != '\0') {
			if(*q == '\\') {
			  ++q;
			  if(*q == '\\' || *q == '"') {
				*p++ = *q++;
			  } else {
				assert(*q != '\0');
				*p++ = '\\';
				*p++ = *q++;
			  }
			} else {
			  *p++ = *q++;
			}
		  }
		  *p = '\0';
		  s = p_orig;
		  free(p_orig);
	  }
    }
  ;

/**
 * Matches a builtin operator symbol and sets kind to its associated Expr kind.
 */
builtinOp[CVC4::Kind& kind]
@init {
  Debug("parser") << "builtin: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
  : NOT_TOK      { $kind = CVC4::kind::NOT;     }
  | IMPLIES_TOK  { $kind = CVC4::kind::IMPLIES; }
  | AND_TOK      { $kind = CVC4::kind::AND;     }
  | OR_TOK       { $kind = CVC4::kind::OR;      }
  | XOR_TOK      { $kind = CVC4::kind::XOR;     }
  | EQUAL_TOK    { $kind = CVC4::kind::EQUAL;   }
  | DISTINCT_TOK { $kind = CVC4::kind::DISTINCT; }
  | ITE_TOK      { $kind = CVC4::kind::ITE; }
  | GREATER_THAN_TOK
                 { $kind = CVC4::kind::GT; }
  | GREATER_THAN_EQUAL_TOK
                 { $kind = CVC4::kind::GEQ; }
  | LESS_THAN_EQUAL_TOK
                 { $kind = CVC4::kind::LEQ; }
  | LESS_THAN_TOK
                 { $kind = CVC4::kind::LT; }
  | PLUS_TOK     { $kind = CVC4::kind::PLUS; }
  | MINUS_TOK    { $kind = CVC4::kind::MINUS; }
  | STAR_TOK     { $kind = CVC4::kind::MULT; }
  | DIV_TOK      { $kind = CVC4::kind::DIVISION; }
  | INTS_DIV_TOK      { $kind = CVC4::kind::INTS_DIVISION; }
  | INTS_MOD_TOK      { $kind = CVC4::kind::INTS_MODULUS; }
  | ABS_TOK      { $kind = CVC4::kind::ABS; }
  | IS_INT_TOK   { $kind = CVC4::kind::IS_INTEGER; }
  | TO_INT_TOK   { $kind = CVC4::kind::TO_INTEGER; }
  | TO_REAL_TOK  { $kind = CVC4::kind::TO_REAL; }

  | SELECT_TOK   { $kind = CVC4::kind::SELECT; }
  | STORE_TOK    { $kind = CVC4::kind::STORE; }

  | CONCAT_TOK   { $kind = CVC4::kind::BITVECTOR_CONCAT; }
  | BVNOT_TOK   { $kind = CVC4::kind::BITVECTOR_NOT; }
  | BVAND_TOK   { $kind = CVC4::kind::BITVECTOR_AND; }
  | BVOR_TOK   { $kind = CVC4::kind::BITVECTOR_OR; }
  | BVNEG_TOK   { $kind = CVC4::kind::BITVECTOR_NEG; }
  | BVADD_TOK   { $kind = CVC4::kind::BITVECTOR_PLUS; }
  | BVMUL_TOK   { $kind = CVC4::kind::BITVECTOR_MULT; }
  | BVUDIV_TOK   { $kind = CVC4::kind::BITVECTOR_UDIV; }
  | BVUREM_TOK   { $kind = CVC4::kind::BITVECTOR_UREM; }
  | BVSHL_TOK     { $kind = CVC4::kind::BITVECTOR_SHL; }
  | BVLSHR_TOK     { $kind = CVC4::kind::BITVECTOR_LSHR; }
  | BVULT_TOK     { $kind = CVC4::kind::BITVECTOR_ULT; }
  | BVNAND_TOK     { $kind = CVC4::kind::BITVECTOR_NAND; }
  | BVNOR_TOK     { $kind = CVC4::kind::BITVECTOR_NOR; }
  | BVXOR_TOK     { $kind = CVC4::kind::BITVECTOR_XOR; }
  | BVXNOR_TOK     { $kind = CVC4::kind::BITVECTOR_XNOR; }
  | BVCOMP_TOK     { $kind = CVC4::kind::BITVECTOR_COMP; }
  | BVSUB_TOK     { $kind = CVC4::kind::BITVECTOR_SUB; }
  | BVSDIV_TOK     { $kind = CVC4::kind::BITVECTOR_SDIV; }
  | BVSREM_TOK     { $kind = CVC4::kind::BITVECTOR_SREM; }
  | BVSMOD_TOK     { $kind = CVC4::kind::BITVECTOR_SMOD; }
  | BVASHR_TOK     { $kind = CVC4::kind::BITVECTOR_ASHR; }
  | BVULE_TOK     { $kind = CVC4::kind::BITVECTOR_ULE; }
  | BVUGT_TOK     { $kind = CVC4::kind::BITVECTOR_UGT; }
  | BVUGE_TOK     { $kind = CVC4::kind::BITVECTOR_UGE; }
  | BVSLT_TOK     { $kind = CVC4::kind::BITVECTOR_SLT; }
  | BVSLE_TOK     { $kind = CVC4::kind::BITVECTOR_SLE; }
  | BVSGT_TOK     { $kind = CVC4::kind::BITVECTOR_SGT; }
  | BVSGE_TOK     { $kind = CVC4::kind::BITVECTOR_SGE; }

  | BV2NAT_TOK     { $kind = CVC4::kind::BITVECTOR_TO_NAT;
                     if(PARSER_STATE->strictModeEnabled()) {
                       PARSER_STATE->parseError("bv2nat and int2bv are not part of SMT-LIB, and aren't available in SMT-LIB strict compliance mode");
                     } }
  //NEW string
  //STRCONS_TOK    { $kind = CVC4::kind::STRING_CONCAT; }
  //STRREVCONS_TOK { $kind = CVC4::kind::STRING_CONCAT; }
  //STRHEAD_TOK    { $kind = CVC4::kind::STRING_CONCAT; }
  //STRTAIL_TOK    { $kind = CVC4::kind::STRING_CONCAT; }
  //STRLAST_TOK    { $kind = CVC4::kind::STRING_CONCAT; }
  //STRFIRST_TOK   { $kind = CVC4::kind::STRING_CONCAT; }
  //OLD string
  | STRCON_TOK     { $kind = CVC4::kind::STRING_CONCAT; }
  | STRLEN_TOK     { $kind = CVC4::kind::STRING_LENGTH; }
  | STRSUB_TOK     { $kind = CVC4::kind::STRING_SUBSTR; }
  | STRCTN_TOK     { $kind = CVC4::kind::STRING_STRCTN; }
  | STRCAT_TOK     { $kind = CVC4::kind::STRING_CHARAT; }
  | STRIDOF_TOK    { $kind = CVC4::kind::STRING_STRIDOF; }
  | STRREPL_TOK    { $kind = CVC4::kind::STRING_STRREPL; }
  | STRPREF_TOK    { $kind = CVC4::kind::STRING_PREFIX; }
  | STRSUFF_TOK    { $kind = CVC4::kind::STRING_SUFFIX; }
  | SITOS_TOK      { $kind = CVC4::kind::STRING_ITOS; }
  | SSTOI_TOK      { $kind = CVC4::kind::STRING_STOI; }
  | STRINRE_TOK    { $kind = CVC4::kind::STRING_IN_REGEXP; }
  | STRTORE_TOK    { $kind = CVC4::kind::STRING_TO_REGEXP; }
  | RECON_TOK      { $kind = CVC4::kind::REGEXP_CONCAT; }
  | REOR_TOK       { $kind = CVC4::kind::REGEXP_OR; }
  | REINTER_TOK    { $kind = CVC4::kind::REGEXP_INTER; }
  | RESTAR_TOK     { $kind = CVC4::kind::REGEXP_STAR; }
  | REPLUS_TOK     { $kind = CVC4::kind::REGEXP_PLUS; }
  | REOPT_TOK      { $kind = CVC4::kind::REGEXP_OPT; }
  | RERANGE_TOK    { $kind = CVC4::kind::REGEXP_RANGE; }
  | SETUNION_TOK  { $kind = CVC4::kind::UNION; }
  | SETINT_TOK    { $kind = CVC4::kind::INTERSECTION; }
  | SETMINUS_TOK  { $kind = CVC4::kind::SETMINUS; }
  | SETSUB_TOK    { $kind = CVC4::kind::SUBSET; }
  | SETIN_TOK     { $kind = CVC4::kind::IN; }
  | SETSINGLETON_TOK { $kind = CVC4::kind::SET_SINGLETON; }

  // NOTE: Theory operators go here
  ;

quantOp[CVC4::Kind& kind]
@init {
  Debug("parser") << "quant: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
  : EXISTS_TOK    { $kind = CVC4::kind::EXISTS; }
  | FORALL_TOK    { $kind = CVC4::kind::FORALL; }
  ;

/**
 * Matches a (possibly undeclared) function symbol (returning the string)
 * @param check what kind of check to do with the symbol
 */
functionName[std::string& name, CVC4::parser::DeclarationCheck check]
  : symbol[name,check,SYM_VARIABLE]
  ;

/**
 * Matches an previously declared function symbol (returning an Expr)
 */
functionSymbol[CVC4::Expr& fun]
@declarations {
	std::string name;
}
  : functionName[name,CHECK_DECLARED]
    { PARSER_STATE->checkFunctionLike(name);
      fun = PARSER_STATE->getVariable(name); }
  ;

/**
 * Matches a sequence of sort symbols and fills them into the given
 * vector.
 */
sortList[std::vector<CVC4::Type>& sorts]
@declarations {
  Type t;
}
  : ( sortSymbol[t,CHECK_DECLARED] { sorts.push_back(t); } )*
  ;

nonemptySortList[std::vector<CVC4::Type>& sorts]
@declarations {
  Type t;
}
  : ( sortSymbol[t,CHECK_DECLARED] { sorts.push_back(t); } )+
  ;

/**
 * Matches a sequence of (variable,sort) symbol pairs and fills them
 * into the given vector.
 */
sortedVarList[std::vector<std::pair<std::string, CVC4::Type> >& sortedVars]
@declarations {
  std::string name;
  Type t;
}
  : ( LPAREN_TOK symbol[name,CHECK_NONE,SYM_VARIABLE] sortSymbol[t,CHECK_DECLARED] RPAREN_TOK
      { sortedVars.push_back(make_pair(name, t)); }
    )*
  ;

/**
 * Matches the sort symbol, which can be an arbitrary symbol.
 * @param check the check to perform on the name
 */
sortName[std::string& name, CVC4::parser::DeclarationCheck check]
  : symbol[name,check,SYM_SORT]
  ;

sortSymbol[CVC4::Type& t, CVC4::parser::DeclarationCheck check]
@declarations {
  std::string name;
  std::vector<CVC4::Type> args;
  std::vector<uint64_t> numerals;
}
  : sortName[name,CHECK_NONE]
  	{
  	  if( check == CHECK_DECLARED || PARSER_STATE->isDeclared(name, SYM_SORT) ){
  	    t = PARSER_STATE->getSort(name);
  	  }else{
  	    t = PARSER_STATE->mkUnresolvedType(name);
  	  }
  	}
  | LPAREN_TOK INDEX_TOK symbol[name,CHECK_NONE,SYM_SORT] nonemptyNumeralList[numerals] RPAREN_TOK
    {
      if( name == "BitVec" ) {
        if( numerals.size() != 1 ) {
          PARSER_STATE->parseError("Illegal bitvector type.");
        }
        if(numerals.front() == 0) {
          PARSER_STATE->parseError("Illegal bitvector size: 0");
        }
        t = EXPR_MANAGER->mkBitVectorType(numerals.front());
      } else {
        std::stringstream ss;
        ss << "unknown indexed symbol `" << name << "'";
        PARSER_STATE->parseError(ss.str());
      }
    }
  | LPAREN_TOK symbol[name,CHECK_NONE,SYM_SORT] sortList[args] RPAREN_TOK
    {
      if(name == "Array") {
        if(args.size() != 2) {
          PARSER_STATE->parseError("Illegal array type.");
        }
        t = EXPR_MANAGER->mkArrayType( args[0], args[1] );
      } else if(name == "Set") {
        if(args.size() != 1) {
          PARSER_STATE->parseError("Illegal set type.");
        }
        t = EXPR_MANAGER->mkSetType( args[0] );
      } else if(check == CHECK_DECLARED ||
                PARSER_STATE->isDeclared(name, SYM_SORT)) {
        t = PARSER_STATE->getSort(name, args);
      } else {
        // make unresolved type
        if(args.empty()) {
          t = PARSER_STATE->mkUnresolvedType(name);
          Debug("parser-param") << "param: make unres type " << name << std::endl;
        } else {
          t = PARSER_STATE->mkUnresolvedTypeConstructor(name,args);
          t = SortConstructorType(t).instantiate( args );
          Debug("parser-param") << "param: make unres param type " << name << " " << args.size() << " "
                                << PARSER_STATE->getArity( name ) << std::endl;
        }
      }
    }
  ;

/**
 * Matches a list of symbols, with check and type arguments as for the
 * symbol[] rule below.
 */
symbolList[std::vector<std::string>& names,
           CVC4::parser::DeclarationCheck check,
           CVC4::parser::SymbolType type]
@declarations {
  std::string id;
}
  : ( symbol[id,check,type] { names.push_back(id); } )*
  ;

/**
 * Matches an symbol and sets the string reference parameter id.
 * @param id string to hold the symbol
 * @param check what kinds of check to do on the symbol
 * @param type the intended namespace for the symbol
 */
symbol[std::string& id,
       CVC4::parser::DeclarationCheck check,
       CVC4::parser::SymbolType type]
  : SIMPLE_SYMBOL
    { id = AntlrInput::tokenText($SIMPLE_SYMBOL);
      if(!PARSER_STATE->isAbstractValue(id)) {
        // if an abstract value, SmtEngine handles declaration
        PARSER_STATE->checkDeclaration(id, check, type);
      }
    }
  | QUOTED_SYMBOL
    { id = AntlrInput::tokenText($QUOTED_SYMBOL);
      /* strip off the quotes */
      id = id.substr(1, id.size() - 2);
      if(!PARSER_STATE->isAbstractValue(id)) {
        // if an abstract value, SmtEngine handles declaration
        PARSER_STATE->checkDeclaration(id, check, type);
      }
    }
  | UNTERMINATED_QUOTED_SYMBOL EOF
    { PARSER_STATE->unexpectedEOF("unterminated |quoted| symbol"); }
  ;

/**
 * Matches a nonempty list of numerals.
 * @param numerals the (empty) vector to house the numerals.
 */
nonemptyNumeralList[std::vector<uint64_t>& numerals]
  : ( INTEGER_LITERAL
      { numerals.push_back(AntlrInput::tokenToUnsigned($INTEGER_LITERAL)); }
    )+
  ;

/**
 * Parses a datatype definition
 */
datatypeDef[std::vector<CVC4::Datatype>& datatypes, std::vector< CVC4::Type >& params]
@init {
  std::string id;
}
    /* This really needs to be CHECK_NONE, or mutually-recursive
     * datatypes won't work, because this type will already be
     * "defined" as an unresolved type; don't worry, we check
     * below. */
  : symbol[id,CHECK_NONE,SYM_SORT] { PARSER_STATE->pushScope(true); }
   /* ( '[' symbol[id2,CHECK_UNDECLARED,SYM_SORT] {
        t = PARSER_STATE->mkSort(id2);
        params.push_back( t );
      }
      ( symbol[id2,CHECK_UNDECLARED,SYM_SORT] {
        t = PARSER_STATE->mkSort(id2);
        params.push_back( t ); }
      )* ']'
    )?*/ //AJR: this isn't necessary if we use z3's style
    { datatypes.push_back(Datatype(id,params));
      if(!PARSER_STATE->isUnresolvedType(id)) {
        // if not unresolved, must be undeclared
        PARSER_STATE->checkDeclaration(id, CHECK_UNDECLARED, SYM_SORT);
      }
    }
    ( LPAREN_TOK constructorDef[datatypes.back()] RPAREN_TOK )+
    { PARSER_STATE->popScope(); }
  ;

/**
 * Parses a constructor defintion for type
 */
constructorDef[CVC4::Datatype& type]
@init {
  std::string id;
  CVC4::DatatypeConstructor* ctor = NULL;
}
  : symbol[id,CHECK_UNDECLARED,SYM_SORT]
    { // make the tester
      std::string testerId("is-");
      testerId.append(id);
      PARSER_STATE->checkDeclaration(testerId, CHECK_UNDECLARED, SYM_SORT);
      ctor = new CVC4::DatatypeConstructor(id, testerId);
    }
    ( LPAREN_TOK selector[*ctor] RPAREN_TOK )*
    { // make the constructor
      type.addConstructor(*ctor);
      Debug("parser-idt") << "constructor: " << id.c_str() << std::endl;
      delete ctor;
    }
  ;

selector[CVC4::DatatypeConstructor& ctor]
@init {
  std::string id;
  Type t, t2;
}
  : symbol[id,CHECK_UNDECLARED,SYM_SORT] sortSymbol[t,CHECK_NONE]
    { ctor.addArg(id, t);
      Debug("parser-idt") << "selector: " << id.c_str()
                          << " of type " << t << std::endl;
    }
  ;

// Base SMT-LIB tokens
ASSERT_TOK : 'assert';
CHECKSAT_TOK : 'check-sat';
DECLARE_FUN_TOK : 'declare-fun';
DECLARE_SORT_TOK : 'declare-sort';
DEFINE_FUN_TOK : 'define-fun';
DEFINE_SORT_TOK : 'define-sort';
GET_VALUE_TOK : 'get-value';
GET_ASSIGNMENT_TOK : 'get-assignment';
GET_ASSERTIONS_TOK : 'get-assertions';
GET_PROOF_TOK : 'get-proof';
GET_UNSAT_CORE_TOK : 'get-unsat-core';
EXIT_TOK : 'exit';
ITE_TOK : 'ite';
LET_TOK : 'let';
ATTRIBUTE_TOK : '!';
LPAREN_TOK : '(';
RPAREN_TOK : ')';
INDEX_TOK : '_';
SET_LOGIC_TOK : 'set-logic';
SET_INFO_TOK : 'set-info';
GET_INFO_TOK : 'get-info';
SET_OPTION_TOK : 'set-option';
GET_OPTION_TOK : 'get-option';
PUSH_TOK : 'push';
POP_TOK : 'pop';
AS_TOK : 'as';

// extended commands
DECLARE_DATATYPES_TOK : 'declare-datatypes';
GET_MODEL_TOK : 'get-model';
ECHO_TOK : 'echo';
REWRITE_RULE_TOK : 'assert-rewrite';
REDUCTION_RULE_TOK : 'assert-reduction';
PROPAGATION_RULE_TOK : 'assert-propagation';
DECLARE_SORTS_TOK : 'declare-sorts';
DECLARE_FUNS_TOK : 'declare-funs';
DECLARE_PREDS_TOK : 'declare-preds';
DEFINE_TOK : 'define';
DECLARE_CONST_TOK : 'declare-const';
SIMPLIFY_TOK : 'simplify';
INCLUDE_TOK : 'include';

// attributes
ATTRIBUTE_PATTERN_TOK : ':pattern';
ATTRIBUTE_NO_PATTERN_TOK : ':no-pattern';
ATTRIBUTE_NAMED_TOK : ':named';

// operators (NOTE: theory symbols go here)
AMPERSAND_TOK     : '&';
AND_TOK           : 'and';
AT_TOK            : '@';
DISTINCT_TOK      : 'distinct';
DIV_TOK           : '/';
EQUAL_TOK         : '=';
EXISTS_TOK        : 'exists';
FORALL_TOK        : 'forall';
GREATER_THAN_TOK  : '>';
GREATER_THAN_EQUAL_TOK  : '>=';
IMPLIES_TOK       : '=>';
IS_INT_TOK        : 'is_int';
LESS_THAN_TOK     : '<';
LESS_THAN_EQUAL_TOK     : '<=';
MINUS_TOK         : '-';
NOT_TOK           : 'not';
OR_TOK            : 'or';
// PERCENT_TOK       : '%';
PLUS_TOK          : '+';
POUND_TOK         : '#';
SELECT_TOK        : 'select';
STAR_TOK          : '*';
STORE_TOK         : 'store';
// TILDE_TOK         : '~';
TO_INT_TOK        : 'to_int';
TO_REAL_TOK       : 'to_real';
XOR_TOK           : 'xor';

INTS_DIV_TOK : 'div';
INTS_MOD_TOK : 'mod';
ABS_TOK : 'abs';

DIVISIBLE_TOK : 'divisible';

CONCAT_TOK : 'concat';
BVNOT_TOK : 'bvnot';
BVAND_TOK : 'bvand';
BVOR_TOK : 'bvor';
BVNEG_TOK : 'bvneg';
BVADD_TOK : 'bvadd';
BVMUL_TOK : 'bvmul';
BVUDIV_TOK : 'bvudiv';
BVUREM_TOK : 'bvurem';
BVSHL_TOK : 'bvshl';
BVLSHR_TOK : 'bvlshr';
BVULT_TOK : 'bvult';
BVNAND_TOK : 'bvnand';
BVNOR_TOK : 'bvnor';
BVXOR_TOK : 'bvxor';
BVXNOR_TOK : 'bvxnor';
BVCOMP_TOK : 'bvcomp';
BVSUB_TOK : 'bvsub';
BVSDIV_TOK : 'bvsdiv';
BVSREM_TOK : 'bvsrem';
BVSMOD_TOK : 'bvsmod';
BVASHR_TOK : 'bvashr';
BVULE_TOK : 'bvule';
BVUGT_TOK : 'bvugt';
BVUGE_TOK : 'bvuge';
BVSLT_TOK : 'bvslt';
BVSLE_TOK : 'bvsle';
BVSGT_TOK : 'bvsgt';
BVSGE_TOK : 'bvsge';
BV2NAT_TOK : 'bv2nat';
INT2BV_TOK : 'int2bv';

//STRING
//NEW
//STRCONS_TOK : 'str.cons';
//STRREVCONS_TOK : 'str.revcons';
//STRHEAD_TOK : 'str.head';
//STRTAIL_TOK : 'str.tail';
//STRLAST_TOK : 'str.last';
//STRFIRST_TOK : 'str.first';
//OLD
STRCON_TOK : 'str.++';
STRLEN_TOK : 'str.len';
STRSUB_TOK : 'str.substr' ;
STRCTN_TOK : 'str.contain' ;
STRCAT_TOK : 'str.at' ;
STRIDOF_TOK : 'str.indexof' ;
STRREPL_TOK : 'str.replace' ;
STRPREF_TOK : 'str.prefixof' ;
STRSUFF_TOK : 'str.suffixof' ;
SITOS_TOK : 'int.to.str' ;
SSTOI_TOK : 'str.to.int' ;
STRINRE_TOK : 'str.in.re';
STRTORE_TOK : 'str.to.re';
RECON_TOK : 're.++';
REOR_TOK : 're.or';
REINTER_TOK : 're.itr';
RESTAR_TOK : 're.*';
REPLUS_TOK : 're.+';
REOPT_TOK : 're.opt';
RERANGE_TOK : 're.range';

SETUNION_TOK: 'union';
SETINT_TOK: 'intersection';
SETMINUS_TOK: 'setminus';
SETSUB_TOK: 'subseteq';
SETIN_TOK: 'in';
SETSINGLETON_TOK: 'setenum';
EMPTYSET_TOK: 'emptyset';

/**
 * A sequence of printable ASCII characters (except backslash) that starts
 * and ends with | and does not otherwise contain |.
 *
 * You shouldn't generally use this in parser rules, as the |quoting|
 * will be part of the token text.  Use the symbol[] parser rule instead.
 */
QUOTED_SYMBOL
  : '|' ~('|' | '\\')* '|'
  ;
UNTERMINATED_QUOTED_SYMBOL
  : '|' ~('|' | '\\')*
  ;

/**
 * Matches a keyword from the input. A keyword is a simple symbol prefixed
 * with a colon.
 */
KEYWORD
  : ':' (ALPHA | DIGIT | SYMBOL_CHAR)+
  ;

/**
 * Matches a "simple" symbol: a non-empty sequence of letters, digits and
 * the characters + - / * = % ? ! . $ ~ & ^ < > @ that does not start with a
 * digit, and is not the special reserved symbols '!' or '_'.
 */
SIMPLE_SYMBOL
  : (ALPHA | SYMBOL_CHAR) (ALPHA | DIGIT | SYMBOL_CHAR)+
  | ALPHA
  | SYMBOL_CHAR_NOUNDERSCORE_NOATTRIBUTE
  ;

/**
 * Matches and skips whitespace in the input.
 */
WHITESPACE
  : (' ' | '\t' | '\f' | '\r' | '\n')+ { SKIP(); }
  ;

/**
 * Matches an integer constant from the input (non-empty sequence of
 * digits, with no leading zeroes).
 */
INTEGER_LITERAL
  : NUMERAL
  ;

/**
 * Match an integer constant. In non-strict mode, this is any sequence
 * of digits. In strict mode, non-zero integers can't have leading
 * zeroes.
 */
fragment NUMERAL
@init {
  char *start = (char*) GETCHARINDEX();
}
  : DIGIT+
    { Debug("parser-extra") << "NUMERAL: "
       << (uintptr_t)start << ".." << GETCHARINDEX()
       << " strict? " << (bool)(PARSER_STATE->strictModeEnabled())
       << " ^0? " << (bool)(*start == '0')
       << " len>1? " << (bool)(start < (char*)(GETCHARINDEX() - 1))
       << std::endl; }
    { !PARSER_STATE->strictModeEnabled() ||
      *start != '0' ||
      start == (char*)(GETCHARINDEX() - 1) }?
  ;

/**
 * Matches a decimal constant from the input.
 */
DECIMAL_LITERAL
  : NUMERAL '.' DIGIT+
  ;

/**
 * Matches a hexadecimal constant.
 */
HEX_LITERAL
  : '#x' HEX_DIGIT+
  ;

/**
 * Matches a binary constant.
 */
BINARY_LITERAL
  : '#b' ('0' | '1')+
  ;

/**
 * Matches a double quoted string literal.  Escaping is supported, and
 * escape character '\' has to be escaped.
 *
 * You shouldn't generally use this in parser rules, as the quotes
 * will be part of the token text.  Use the str[] parser rule instead.
 */
STRING_LITERAL
  : '"' ('\\' . | ~('\\' | '"'))* '"'
  ;

/**
 * Matches the comments and ignores them
 */
COMMENT
  : ';' (~('\n' | '\r'))* { SKIP(); }
  ;

/**
 * Matches any letter ('a'-'z' and 'A'-'Z').
 */
fragment
ALPHA
  : 'a'..'z'
  | 'A'..'Z'
  ;

/**
 * Matches the digits (0-9)
 */
fragment DIGIT : '0'..'9';

fragment HEX_DIGIT : DIGIT | 'a'..'f' | 'A'..'F';

/**
 * Matches the characters that may appear as a one-character "symbol"
 * (which excludes _ and !, which are reserved words in SMT-LIB).
 */
fragment SYMBOL_CHAR_NOUNDERSCORE_NOATTRIBUTE
  : '+' | '-' | '/' | '*' | '=' | '%' | '?' | '.' | '$' | '~'
  | '&' | '^' | '<' | '>' | '@'
  ;

/**
 * Matches the characters that may appear in a "symbol" (i.e., an identifier)
 */
fragment SYMBOL_CHAR
  : SYMBOL_CHAR_NOUNDERSCORE_NOATTRIBUTE | '_' | '!'
  ;
