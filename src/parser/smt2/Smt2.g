/* *******************                                                        */
/*! \file Smt2.g
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
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
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.
 **/
}/* @header */

@lexer::includes {

// This should come immediately after #include <antlr3.h> in the generated
// files. See the documentation in "parser/antlr_undefines.h" for more details.
#include "parser/antlr_undefines.h"

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

// This should come immediately after #include <antlr3.h> in the generated
// files. See the documentation in "parser/antlr_undefines.h" for more details.
#include "parser/antlr_undefines.h"

#include <memory>

#include "parser/parser.h"
#include "parser/antlr_tracing.h"
#include "smt/command.h"

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

#include <set>
#include <sstream>
#include <string>
#include <unordered_set>
#include <vector>

#include "base/output.h"
#include "expr/expr.h"
#include "expr/kind.h"
#include "expr/type.h"
#include "options/set_language.h"
#include "parser/antlr_input.h"
#include "parser/parser.h"
#include "parser/smt2/smt2.h"
#include "util/floatingpoint.h"
#include "util/hash.h"
#include "util/integer.h"
#include "util/rational.h"
// \todo Review the need for this header
#include "math.h"

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

static bool isClosed(const Expr& e, std::set<Expr>& free, std::unordered_set<Expr, ExprHashFunction>& closedCache) {
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

static inline bool isClosed(const Expr& e, std::set<Expr>& free) {
  std::unordered_set<Expr, ExprHashFunction> cache;
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
parseCommand returns [CVC4::Command* cmd_return = NULL]
@declarations {
  std::unique_ptr<CVC4::Command> cmd;
  std::string name;
}
@after {
  cmd_return = cmd.release();
}
  : LPAREN_TOK command[&cmd] RPAREN_TOK

    /* This extended command has to be in the outermost production so that
     * the RPAREN_TOK is properly eaten and we are in a good state to read
     * the included file's tokens. */
  | LPAREN_TOK INCLUDE_TOK str[name,true] RPAREN_TOK
    { if(!PARSER_STATE->canIncludeFile()) {
        PARSER_STATE->parseError("include-file feature was disabled for this "
                                 "run.");
      }
      if(PARSER_STATE->strictModeEnabled()) {
        PARSER_STATE->parseError("Extended commands are not permitted while "
                                 "operating in strict compliance mode.");
      }
      PARSER_STATE->includeFile(name);
      // The command of the included file will be produced at the next
      // parseCommand() call
      cmd.reset(new EmptyCommand("include::" + name));
    }

  | EOF
  ;

/**
 * Parses a SyGuS command.
 * @return the parsed SyGuS command, or NULL if we've reached the end of the
 * input
 */
parseSygus returns [CVC4::Command* cmd_return = NULL]
@declarations {
  std::unique_ptr<CVC4::Command> cmd;
  std::string name;
}
@after {
  cmd_return = cmd.release();
}
  : LPAREN_TOK sygusCommand[&cmd] RPAREN_TOK
  | EOF
  ;

/**
 * Parse the internal portion of the command, ignoring the surrounding
 * parentheses.
 */
command [std::unique_ptr<CVC4::Command>* cmd]
@declarations {
  std::string name;
  std::vector<std::string> names;
  Expr expr, expr2;
  Type t;
  std::vector<Expr> terms;
  std::vector<Type> sorts;
  std::vector<std::pair<std::string, Type> > sortedVarNames;
  std::vector<Expr> flattenVars;
}
  : /* set the logic */
    SET_LOGIC_TOK symbol[name,CHECK_NONE,SYM_SORT]
    { Debug("parser") << "set logic: '" << name << "'" << std::endl;
      if( PARSER_STATE->logicIsSet() ) {
        PARSER_STATE->parseError("Only one set-logic is allowed.");
      }
      PARSER_STATE->setLogic(name);
      if( PARSER_STATE->sygus() ){
        cmd->reset(new SetBenchmarkLogicCommand(PARSER_STATE->getLogic().getLogicString()));
      }else{
        cmd->reset(new SetBenchmarkLogicCommand(name));
      }
    }
  | /* set-info */
    SET_INFO_TOK metaInfoInternal[cmd]
  | /* get-info */
    GET_INFO_TOK KEYWORD
    { cmd->reset(new GetInfoCommand(
          AntlrInput::tokenText($KEYWORD).c_str() + 1));
    }
  | /* set-option */
    SET_OPTION_TOK setOptionInternal[cmd]
  | /* get-option */
    GET_OPTION_TOK KEYWORD
    { cmd->reset(new GetOptionCommand(
          AntlrInput::tokenText($KEYWORD).c_str() + 1));
    }
  | /* sort declaration */
    DECLARE_SORT_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    { if(!PARSER_STATE->isTheoryEnabled(Smt2::THEORY_UF) &&
         !PARSER_STATE->isTheoryEnabled(Smt2::THEORY_ARRAYS) &&
         !PARSER_STATE->isTheoryEnabled(Smt2::THEORY_DATATYPES) &&
         !PARSER_STATE->isTheoryEnabled(Smt2::THEORY_SETS)) {
          PARSER_STATE->parseErrorLogic("Free sort symbols not allowed in ");
      }
    }
    symbol[name,CHECK_UNDECLARED,SYM_SORT]
    { PARSER_STATE->checkUserSymbol(name); }
    n=INTEGER_LITERAL
    { Debug("parser") << "declare sort: '" << name
                      << "' arity=" << n << std::endl;
      unsigned arity = AntlrInput::tokenToUnsigned(n);
      if(arity == 0) {
        Type type = PARSER_STATE->mkSort(name);
        cmd->reset(new DeclareTypeCommand(name, 0, type));
      } else {
        Type type = PARSER_STATE->mkSortConstructor(name, arity);
        cmd->reset(new DeclareTypeCommand(name, arity, type));
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
      cmd->reset(new DefineTypeCommand(name, sorts, t));
    }
  | /* function declaration */
    DECLARE_FUN_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    symbol[name,CHECK_NONE,SYM_VARIABLE]
    { PARSER_STATE->checkUserSymbol(name); }
    LPAREN_TOK sortList[sorts] RPAREN_TOK
    sortSymbol[t,CHECK_DECLARED]
    { Debug("parser") << "declare fun: '" << name << "'" << std::endl;
      if( !sorts.empty() ) {
        t = PARSER_STATE->mkFlatFunctionType(sorts, t);
      }
      if(t.isFunction() && !PARSER_STATE->isTheoryEnabled(Smt2::THEORY_UF)) {
        PARSER_STATE->parseErrorLogic("Functions (of non-zero arity) cannot "
                                      "be declared in logic ");
      }
      // we allow overloading for function declarations
      Expr func = PARSER_STATE->mkVar(name, t, ExprManager::VAR_FLAG_NONE, true);
      cmd->reset(new DeclareFunctionCommand(name, func, t));
    }
  | /* function definition */
    DEFINE_FUN_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    symbol[name,CHECK_UNDECLARED,SYM_VARIABLE]
    { PARSER_STATE->checkUserSymbol(name); }
    LPAREN_TOK sortedVarList[sortedVarNames] RPAREN_TOK
    sortSymbol[t,CHECK_DECLARED]
    { /* add variables to parser state before parsing term */
      Debug("parser") << "define fun: '" << name << "'" << std::endl;
      if( sortedVarNames.size() > 0 ) {
        sorts.reserve(sortedVarNames.size());
        for(std::vector<std::pair<std::string, CVC4::Type> >::const_iterator i =
              sortedVarNames.begin(), iend = sortedVarNames.end();
            i != iend;
            ++i) {
          sorts.push_back((*i).second);
        }
        t = PARSER_STATE->mkFlatFunctionType(sorts, t, flattenVars);
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
    {
      if( !flattenVars.empty() ){
        // if this function has any implicit variables flattenVars,
        // we apply the body of the definition to the flatten vars
        expr = PARSER_STATE->mkHoApply(expr, flattenVars);
        terms.insert(terms.end(), flattenVars.begin(), flattenVars.end());
      }
      PARSER_STATE->popScope();
      // declare the name down here (while parsing term, signature
      // must not be extended with the name itself; no recursion
      // permitted)
      // we allow overloading for function definitions
      Expr func = PARSER_STATE->mkFunction(name, t,
                                           ExprManager::VAR_FLAG_DEFINED, true);
      cmd->reset(new DefineFunctionCommand(name, func, terms, expr));
    }
  | /* value query */
    GET_VALUE_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    ( LPAREN_TOK termList[terms,expr] RPAREN_TOK
      { cmd->reset(new GetValueCommand(terms)); }
    | ~LPAREN_TOK
      { PARSER_STATE->parseError("The get-value command expects a list of "
                                 "terms.  Perhaps you forgot a pair of "
                                 "parentheses?");
      }
    )
  | /* get-assignment */
    GET_ASSIGNMENT_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    { cmd->reset(new GetAssignmentCommand()); }
  | /* assertion */
    ASSERT_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    /* { if( PARSER_STATE->sygus() ){
     *     PARSER_STATE->parseError("Sygus does not support assert command.");
     *   }
     * } */
    { PARSER_STATE->clearLastNamedTerm(); }
    term[expr, expr2]
    { bool inUnsatCore = PARSER_STATE->lastNamedTerm().first == expr;
      cmd->reset(new AssertCommand(expr, inUnsatCore));
      if(inUnsatCore) {
        // set the expression name, if there was a named term
        std::pair<Expr, std::string> namedTerm = PARSER_STATE->lastNamedTerm();
        Command* csen = new SetExpressionNameCommand(namedTerm.first, namedTerm.second);
        csen->setMuted(true);
        PARSER_STATE->preemptCommand(csen);
      }
    }
  | /* check-sat */
    CHECKSAT_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    { if( PARSER_STATE->sygus() ){
        PARSER_STATE->parseError("Sygus does not support check-sat command.");
      }
    }
    ( term[expr, expr2]
      { if(PARSER_STATE->strictModeEnabled()) {
          PARSER_STATE->parseError(
              "Extended commands (such as check-sat with an argument) are not "
              "permitted while operating in strict compliance mode.");
        }
      }
    | { expr = MK_CONST(bool(true)); }
    )
    { cmd->reset(new CheckSatCommand(expr)); }
  | /* get-assertions */
    GET_ASSERTIONS_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    { cmd->reset(new GetAssertionsCommand()); }
  | /* get-proof */
    GET_PROOF_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    { cmd->reset(new GetProofCommand()); }
  | /* get-unsat-core */
    GET_UNSAT_CORE_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    { cmd->reset(new GetUnsatCoreCommand); }
  | /* push */
    PUSH_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    { if( PARSER_STATE->sygus() ){
        PARSER_STATE->parseError("Sygus does not support push command.");
      }
    }
    ( k=INTEGER_LITERAL
      { unsigned n = AntlrInput::tokenToUnsigned(k);
        if(n == 0) {
          cmd->reset(new EmptyCommand());
        } else if(n == 1) {
          PARSER_STATE->pushScope();
          cmd->reset(new PushCommand());
        } else {
          std::unique_ptr<CommandSequence> seq(new CommandSequence());
          do {
            PARSER_STATE->pushScope();
            Command* push_cmd = new PushCommand();
            push_cmd->setMuted(n > 1);
            seq->addCommand(push_cmd);
            --n;
            } while(n > 0);
          cmd->reset(seq.release());
        }
      }
    | { if(PARSER_STATE->strictModeEnabled()) {
          PARSER_STATE->parseError(
              "Strict compliance mode demands an integer to be provided to "
              "PUSH.  Maybe you want (push 1)?");
        } else {
          PARSER_STATE->pushScope();
          cmd->reset(new PushCommand());
        }
      } )
  | POP_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    { if( PARSER_STATE->sygus() ){
        PARSER_STATE->parseError("Sygus does not support pop command.");
      }
    }
    ( k=INTEGER_LITERAL
      { unsigned n = AntlrInput::tokenToUnsigned(k);
        if(n > PARSER_STATE->scopeLevel()) {
          PARSER_STATE->parseError("Attempted to pop above the top stack "
                                   "frame.");
        }
        if(n == 0) {
          cmd->reset(new EmptyCommand());
        } else if(n == 1) {
          PARSER_STATE->popScope();
          cmd->reset(new PopCommand());
        } else {
          std::unique_ptr<CommandSequence> seq(new CommandSequence());
          do {
            PARSER_STATE->popScope();
            Command* pop_command = new PopCommand();
            pop_command->setMuted(n > 1);
            seq->addCommand(pop_command);
            --n;
          } while(n > 0);
          cmd->reset(seq.release());
        }
      }
    | { if(PARSER_STATE->strictModeEnabled()) {
          PARSER_STATE->parseError(
              "Strict compliance mode demands an integer to be provided to POP."
              "Maybe you want (pop 1)?");
        } else {
          PARSER_STATE->popScope();
          cmd->reset(new PopCommand());
        }
      }
    )
    /* exit */
  | EXIT_TOK
    { cmd->reset(new QuitCommand()); }

    /* New SMT-LIB 2.5 command set */
  | smt25Command[cmd]
    { if(PARSER_STATE->v2_0() && PARSER_STATE->strictModeEnabled()) {
        PARSER_STATE->parseError(
            "SMT-LIB 2.5 commands are not permitted while operating in strict "
            "compliance mode and in SMT-LIB 2.0 mode.");
      }
    }

    /* CVC4-extended SMT-LIB commands */
  | extendedCommand[cmd]
    { if(PARSER_STATE->strictModeEnabled()) {
        PARSER_STATE->parseError(
            "Extended commands are not permitted while operating in strict "
            "compliance mode.");
      }
    }

    /* error handling */
  | SIMPLE_SYMBOL
    { std::string id = AntlrInput::tokenText($SIMPLE_SYMBOL);
      if(id == "benchmark") {
        PARSER_STATE->parseError(
            "In SMT-LIBv2 mode, but got something that looks like SMT-LIBv1. "
            "Use --lang smt1 for SMT-LIBv1.");
      } else {
        PARSER_STATE->parseError("expected SMT-LIBv2 command, got `" + id +
                                 "'.");
      }
    }
  ;

sygusCommand [std::unique_ptr<CVC4::Command>* cmd]
@declarations {
  std::string name, fun;
  std::vector<std::string> names;
  Expr expr, expr2;
  Type t, range;
  std::vector<Expr> terms;
  std::vector<Type> sorts;
  std::vector<Expr> sygus_vars;
  std::vector<std::pair<std::string, Type> > sortedVarNames;
  SExpr sexpr;
  std::unique_ptr<CVC4::CommandSequence> seq;
  std::vector< std::vector< CVC4::SygusGTerm > > sgts;
  std::vector< CVC4::Datatype > datatypes;
  std::vector< std::vector<Expr> > ops;
  std::vector< std::vector< std::string > > cnames;
  std::vector< std::vector< std::vector< CVC4::Type > > > cargs;
  std::vector< bool > allow_const;
  std::vector< std::vector< std::string > > unresolved_gterm_sym;
  bool read_syntax = false;
  Type sygus_ret;
  std::map< CVC4::Type, CVC4::Type > sygus_to_builtin;
  std::map< CVC4::Type, CVC4::Expr > sygus_to_builtin_expr;
  int startIndex = -1;
  Expr synth_fun;
}
  : /* declare-var */
    DECLARE_VAR_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    symbol[name,CHECK_UNDECLARED,SYM_VARIABLE]
    { PARSER_STATE->checkUserSymbol(name); }
    sortSymbol[t,CHECK_DECLARED]
    { PARSER_STATE->mkSygusVar(name, t);
      cmd->reset(new EmptyCommand());
    }
  | /* declare-primed-var */
    DECLARE_PRIMED_VAR_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    symbol[name,CHECK_UNDECLARED,SYM_VARIABLE]
    { PARSER_STATE->checkUserSymbol(name); }
    sortSymbol[t,CHECK_DECLARED]
    { PARSER_STATE->mkSygusVar(name, t, true);
      cmd->reset(new EmptyCommand());
    }

  | /* synth-fun */
    ( SYNTH_FUN_TOK | SYNTH_INV_TOK { range = EXPR_MANAGER->booleanType(); } )
    { PARSER_STATE->checkThatLogicIsSet(); }
    symbol[fun,CHECK_UNDECLARED,SYM_VARIABLE]
    LPAREN_TOK sortedVarList[sortedVarNames] RPAREN_TOK
    ( sortSymbol[range,CHECK_DECLARED] )? {
      if( range.isNull() ){
        PARSER_STATE->parseError("Must supply return type for synth-fun.");
      }
      if( range.isFunction() ){
        PARSER_STATE->parseError("Cannot use synth-fun with function return type.");
      }
      seq.reset(new CommandSequence());
      std::vector<Type> var_sorts;
      for(std::vector<std::pair<std::string, CVC4::Type> >::const_iterator i =
            sortedVarNames.begin(), iend = sortedVarNames.end(); i != iend;
          ++i) {
        var_sorts.push_back( (*i).second );
      }
      Debug("parser-sygus") << "Define synth fun : " << fun << std::endl;
      Type synth_fun_type;
      if( var_sorts.size()>0 ){
        synth_fun_type = EXPR_MANAGER->mkFunctionType(var_sorts, range);
      }else{
        synth_fun_type = range;
      }
      // we do not allow overloading for synth fun
      synth_fun = PARSER_STATE->mkBoundVar(fun, synth_fun_type);
      // we add a declare function command here
      // this is the single unmuted command in the sequence generated by this smt2 command
      // TODO (as part of #1170) : make this a standard command.
      seq->addCommand(new DeclareFunctionCommand(fun, synth_fun, synth_fun_type));
      PARSER_STATE->pushScope(true);
      for(std::vector<std::pair<std::string, CVC4::Type> >::const_iterator i =
            sortedVarNames.begin(), iend = sortedVarNames.end(); i != iend;
          ++i) {
        Expr v = PARSER_STATE->mkBoundVar((*i).first, (*i).second);
        terms.push_back( v );
        sygus_vars.push_back( v );
      }
      Expr bvl;
      if( !terms.empty() ){
        bvl = MK_EXPR(kind::BOUND_VAR_LIST, terms);
      }
      terms.clear();
      terms.push_back(bvl);
      // associate this variable list with the synth fun
      std::vector< Expr > attr_val_bvl;
      attr_val_bvl.push_back( bvl );
      Command* cattr_bvl = new SetUserAttributeCommand("sygus-synth-fun-var-list", synth_fun, attr_val_bvl);
      cattr_bvl->setMuted(true);
      PARSER_STATE->preemptCommand(cattr_bvl);
    }
    ( LPAREN_TOK
    ( LPAREN_TOK
      symbol[name,CHECK_NONE,SYM_VARIABLE] 
      sortSymbol[t,CHECK_DECLARED]
      { std::stringstream ss;
        ss << fun << "_" << name;
        if( name=="Start" ){
          startIndex = datatypes.size();
        }
        std::string dname = ss.str();
        sgts.push_back( std::vector< CVC4::SygusGTerm >() );
        sgts.back().push_back( CVC4::SygusGTerm() );
        PARSER_STATE->pushSygusDatatypeDef(
            t, dname, datatypes, sorts, ops, cnames, cargs, allow_const,
            unresolved_gterm_sym);
        Type unres_t;
        if(!PARSER_STATE->isUnresolvedType(dname)) {
          // if not unresolved, must be undeclared
          Debug("parser-sygus") << "Make unresolved type : " << dname
                                << std::endl;
          PARSER_STATE->checkDeclaration(dname, CHECK_UNDECLARED, SYM_SORT);
          unres_t = PARSER_STATE->mkUnresolvedType(dname);
        }else{
          Debug("parser-sygus") << "Get sort : " << dname << std::endl;
          unres_t = PARSER_STATE->getSort(dname);
        }
        sygus_to_builtin[unres_t] = t;
        Debug("parser-sygus") << "--- Read sygus grammar " << name
                              << " under function " << fun << "..."
                              << std::endl
                              << "    type to resolve " << unres_t << std::endl
                              << "    builtin type " << t << std::endl;
      }
      // Note the official spec for NTDef is missing the ( parens )
      // but they are necessary to parse SyGuS examples
      LPAREN_TOK ( sygusGTerm[ sgts.back().back(), fun]
      { sgts.back().push_back( CVC4::SygusGTerm() ); } )+ 
      RPAREN_TOK { sgts.back().pop_back(); }
      RPAREN_TOK 
    )+
    RPAREN_TOK { read_syntax = true; }
    )?
    { // the sygus sym type specifies the required grammar for synth_fun, expressed as a type
      Type sygus_sym_type;
      if( !read_syntax ){
        sygus_sym_type = range;
        PARSER_STATE->popScope();
      }else{
        Debug("parser-sygus") << "--- Process " << sgts.size()
                              << " sygus gterms..." << std::endl;
        for( unsigned i=0; i<sgts.size(); i++ ){
          for( unsigned j=0; j<sgts[i].size(); j++ ){
            Type sub_ret;
            PARSER_STATE->processSygusGTerm(
                sgts[i][j], i, datatypes, sorts, ops, cnames, cargs,
                allow_const, unresolved_gterm_sym, sygus_vars, sygus_to_builtin,
                sygus_to_builtin_expr, sub_ret );
          }
        }
        //swap index if necessary
        Debug("parser-sygus") << "--- Making sygus datatypes..." << std::endl;
        for( unsigned i=0; i<datatypes.size(); i++ ){
          Debug("parser-sygus") << "..." << datatypes[i].getName()
                                << " has builtin sort " << sorts[i]
                                << std::endl;
        }
        for( unsigned i=0; i<datatypes.size(); i++ ){
          Debug("parser-sygus") << "...make " << datatypes[i].getName()
                                << " with builtin sort " << sorts[i]
                                << std::endl;
          if( sorts[i].isNull() ){
            PARSER_STATE->parseError("Internal error : could not infer "
                                     "builtin sort for nested gterm.");
          }
          datatypes[i].setSygus( sorts[i], terms[0], allow_const[i], false );
          PARSER_STATE->mkSygusDatatype(
              datatypes[i], ops[i], cnames[i], cargs[i],
              unresolved_gterm_sym[i], sygus_to_builtin );
        }
        PARSER_STATE->setSygusStartIndex(fun, startIndex, datatypes, sorts, ops);
        //only care about datatypes/sorts/ops past here
        PARSER_STATE->popScope();
        Debug("parser-sygus") << "--- Make " << datatypes.size()
                              << " mutual datatypes..." << std::endl;
        for( unsigned i=0; i<datatypes.size(); i++ ){
          Debug("parser-sygus") << "  " << i << " : " << datatypes[i].getName() << std::endl;
        }
        std::vector<DatatypeType> datatypeTypes =
            PARSER_STATE->mkMutualDatatypeTypes(datatypes);
        Command * cdd = new DatatypeDeclarationCommand(datatypeTypes);
        // we set this command muted since there should only be one success printed
        cdd->setMuted(true);
        seq->addCommand(cdd);
        if( sorts[0]!=range ){
          PARSER_STATE->parseError(std::string("Bad return type in grammar for "
                                               "SyGuS function ") + fun);
        }
        sygus_sym_type = datatypeTypes[0];
      }
      
      // store a dummy variable which stands for second-order quantification, linked to synth fun by an attribute
      PARSER_STATE->addSygusFunSymbol( sygus_sym_type, synth_fun );
      cmd->reset(seq.release());
    }
  | /* constraint */
    CONSTRAINT_TOK { 
      PARSER_STATE->checkThatLogicIsSet();
      Debug("parser-sygus") << "Sygus : define sygus funs..." << std::endl;
      Debug("parser-sygus") << "Sygus : read constraint..." << std::endl;
    }
    term[expr, expr2]
    { Debug("parser-sygus") << "...read constraint " << expr << std::endl;
      PARSER_STATE->addSygusConstraint(expr);
      cmd->reset(new EmptyCommand());
    }
  | INV_CONSTRAINT_TOK {  
      PARSER_STATE->checkThatLogicIsSet();
      Debug("parser-sygus") << "Sygus : define sygus funs..." << std::endl;
      Debug("parser-sygus") << "Sygus : read inv-constraint..." << std::endl;
    }
    ( symbol[name,CHECK_NONE,SYM_VARIABLE] { 
        if( !terms.empty() ){
          if( !PARSER_STATE->isDefinedFunction(name) ){
            std::stringstream ss;
            ss << "Function " << name << " in inv-constraint is not defined.";
            PARSER_STATE->parseError(ss.str());
          }
        }
        terms.push_back( PARSER_STATE->getVariable(name) );
      }
    )+ {
      if( terms.size()!=4 ){
        PARSER_STATE->parseError("Bad syntax for inv-constraint: expected 4 "
                                 "arguments.");
      }
      //get primed variables
      std::vector< Expr > primed[2];
      std::vector< Expr > all;
      for( unsigned i=0; i<2; i++ ){
        PARSER_STATE->getSygusPrimedVars( primed[i], i==1 );
        all.insert( all.end(), primed[i].begin(), primed[i].end() );
      }
      //make relevant terms
      for( unsigned i=0; i<4; i++ ){
        Expr op = terms[i];
        Debug("parser-sygus") << "Make inv-constraint term #" << i << " : " << op  << "..." << std::endl;
        std::vector< Expr > children;
        children.push_back( op );
        if( i==2 ){
          children.insert( children.end(), all.begin(), all.end() );
        }else{
          children.insert( children.end(), primed[0].begin(), primed[0].end() );
        }
        terms[i] = EXPR_MANAGER->mkExpr( i==0 ? kind::APPLY_UF : kind::APPLY,children);
        if( i==0 ){
          std::vector< Expr > children2;
          children2.push_back( op );
          children2.insert(children2.end(), primed[1].begin(),
                           primed[1].end());
          terms.push_back( EXPR_MANAGER->mkExpr(kind::APPLY_UF,children2) );
        }
      }
      //make constraints
      std::vector< Expr > conj;
      conj.push_back( EXPR_MANAGER->mkExpr(kind::IMPLIES, terms[1],
                                           terms[0] ) );
      const Expr term0_and_2 = EXPR_MANAGER->mkExpr(kind::AND, terms[0],
                                                    terms[2] );
      conj.push_back( EXPR_MANAGER->mkExpr(kind::IMPLIES, term0_and_2,
                                           terms[4] ) );
      conj.push_back( EXPR_MANAGER->mkExpr(kind::IMPLIES, terms[0], terms[3]) );
      Expr ic = EXPR_MANAGER->mkExpr( kind::AND, conj );
      Debug("parser-sygus") << "...read invariant constraint " << ic
                            << std::endl;
      PARSER_STATE->addSygusConstraint(ic);
      cmd->reset(new EmptyCommand());
    }
  | /* check-synth */
    CHECK_SYNTH_TOK
    { PARSER_STATE->checkThatLogicIsSet(); }
    { Expr sygusVar = EXPR_MANAGER->mkVar("sygus", EXPR_MANAGER->booleanType());
      Expr inst_attr =EXPR_MANAGER->mkExpr(kind::INST_ATTRIBUTE, sygusVar);
      Expr sygusAttr = EXPR_MANAGER->mkExpr(kind::INST_PATTERN_LIST, inst_attr);
      std::vector<Expr> bodyv;
      Debug("parser-sygus") << "Sygus : Constructing sygus constraint..."
                            << std::endl;
      Expr body = EXPR_MANAGER->mkExpr(kind::NOT,
                                       PARSER_STATE->getSygusConstraints());
      Debug("parser-sygus") << "...constructed sygus constraint " << body
                            << std::endl;      
      if( !PARSER_STATE->getSygusVars().empty() ){
        Expr boundVars = EXPR_MANAGER->mkExpr(kind::BOUND_VAR_LIST,
                                              PARSER_STATE->getSygusVars());
        body = EXPR_MANAGER->mkExpr(kind::EXISTS, boundVars, body);
        Debug("parser-sygus") << "...constructed exists " << body << std::endl;
      }
      if( !PARSER_STATE->getSygusFunSymbols().empty() ){
        Expr boundVars = EXPR_MANAGER->mkExpr(
            kind::BOUND_VAR_LIST, PARSER_STATE->getSygusFunSymbols());
        body = EXPR_MANAGER->mkExpr(kind::FORALL, boundVars, body, sygusAttr);
      }
      Debug("parser-sygus") << "...constructed forall " << body << std::endl;   
      Command* c = new SetUserAttributeCommand("sygus", sygusVar);
      c->setMuted(true);
      PARSER_STATE->preemptCommand(c);
      cmd->reset(new CheckSynthCommand(body));
    }
  | command[cmd]
 //   /* error handling */
 // | (~(CHECK_SYNTH_TOK))=> token=.
 //   { std::string id = AntlrInput::tokenText($token);
 //     std::stringstream ss;
 //     ss << "Not a recognized SyGuS command: `" << id << "'";
 //     PARSER_STATE->parseError(ss.str());
 //   }
  ;

// SyGuS grammar term.
//
// fun is the name of the synth-fun this grammar term is for.
// This method adds N operators to ops[index], N names to cnames[index] and N
// type argument vectors to cargs[index] (where typically N=1)
// This method may also add new elements pairwise into
// datatypes/sorts/ops/cnames/cargs in the case of non-flat gterms.
sygusGTerm[CVC4::SygusGTerm& sgt, std::string& fun]
@declarations {
  std::string name, name2;
  bool readEnum = false;
  Kind k;
  Type t;
  CVC4::DatatypeConstructor* ctor = NULL;
  std::string sname;
  std::vector< Expr > let_vars;
  bool readingLet = false;
  std::string s;
}
  : LPAREN_TOK
    //read operator
    ( builtinOp[k]{ 
        Debug("parser-sygus") << "Sygus grammar " << fun << " : builtin op : "
                              << name << std::endl;
        // Since we enforce satisfaction completeness, immediately convert to
        // total version.
        if( k==CVC4::kind::BITVECTOR_UDIV ){
          k = CVC4::kind::BITVECTOR_UDIV_TOTAL;
        }else if( k==CVC4::kind::BITVECTOR_UREM ){
          k = CVC4::kind::BITVECTOR_UREM_TOTAL;
        }else if( k==CVC4::kind::DIVISION ){
          k = CVC4::kind::DIVISION_TOTAL;
        }else if( k==CVC4::kind::INTS_DIVISION ){
          k = CVC4::kind::INTS_DIVISION_TOTAL;
        }else if( k==CVC4::kind::INTS_MODULUS ){
          k = CVC4::kind::INTS_MODULUS_TOTAL;
        }
        sgt.d_name = kind::kindToString(k);
        sgt.d_gterm_type = SygusGTerm::gterm_op;
        sgt.d_expr = EXPR_MANAGER->operatorOf(k);
      }
     | SYGUS_LET_TOK LPAREN_TOK { 
         sgt.d_name = std::string("let");
         sgt.d_gterm_type = SygusGTerm::gterm_let;
         PARSER_STATE->pushScope(true);
         readingLet = true;
       }
       ( LPAREN_TOK 
        symbol[sname,CHECK_NONE,SYM_VARIABLE] 
        sortSymbol[t,CHECK_DECLARED] { 
          Expr v = PARSER_STATE->mkBoundVar(sname,t); 
          sgt.d_let_vars.push_back( v ); 
          sgt.addChild();
        } 
        sygusGTerm[sgt.d_children.back(), fun]
        RPAREN_TOK )+ RPAREN_TOK
    | SYGUS_CONSTANT_TOK sortSymbol[t,CHECK_DECLARED] 
      { sgt.d_gterm_type = SygusGTerm::gterm_constant;
        sgt.d_type = t;
        Debug("parser-sygus") << "Sygus grammar constant." << std::endl;
      }
    | SYGUS_VARIABLE_TOK sortSymbol[t,CHECK_DECLARED]
      { sgt.d_gterm_type = SygusGTerm::gterm_variable;
        sgt.d_type = t;
        Debug("parser-sygus") << "Sygus grammar variable." << std::endl;
      }
    | SYGUS_LOCAL_VARIABLE_TOK sortSymbol[t,CHECK_DECLARED]
      { sgt.d_gterm_type = SygusGTerm::gterm_local_variable;
        sgt.d_type = t;
        Debug("parser-sygus") << "Sygus grammar local variable...ignore."
                              << std::endl;
      }
    | SYGUS_INPUT_VARIABLE_TOK sortSymbol[t,CHECK_DECLARED]
      { sgt.d_gterm_type = SygusGTerm::gterm_input_variable;
        sgt.d_type = t;
        Debug("parser-sygus") << "Sygus grammar (input) variable."
                              << std::endl;
      }
    | symbol[name,CHECK_NONE,SYM_VARIABLE] { 
        bool isBuiltinOperator = PARSER_STATE->isOperatorEnabled(name);
        if(isBuiltinOperator) {
          Debug("parser-sygus") << "Sygus grammar " << fun << " : builtin op : "
                                << name << std::endl;
          k = PARSER_STATE->getOperatorKind(name);
          if( k==CVC4::kind::BITVECTOR_UDIV ){
            k = CVC4::kind::BITVECTOR_UDIV_TOTAL;
          }else if( k==CVC4::kind::BITVECTOR_UREM ){
            k = CVC4::kind::BITVECTOR_UREM_TOTAL;
          }else if( k==CVC4::kind::DIVISION ){
            k = CVC4::kind::DIVISION_TOTAL;
          }else if( k==CVC4::kind::INTS_DIVISION ){
            k = CVC4::kind::INTS_DIVISION_TOTAL;
          }else if( k==CVC4::kind::INTS_MODULUS ){
            k = CVC4::kind::INTS_MODULUS_TOTAL;
          }
          sgt.d_name = kind::kindToString(k);
          sgt.d_gterm_type = SygusGTerm::gterm_op;
          sgt.d_expr = EXPR_MANAGER->operatorOf(k);
        }else{
          // what is this sygus term trying to accomplish here, if the
          // symbol isn't yet declared?!  probably the following line will
          // fail, but we need an operator to continue here..
          Debug("parser-sygus")
              << "Sygus grammar " << fun << " : op (declare="
              << PARSER_STATE->isDeclared(name) << ", define="
              << PARSER_STATE->isDefinedFunction(name) << ") : " << name
              << std::endl;
          if(!PARSER_STATE->isDeclared(name) &&
             !PARSER_STATE->isDefinedFunction(name) ){
            PARSER_STATE->parseError("Functions in sygus grammars must be "
                                     "defined.");
          }
          sgt.d_name = name;
          sgt.d_gterm_type = SygusGTerm::gterm_op;
          sgt.d_expr = PARSER_STATE->getVariable(name) ;
        }
      }
    )
    //read arguments
    { Debug("parser-sygus") << "Read arguments under " << sgt.d_name
                            << std::endl;
      sgt.addChild();
    }
    ( sygusGTerm[sgt.d_children.back(), fun]
      { Debug("parser-sygus") << "Finished read argument #"
                              << sgt.d_children.size() << "..." << std::endl;
        sgt.addChild();
      }
    )* 
    RPAREN_TOK {
      //pop last child index 
      sgt.d_children.pop_back();   
      if( readingLet ){
        PARSER_STATE->popScope();
      }
    }
  | INTEGER_LITERAL
    { Debug("parser-sygus") << "Sygus grammar " << fun << " : integer literal "
                            << AntlrInput::tokenText($INTEGER_LITERAL)
                            << std::endl;
      sgt.d_expr = MK_CONST(Rational(AntlrInput::tokenText($INTEGER_LITERAL)));
      sgt.d_name = AntlrInput::tokenText($INTEGER_LITERAL);
      sgt.d_gterm_type = SygusGTerm::gterm_op;
    }
  | HEX_LITERAL
    { Debug("parser-sygus") << "Sygus grammar " << fun << " : hex literal "
                            << AntlrInput::tokenText($HEX_LITERAL) << std::endl;
      assert( AntlrInput::tokenText($HEX_LITERAL).find("#x") == 0 );
      std::string hexString = AntlrInput::tokenTextSubstr($HEX_LITERAL, 2);
      sgt.d_expr = MK_CONST( BitVector(hexString, 16) );
      sgt.d_name = AntlrInput::tokenText($HEX_LITERAL);
      sgt.d_gterm_type = SygusGTerm::gterm_op;
    }
  | BINARY_LITERAL
    { Debug("parser-sygus") << "Sygus grammar " << fun << " : binary literal "
                            << AntlrInput::tokenText($BINARY_LITERAL)
                            << std::endl;
      assert( AntlrInput::tokenText($BINARY_LITERAL).find("#b") == 0 );
      std::string binString = AntlrInput::tokenTextSubstr($BINARY_LITERAL, 2);
      sgt.d_expr = MK_CONST( BitVector(binString, 2) );
      sgt.d_name = AntlrInput::tokenText($BINARY_LITERAL);
      sgt.d_gterm_type = SygusGTerm::gterm_op;
    }
  | str[s,false]
    { Debug("parser-sygus") << "Sygus grammar " << fun << " : string literal \""
                            << s << "\"" << std::endl;
      sgt.d_expr = MK_CONST( ::CVC4::String(s, true) );
      sgt.d_name = s;
      sgt.d_gterm_type = SygusGTerm::gterm_op;
    }
  | symbol[name,CHECK_NONE,SYM_VARIABLE]
    ( SYGUS_ENUM_CONS_TOK symbol[name2,CHECK_NONE,SYM_VARIABLE]
      { readEnum = true; }
    )?
    { if( readEnum ){
        name = name + "__Enum__" + name2;
        Debug("parser-sygus") << "Sygus grammar " << fun << " : Enum constant "
                              << name << std::endl;
        Expr c = PARSER_STATE->getVariable(name);
        sgt.d_expr = MK_EXPR(kind::APPLY_CONSTRUCTOR,c);
        sgt.d_name = name;
        sgt.d_gterm_type = SygusGTerm::gterm_op;
      }else{
        if( name[0] == '-' ){  //hack for unary minus
          Debug("parser-sygus") << "Sygus grammar " << fun
                                << " : unary minus integer literal " << name
                                << std::endl;
          sgt.d_expr = MK_CONST(Rational(name));
          sgt.d_name = name;
          sgt.d_gterm_type = SygusGTerm::gterm_op;
        }else if( PARSER_STATE->isDeclared(name,SYM_VARIABLE) ){
          Debug("parser-sygus") << "Sygus grammar " << fun << " : symbol "
                                << name << std::endl;
          sgt.d_expr = PARSER_STATE->getVariable(name);
          sgt.d_name = name;
          sgt.d_gterm_type = SygusGTerm::gterm_op;
        }else{
          //prepend function name to base sorts when reading an operator
          std::stringstream ss;
          ss << fun << "_" << name;
          name = ss.str();
          if( PARSER_STATE->isDeclared(name, SYM_SORT) ){
            Debug("parser-sygus") << "Sygus grammar " << fun
                                  << " : nested sort " << name << std::endl;
            sgt.d_type = PARSER_STATE->getSort(name);
            sgt.d_gterm_type = SygusGTerm::gterm_nested_sort;
          }else{
            Debug("parser-sygus") << "Sygus grammar " << fun
                                  << " : unresolved symbol " << name
                                  << std::endl;
            sgt.d_gterm_type = SygusGTerm::gterm_unresolved;
            sgt.d_name = name;
          }
        }
      }
    }
  ;

// Separate this into its own rule (can be invoked by set-info or meta-info)
metaInfoInternal[std::unique_ptr<CVC4::Command>* cmd]
@declarations {
  std::string name;
  SExpr sexpr;
}
  : KEYWORD symbolicExpr[sexpr]
    { name = AntlrInput::tokenText($KEYWORD);
      if(name == ":cvc4-logic" || name == ":cvc4_logic") {
        PARSER_STATE->setLogic(sexpr.getValue());
      } else if(name == ":smt-lib-version") {
        // if we don't recognize the revision name, just keep the current mode
        if( (sexpr.isRational() && sexpr.getRationalValue() == Rational(2)) ||
            sexpr.getValue() == "2" ||
            sexpr.getValue() == "2.0" ) {
          PARSER_STATE->setLanguage(language::input::LANG_SMTLIB_V2_0);
        } else if( (sexpr.isRational() &&
                    sexpr.getRationalValue() == Rational(5, 2)) ||
                  sexpr.getValue() == "2.5" ) {
          PARSER_STATE->setLanguage(language::input::LANG_SMTLIB_V2_5);
        } else if( (sexpr.isRational() &&
                    sexpr.getRationalValue() == Rational(13, 5)) ||
                  sexpr.getValue() == "2.6" ) {
          PARSER_STATE->setLanguage(language::input::LANG_SMTLIB_V2_6);
        }
      }
      PARSER_STATE->setInfo(name.c_str() + 1, sexpr);
      cmd->reset(new SetInfoCommand(name.c_str() + 1, sexpr));
    }
  ;

setOptionInternal[std::unique_ptr<CVC4::Command>* cmd]
@init {
  std::string name;
  SExpr sexpr;
}
  : keyword[name] symbolicExpr[sexpr]
    { PARSER_STATE->setOption(name.c_str() + 1, sexpr);
      cmd->reset(new SetOptionCommand(name.c_str() + 1, sexpr));
      // Ugly that this changes the state of the parser; but
      // global-declarations affects parsing, so we can't hold off
      // on this until some SmtEngine eventually (if ever) executes it.
      if(name == ":global-declarations") {
        PARSER_STATE->setGlobalDeclarations(sexpr.getValue() == "true");
      }
    }
  ;

smt25Command[std::unique_ptr<CVC4::Command>* cmd]
@declarations {
  std::string name;
  std::string fname;
  Expr expr, expr2;
  std::vector<std::pair<std::string, Type> > sortedVarNames;
  SExpr sexpr;
  Type t;
  Expr func;
  std::vector<Expr> bvs;
  std::vector< std::vector<std::pair<std::string, Type> > > sortedVarNamesList;
  std::vector<std::vector<Expr>> flattenVarsList;
  std::vector<std::vector<Expr>> formals;
  std::vector<Expr> funcs;
  std::vector<Expr> func_defs;
  Expr aexpr;
  std::unique_ptr<CVC4::CommandSequence> seq;
  std::vector<Type> sorts;
  std::vector<Expr> flattenVars;
}
    /* meta-info */
  : META_INFO_TOK metaInfoInternal[cmd]

    /* declare-const */
  | DECLARE_CONST_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    symbol[name,CHECK_NONE,SYM_VARIABLE]
    { PARSER_STATE->checkUserSymbol(name); }
    sortSymbol[t,CHECK_DECLARED]
    { // allow overloading here
      Expr c = PARSER_STATE->mkVar(name, t, ExprManager::VAR_FLAG_NONE, true);
      cmd->reset(new DeclareFunctionCommand(name, c, t)); }

    /* get model */
  | GET_MODEL_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    { cmd->reset(new GetModelCommand()); }

    /* echo */
  | ECHO_TOK
    ( simpleSymbolicExpr[sexpr]
      { cmd->reset(new EchoCommand(sexpr.toString())); }
    | { cmd->reset(new EchoCommand()); }
    )

    /* reset: reset everything, returning solver to initial state.
     * Logic and options must be set again. */
  | RESET_TOK
    { cmd->reset(new ResetCommand());
      PARSER_STATE->reset();
    }
    /* reset-assertions: reset assertions, assertion stack, declarations,
     * etc., but the logic and options remain as they were. */
  | RESET_ASSERTIONS_TOK
    { cmd->reset(new ResetAssertionsCommand());
      PARSER_STATE->resetAssertions();
    }
  | DEFINE_FUN_REC_TOK
    { PARSER_STATE->checkThatLogicIsSet(); }
    symbol[fname,CHECK_NONE,SYM_VARIABLE]
    { PARSER_STATE->checkUserSymbol(fname); }
    LPAREN_TOK sortedVarList[sortedVarNames] RPAREN_TOK
    sortSymbol[t,CHECK_DECLARED]
    {
      func = PARSER_STATE->mkDefineFunRec(fname, sortedVarNames, t, flattenVars);
      PARSER_STATE->pushDefineFunRecScope(sortedVarNames, func, flattenVars, bvs, true );
    }
    term[expr, expr2]
    { PARSER_STATE->popScope(); 
      if( !flattenVars.empty() ){
        expr = PARSER_STATE->mkHoApply( expr, flattenVars );
      }
      cmd->reset(new DefineFunctionRecCommand(func,bvs,expr));
    }
  | DEFINE_FUNS_REC_TOK
    { PARSER_STATE->checkThatLogicIsSet();}
    LPAREN_TOK
    ( LPAREN_TOK
      symbol[fname,CHECK_UNDECLARED,SYM_VARIABLE]
      { PARSER_STATE->checkUserSymbol(fname); }
      LPAREN_TOK sortedVarList[sortedVarNames] RPAREN_TOK
      sortSymbol[t,CHECK_DECLARED]
      {
        flattenVars.clear();
        func = PARSER_STATE->mkDefineFunRec( fname, sortedVarNames, t, flattenVars );
        funcs.push_back( func );

        // add to lists (need to remember for when parsing the bodies)
        sortedVarNamesList.push_back( sortedVarNames );
        flattenVarsList.push_back( flattenVars );

        // set up parsing the next variable list block
        sortedVarNames.clear();
        flattenVars.clear();
      }
      RPAREN_TOK
    )+
    RPAREN_TOK
    LPAREN_TOK
    { 
      //set up the first scope 
      if( sortedVarNamesList.empty() ){
        PARSER_STATE->parseError("Must define at least one function in "
                                 "define-funs-rec");
      }
      bvs.clear();
      PARSER_STATE->pushDefineFunRecScope( sortedVarNamesList[0], funcs[0],
                                           flattenVarsList[0], bvs, true);
    }
    (
    term[expr,expr2]
    { 
      unsigned j = func_defs.size();
      if( !flattenVarsList[j].empty() ){
        expr = PARSER_STATE->mkHoApply( expr, flattenVarsList[j] );
      }
      func_defs.push_back( expr );
      formals.push_back(bvs);
      j++;
      //set up the next scope 
      PARSER_STATE->popScope();
      if( func_defs.size()<funcs.size() ){
        bvs.clear();
        PARSER_STATE->pushDefineFunRecScope( sortedVarNamesList[j], funcs[j], 
                                             flattenVarsList[j], bvs, true);
      }
    }
    )+
    RPAREN_TOK
    { if( funcs.size()!=func_defs.size() ){
        PARSER_STATE->parseError(std::string(
            "Number of functions defined does not match number listed in "
            "define-funs-rec"));
      }
      cmd->reset( new DefineFunctionRecCommand(funcs,formals,func_defs));
    }
  // CHECK_SAT_ASSUMING still being discussed
  // GET_UNSAT_ASSUMPTIONS
  ;

extendedCommand[std::unique_ptr<CVC4::Command>* cmd]
@declarations {
  std::vector<CVC4::Datatype> dts;
  Expr e, e2;
  Type t;
  std::string name;
  std::vector<std::string> names;
  std::vector<Expr> terms;
  std::vector<Type> sorts;
  std::vector<std::pair<std::string, Type> > sortedVarNames;
  std::unique_ptr<CVC4::CommandSequence> seq;
}
    /* Extended SMT-LIB set of commands syntax, not permitted in
     * --smtlib2 compliance mode. */
  : DECLARE_DATATYPES_2_5_TOK datatypes_2_5_DefCommand[false, cmd]
  | DECLARE_CODATATYPES_2_5_TOK datatypes_2_5_DefCommand[true, cmd]
  | DECLARE_DATATYPE_TOK datatypeDefCommand[false, cmd]
  | DECLARE_CODATATYPE_TOK datatypeDefCommand[true, cmd]
  | DECLARE_DATATYPES_TOK datatypesDefCommand[false, cmd]
  | DECLARE_CODATATYPES_TOK datatypesDefCommand[true, cmd]
  | rewriterulesCommand[cmd]

    /* Support some of Z3's extended SMT-LIB commands */

  | DECLARE_SORTS_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    { if(!PARSER_STATE->isTheoryEnabled(Smt2::THEORY_UF) &&
         !PARSER_STATE->isTheoryEnabled(Smt2::THEORY_ARRAYS) &&
         !PARSER_STATE->isTheoryEnabled(Smt2::THEORY_DATATYPES) &&
         !PARSER_STATE->isTheoryEnabled(Smt2::THEORY_SETS)) {
        PARSER_STATE->parseErrorLogic("Free sort symbols not allowed in ");
      }
    }
    { seq.reset(new CVC4::CommandSequence()); }
    LPAREN_TOK
    ( symbol[name,CHECK_UNDECLARED,SYM_SORT]
      { PARSER_STATE->checkUserSymbol(name);
        Type type = PARSER_STATE->mkSort(name);
        seq->addCommand(new DeclareTypeCommand(name, 0, type));
      }
    )+
    RPAREN_TOK
    { cmd->reset(seq.release()); }

  | DECLARE_FUNS_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    { seq.reset(new CVC4::CommandSequence()); }
    LPAREN_TOK
    ( LPAREN_TOK symbol[name,CHECK_UNDECLARED,SYM_VARIABLE]
      { PARSER_STATE->checkUserSymbol(name); }
      nonemptySortList[sorts] RPAREN_TOK
      { Type t;
        if(sorts.size() > 1) {
          if(!PARSER_STATE->isTheoryEnabled(Smt2::THEORY_UF)) {
            PARSER_STATE->parseErrorLogic("Functions (of non-zero arity) "
                                          "cannot be declared in logic ");
          }
          // must flatten
          Type range = sorts.back();
          sorts.pop_back();
          t = PARSER_STATE->mkFlatFunctionType(sorts, range);
        } else {
          t = sorts[0];
        }
        // allow overloading
        Expr func = PARSER_STATE->mkVar(name, t, ExprManager::VAR_FLAG_NONE, true);
        seq->addCommand(new DeclareFunctionCommand(name, func, t));
        sorts.clear();
      }
    )+
    RPAREN_TOK
    { cmd->reset(seq.release()); } 
  | DECLARE_PREDS_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    { seq.reset(new CVC4::CommandSequence()); }
    LPAREN_TOK
    ( LPAREN_TOK symbol[name,CHECK_UNDECLARED,SYM_VARIABLE]
      { PARSER_STATE->checkUserSymbol(name); }
      sortList[sorts] RPAREN_TOK
      { Type t = EXPR_MANAGER->booleanType();
        if(sorts.size() > 0) {
          if(!PARSER_STATE->isTheoryEnabled(Smt2::THEORY_UF)) {
            PARSER_STATE->parseErrorLogic("Predicates (of non-zero arity) "
                                          "cannot be declared in logic ");
          }
          t = EXPR_MANAGER->mkFunctionType(sorts, t);
        }
        // allow overloading
        Expr func = PARSER_STATE->mkVar(name, t, ExprManager::VAR_FLAG_NONE, true);
        seq->addCommand(new DeclareFunctionCommand(name, func, t));
        sorts.clear();
      }
    )+
    RPAREN_TOK
    { cmd->reset(seq.release()); }

  | DEFINE_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    ( symbol[name,CHECK_UNDECLARED,SYM_VARIABLE]
      { PARSER_STATE->checkUserSymbol(name); }
      term[e,e2]
      { Expr func = PARSER_STATE->mkFunction(name, e.getType(),
                                             ExprManager::VAR_FLAG_DEFINED);
        cmd->reset(new DefineFunctionCommand(name, func, e));
      }
    | LPAREN_TOK
      symbol[name,CHECK_UNDECLARED,SYM_VARIABLE]
      { PARSER_STATE->checkUserSymbol(name); }
      sortedVarList[sortedVarNames] RPAREN_TOK
      { /* add variables to parser state before parsing term */
        Debug("parser") << "define fun: '" << name << "'" << std::endl;
        PARSER_STATE->pushScope(true);
        for(std::vector<std::pair<std::string, CVC4::Type> >::const_iterator i =
              sortedVarNames.begin(), iend = sortedVarNames.end(); i != iend;
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
          for(std::vector<std::pair<std::string, CVC4::Type> >::const_iterator
                i = sortedVarNames.begin(), iend = sortedVarNames.end();
              i != iend; ++i) {
            sorts.push_back((*i).second);
          }
          t = EXPR_MANAGER->mkFunctionType(sorts, t);
        }
        Expr func = PARSER_STATE->mkFunction(name, t,
                                             ExprManager::VAR_FLAG_DEFINED);
        cmd->reset(new DefineFunctionCommand(name, func, terms, e));
      }
    )
  | DEFINE_CONST_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    symbol[name,CHECK_UNDECLARED,SYM_VARIABLE]
    { PARSER_STATE->checkUserSymbol(name); }
    sortSymbol[t,CHECK_DECLARED]
    { /* add variables to parser state before parsing term */
      Debug("parser") << "define const: '" << name << "'" << std::endl;
      PARSER_STATE->pushScope(true);
      for(std::vector<std::pair<std::string, CVC4::Type> >::const_iterator i =
            sortedVarNames.begin(), iend = sortedVarNames.end(); i != iend;
          ++i) {
        terms.push_back(PARSER_STATE->mkBoundVar((*i).first, (*i).second));
      }
    }
    term[e, e2]
    { PARSER_STATE->popScope();
      // declare the name down here (while parsing term, signature
      // must not be extended with the name itself; no recursion
      // permitted)
      Expr func = PARSER_STATE->mkFunction(name, t,
                                           ExprManager::VAR_FLAG_DEFINED);
      cmd->reset(new DefineFunctionCommand(name, func, terms, e));
    }

  | SIMPLIFY_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    term[e,e2]
    { cmd->reset(new SimplifyCommand(e)); }
  | GET_QE_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    term[e,e2]
    { cmd->reset(new GetQuantifierEliminationCommand(e, true)); }
  | GET_QE_DISJUNCT_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    term[e,e2]
    { cmd->reset(new GetQuantifierEliminationCommand(e, false)); }
  ;


datatypes_2_5_DefCommand[bool isCo, std::unique_ptr<CVC4::Command>* cmd]
@declarations {
  std::vector<CVC4::Datatype> dts;
  std::string name;
  std::vector<Type> sorts;
  std::vector<std::string> dnames;
  std::vector<unsigned> arities;
}
  : { PARSER_STATE->checkThatLogicIsSet();
    /* open a scope to keep the UnresolvedTypes contained */
    PARSER_STATE->pushScope(true); }
  LPAREN_TOK /* parametric sorts */
  ( symbol[name,CHECK_UNDECLARED,SYM_SORT]
    { sorts.push_back( PARSER_STATE->mkSort(name) ); }
  )*
  RPAREN_TOK
  LPAREN_TOK ( LPAREN_TOK datatypeDef[isCo, dts, sorts] RPAREN_TOK )+ RPAREN_TOK
  { PARSER_STATE->popScope();
    cmd->reset(new DatatypeDeclarationCommand(PARSER_STATE->mkMutualDatatypeTypes(dts, true)));
  }
  ;
  
datatypeDefCommand[bool isCo, std::unique_ptr<CVC4::Command>* cmd]  
@declarations {
  std::vector<CVC4::Datatype> dts;
  std::string name;
  std::vector<std::string> dnames;
  std::vector<int> arities;
}
 : { PARSER_STATE->checkThatLogicIsSet(); }
 symbol[name,CHECK_UNDECLARED,SYM_SORT]
 {
   dnames.push_back(name);
   arities.push_back(-1);
 }
 datatypesDef[isCo, dnames, arities, cmd]
 ;
  
datatypesDefCommand[bool isCo, std::unique_ptr<CVC4::Command>* cmd]
@declarations {
  std::vector<CVC4::Datatype> dts;
  std::string name;
  std::vector<std::string> dnames;
  std::vector<int> arities;
}
  : { PARSER_STATE->checkThatLogicIsSet(); }
  LPAREN_TOK /* datatype definition prelude */
  ( LPAREN_TOK symbol[name,CHECK_UNDECLARED,SYM_SORT] n=INTEGER_LITERAL RPAREN_TOK
    { unsigned arity = AntlrInput::tokenToUnsigned(n);
      Debug("parser-dt") << "Datatype : " << name << ", arity = " << arity << std::endl;
      dnames.push_back(name);
      arities.push_back( static_cast<int>(arity) );
    }
  )*
  RPAREN_TOK 
  LPAREN_TOK 
  datatypesDef[isCo, dnames, arities, cmd]
  RPAREN_TOK
  ;

/**
 * Read a list of datatype definitions for datatypes with names dnames and
 * parametric arities arities. A negative value in arities indicates that the
 * arity for the corresponding datatype has not been fixed.
 */
datatypesDef[bool isCo,
             const std::vector<std::string>& dnames,
             const std::vector<int>& arities,
             std::unique_ptr<CVC4::Command>* cmd]
@declarations {
  std::vector<CVC4::Datatype> dts;
  std::string name;
  std::vector<Type> params;
}
  : { PARSER_STATE->pushScope(true); }
    ( LPAREN_TOK {
      params.clear(); 
      Debug("parser-dt") << "Processing datatype #" << dts.size() << std::endl;
      if( dts.size()>=dnames.size() ){
        PARSER_STATE->parseError("Too many datatypes defined in this block.");
      }
    }
    ( PAR_TOK { PARSER_STATE->pushScope(true); } LPAREN_TOK
      ( symbol[name,CHECK_UNDECLARED,SYM_SORT]
        { params.push_back( PARSER_STATE->mkSort(name) ); }
      )*
      RPAREN_TOK {
        // if the arity was fixed by prelude and is not equal to the number of parameters
        if( arities[dts.size()]>=0 && static_cast<int>(params.size())!=arities[dts.size()] ){
          PARSER_STATE->parseError("Wrong number of parameters for datatype.");
        }
        Debug("parser-dt") << params.size() << " parameters for " << dnames[dts.size()] << std::endl;
        dts.push_back(Datatype(dnames[dts.size()],params,isCo));
      }
      LPAREN_TOK
      ( LPAREN_TOK constructorDef[dts.back()] RPAREN_TOK )+
      RPAREN_TOK { PARSER_STATE->popScope(); } 
    | { // if the arity was fixed by prelude and is not equal to 0
        if( arities[dts.size()]>0 ){
          PARSER_STATE->parseError("No parameters given for datatype.");
        }
        Debug("parser-dt") << params.size() << " parameters for " << dnames[dts.size()] << std::endl;
        dts.push_back(Datatype(dnames[dts.size()],params,isCo));
      }
      ( LPAREN_TOK constructorDef[dts.back()] RPAREN_TOK )+
    )
    RPAREN_TOK
    )+
  {
    PARSER_STATE->popScope();
    cmd->reset(new DatatypeDeclarationCommand(PARSER_STATE->mkMutualDatatypeTypes(dts, true))); 
  }
  ;

rewriterulesCommand[std::unique_ptr<CVC4::Command>* cmd]
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
      cmd->reset(new AssertCommand(expr, false)); }
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
      cmd->reset(new AssertCommand(expr, false));
    }
  ;

rewritePropaKind[CVC4::Kind& kind]
  : REDUCTION_RULE_TOK    { $kind = CVC4::kind::RR_REDUCTION; }
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
  | HEX_LITERAL
    { assert( AntlrInput::tokenText($HEX_LITERAL).find("#x") == 0 );
      std::string hexString = AntlrInput::tokenTextSubstr($HEX_LITERAL, 2);
      sexpr = SExpr(Integer(hexString, 16));
    }
  | BINARY_LITERAL
    { assert( AntlrInput::tokenText($BINARY_LITERAL).find("#b") == 0 );
      std::string binString = AntlrInput::tokenTextSubstr($BINARY_LITERAL, 2);
      sexpr = SExpr(Integer(binString, 2));
    }
  | str[s,false]
    { sexpr = SExpr(s); }
//  | LPAREN_TOK STRCST_TOK
//      ( INTEGER_LITERAL {
//      s_vec.push_back( atoi( AntlrInput::tokenText($INTEGER_LITERAL) ) + 65 );
//    } )* RPAREN_TOK
//   {
//  sexpr = SExpr( MK_CONST( ::CVC4::String(s_vec) ) );
//  }
  | symbol[s,CHECK_NONE,SYM_SORT]
    { sexpr = SExpr(SExpr::Keyword(s)); }
  | tok=(ASSERT_TOK | CHECKSAT_TOK | DECLARE_FUN_TOK | DECLARE_SORT_TOK
        | DEFINE_FUN_TOK | DEFINE_FUN_REC_TOK | DEFINE_FUNS_REC_TOK
        | DEFINE_SORT_TOK | GET_VALUE_TOK | GET_ASSIGNMENT_TOK
        | GET_ASSERTIONS_TOK | GET_PROOF_TOK | GET_UNSAT_CORE_TOK | EXIT_TOK
        | RESET_TOK | RESET_ASSERTIONS_TOK | SET_LOGIC_TOK | SET_INFO_TOK
        | GET_INFO_TOK | SET_OPTION_TOK | GET_OPTION_TOK | PUSH_TOK | POP_TOK
        | DECLARE_DATATYPES_TOK | GET_MODEL_TOK | ECHO_TOK | REWRITE_RULE_TOK
        | REDUCTION_RULE_TOK | PROPAGATION_RULE_TOK | SIMPLIFY_TOK)
    { sexpr = SExpr(SExpr::Keyword(AntlrInput::tokenText($tok))); }
  | builtinOp[k]
    { std::stringstream ss;
      ss << language::SetLanguage(CVC4::language::output::LANG_SMTLIB_V2_5)
         << EXPR_MANAGER->mkConst(k);
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
    ( symbolicExpr[sexpr] { children.push_back(sexpr); } )* RPAREN_TOK
    { sexpr = SExpr(children); }
  ;

/**
 * Matches a term.
 * @return the expression representing the formula
 */
term[CVC4::Expr& expr, CVC4::Expr& expr2]
@init {
  std::string name;
}
: termNonVariable[expr, expr2]
    /* a variable */
  | symbol[name,CHECK_DECLARED,SYM_VARIABLE]
    { expr = PARSER_STATE->getExpressionForName(name); 
      assert( !expr.isNull() );
    }
  ;

/**
 * Matches a term.
 * @return the expression representing the formula
 */
termNonVariable[CVC4::Expr& expr, CVC4::Expr& expr2]
@init {
  Debug("parser") << "term: " << AntlrInput::tokenText(LT(1)) << std::endl;
  Kind kind = kind::NULL_EXPR;
  Expr op;
  std::string name, name2;
  std::vector<Expr> args;
  std::vector< std::pair<std::string, Type> > sortedVarNames;
  Expr f, f2, f3, f4;
  std::string attr;
  Expr attexpr;
  std::vector<Expr> patexprs;
  std::vector<Expr> patconds;
  std::unordered_set<std::string> names;
  std::vector< std::pair<std::string, Expr> > binders;
  Type type;
  std::string s;
  bool isBuiltinOperator = false;
  bool isOverloadedFunction = false;
  bool readVariable = false;
  int match_vindex = -1;
  std::vector<Type> match_ptypes;
}
  : /* a built-in operator application */
    LPAREN_TOK builtinOp[kind] termList[args,expr] RPAREN_TOK
    {
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
      } else if( ( kind == CVC4::kind::EQUAL ||
                   kind == CVC4::kind::LT || kind == CVC4::kind::GT ||
                   kind == CVC4::kind::LEQ || kind == CVC4::kind::GEQ ) &&
                 args.size() > 2 ) {
        /* "chainable", but CVC4 internally only supports 2 args */
        expr = MK_EXPR(MK_CONST(Chain(kind)), args);
      } else if( PARSER_STATE->strictModeEnabled() && kind == CVC4::kind::ABS &&
                 args.size() == 1 && !args[0].getType().isInteger() ) {
        /* first, check that ABS is even defined in this logic */
        PARSER_STATE->checkOperator(kind, args.size());
        PARSER_STATE->parseError("abs can only be applied to Int, not Real, "
                                 "while in strict SMT-LIB compliance mode");
      } else {
        PARSER_STATE->checkOperator(kind, args.size());
        expr = MK_EXPR(kind, args);
      }
    }
  | LPAREN_TOK AS_TOK ( termNonVariable[f, f2] | symbol[name,CHECK_DECLARED,SYM_VARIABLE] { readVariable = true; } ) 
    sortSymbol[type, CHECK_DECLARED] RPAREN_TOK
    {
      if(readVariable) {
        Trace("parser-overloading") << "Getting variable expression of type " << name << " with type " << type << std::endl;
        // get the variable expression for the type
        f = PARSER_STATE->getExpressionForNameAndType(name, type); 
        assert( !f.isNull() );
      }
      if(f.getKind() == CVC4::kind::APPLY_CONSTRUCTOR && type.isDatatype()) {
        // could be a parametric type constructor or just an overloaded constructor
        if(((DatatypeType)type).isParametric()) {
          std::vector<CVC4::Expr> v;
          Expr e = f.getOperator();
          const DatatypeConstructor& dtc =
              Datatype::datatypeOf(e)[Datatype::indexOf(e)];
          v.push_back(MK_EXPR( CVC4::kind::APPLY_TYPE_ASCRIPTION,
                               MK_CONST(AscriptionType(dtc.getSpecializedConstructorType(type))), f.getOperator() ));
          v.insert(v.end(), f.begin(), f.end());
          expr = MK_EXPR(CVC4::kind::APPLY_CONSTRUCTOR, v);
        }else{
          expr = f;
        }
      } else if(f.getKind() == CVC4::kind::EMPTYSET) {
        Debug("parser") << "Empty set encountered: " << f << " "
                          << f2 << " " << type <<  std::endl;
        expr = MK_CONST( ::CVC4::EmptySet(type) );
      } else if(f.getKind() == CVC4::kind::UNIVERSE_SET) {
        expr = EXPR_MANAGER->mkNullaryOperator(type, kind::UNIVERSE_SET);
      } else if(f.getKind() == CVC4::kind::SEP_NIL) {
        //We don't want the nil reference to be a constant: for instance, it
        //could be of type Int but is not a const rational. However, the
        //expression has 0 children. So we convert to a SEP_NIL variable.
        expr = EXPR_MANAGER->mkNullaryOperator(type, kind::SEP_NIL);
      } else {
        if(f.getType() != type) {
          PARSER_STATE->parseError("Type ascription not satisfied.");
        }else{
          expr = f;
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
          PARSER_STATE->parseError("Use Exists instead of Forall for a rewrite "
                                   "rule.");
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
  | LPAREN_TOK functionName[name, CHECK_NONE]
    { isBuiltinOperator = PARSER_STATE->isOperatorEnabled(name);
      if(isBuiltinOperator) {
        /* A built-in operator not already handled by the lexer */
        kind = PARSER_STATE->getOperatorKind(name);
      } else {
        /* A non-built-in function application */
        PARSER_STATE->checkDeclaration(name, CHECK_DECLARED, SYM_VARIABLE);
        expr = PARSER_STATE->getVariable(name);
        if(!expr.isNull()) {
          //hack to allow constants with parentheses (disabled for now)
          //if( PARSER_STATE->sygus() && !PARSER_STATE->isFunctionLike(expr) ){
          //  op = PARSER_STATE->getVariable(name);
          //}else{
          PARSER_STATE->checkFunctionLike(expr);
          kind = PARSER_STATE->getKindForFunction(expr);
          args.push_back(expr);
        }else{
          isOverloadedFunction = true;
        }
      }
    }
    //(termList[args,expr])? RPAREN_TOK
    termList[args,expr] RPAREN_TOK
    { Debug("parser") << "args has size " << args.size() << std::endl
                      << "expr is " << expr << std::endl;
      for(std::vector<Expr>::iterator i = args.begin(); i != args.end(); ++i) {
        Debug("parser") << "++ " << *i << std::endl;
      }
      if(isOverloadedFunction) {
        std::vector< Type > argTypes;
        for(std::vector<Expr>::iterator i = args.begin(); i != args.end(); ++i) {
          argTypes.push_back( (*i).getType() );
        }
        expr = PARSER_STATE->getOverloadedFunctionForTypes(name, argTypes);
        if(!expr.isNull()) {
          PARSER_STATE->checkFunctionLike(expr);
          kind = PARSER_STATE->getKindForFunction(expr);
          args.insert(args.begin(),expr);
        }else{
          PARSER_STATE->parseError("Cannot find unambiguous overloaded function for argument types.");
        }
      }
      if(isBuiltinOperator) {
        PARSER_STATE->checkOperator(kind, args.size());
      }
      // may be partially applied function, in this case we should use HO_APPLY
      if( args.size()>=2 && args[0].getType().isFunction() &&
          (args.size()-1)<((FunctionType)args[0].getType()).getArity() ){
        Debug("parser") << "Partial application of " << args[0];
        Debug("parser") << " : #argTypes = " << ((FunctionType)args[0].getType()).getArity();
        Debug("parser") << ", #args = " << args.size()-1 << std::endl;
        // must curry the application
        expr = args[0];
        expr = PARSER_STATE->mkHoApply( expr, args, 1 );
      }else{
        expr = MK_EXPR(kind, args);
      }
    }

  | LPAREN_TOK
    ( /* An indexed function application */
      indexedFunctionName[op, kind] termList[args,expr] RPAREN_TOK { 
        if(kind==CVC4::kind::APPLY_SELECTOR) {
          //tuple selector case
          Integer x = op.getConst<CVC4::Rational>().getNumerator();
          if (!x.fitsUnsignedInt()) {
            PARSER_STATE->parseError("index of tupSel is larger than size of unsigned int");
          }
          unsigned int n = x.toUnsignedInt();
          if (args.size()>1) {
            PARSER_STATE->parseError("tupSel applied to more than one tuple argument");
          }
          Type t = args[0].getType();
          if (!t.isTuple()) {
            PARSER_STATE->parseError("tupSel applied to non-tuple");
          }
          size_t length = ((DatatypeType)t).getTupleLength();
          if (n >= length) {
            std::stringstream ss;
            ss << "tuple is of length " << length << "; cannot access index " << n;
            PARSER_STATE->parseError(ss.str());
          }
          const Datatype & dt = ((DatatypeType)t).getDatatype();
          op = dt[0][n].getSelector();
        }
        if (kind!=kind::NULL_EXPR) {
          expr = MK_EXPR( kind, op, args );
        } else {
          expr = MK_EXPR(op, args);
        }
        PARSER_STATE->checkOperator(expr.getKind(), args.size());
      }
    | /* Array constant (in Z3 syntax) */
      LPAREN_TOK AS_TOK CONST_TOK sortSymbol[type, CHECK_DECLARED]
      RPAREN_TOK term[f, f2] RPAREN_TOK
      {
        if(!type.isArray()) {
          std::stringstream ss;
          ss << "expected array constant term, but cast is not of array type"
             << std::endl
             << "cast type: " << type;
          PARSER_STATE->parseError(ss.str());
        }
        if(!f.isConst()) {
          std::stringstream ss;
          ss << "expected constant term inside array constant, but found "
             << "nonconstant term:" << std::endl
             << "the term: " << f;
          PARSER_STATE->parseError(ss.str());
        }
        if(!ArrayType(type).getConstituentType().isComparableTo(f.getType())) {
          std::stringstream ss;
          ss << "type mismatch inside array constant term:" << std::endl
             << "array type:          " << type << std::endl
             << "expected const type: " << ArrayType(type).getConstituentType()
             << std::endl
             << "computed const type: " << f.getType();
          PARSER_STATE->parseError(ss.str());
        }
        expr = MK_CONST( ::CVC4::ArrayStoreAll(type, f) );
      }
    )
  | /* a let or sygus let binding */
    LPAREN_TOK ( 
      LET_TOK LPAREN_TOK
      { PARSER_STATE->pushScope(true); }
      ( LPAREN_TOK symbol[name,CHECK_NONE,SYM_VARIABLE]
        term[expr, f2]
        RPAREN_TOK
        // this is a parallel let, so we have to save up all the contributions
        // of the let and define them only later on
        { if(names.count(name) == 1) {
            std::stringstream ss;
            ss << "warning: symbol `" << name << "' bound multiple times by let;"
               << " the last binding will be used, shadowing earlier ones";
            PARSER_STATE->warning(ss.str());
          } else {
            names.insert(name);
          }
          binders.push_back(std::make_pair(name, expr)); } )+ |
      SYGUS_LET_TOK LPAREN_TOK
      { PARSER_STATE->pushScope(true); }
      ( LPAREN_TOK symbol[name,CHECK_NONE,SYM_VARIABLE]
        sortSymbol[type,CHECK_DECLARED]
        term[expr, f2]
        RPAREN_TOK
        // this is a parallel let, so we have to save up all the contributions
        // of the let and define them only later on
        { if(names.count(name) == 1) {
            std::stringstream ss;
            ss << "warning: symbol `" << name << "' bound multiple times by let;"
               << " the last binding will be used, shadowing earlier ones";
            PARSER_STATE->warning(ss.str());
          } else {
            names.insert(name);
          }
          binders.push_back(std::make_pair(name, expr)); } )+ )
    { // now implement these bindings
      for(std::vector< std::pair<std::string, Expr> >::iterator
            i = binders.begin(); i != binders.end(); ++i) {
        PARSER_STATE->defineVar((*i).first, (*i).second);
      }
    }
    RPAREN_TOK
    term[expr, f2]
    RPAREN_TOK
    { PARSER_STATE->popScope(); }
  | /* match expression */
    LPAREN_TOK MATCH_TOK term[expr, f2] {
      if( !expr.getType().isDatatype() ){
        PARSER_STATE->parseError("Cannot match on non-datatype term.");
      }
    }
    LPAREN_TOK
    ( 
      /* match cases */
       LPAREN_TOK INDEX_TOK term[f, f2] { 
          if( match_vindex==-1 ){
            match_vindex = (int)patexprs.size(); 
          }
          patexprs.push_back( f ); 
          patconds.push_back(MK_CONST(bool(true)));
        }
        RPAREN_TOK
      | LPAREN_TOK LPAREN_TOK term[f, f2] { 
           args.clear(); 
           PARSER_STATE->pushScope(true); 
           //f should be a constructor
           type = f.getType();
           Debug("parser-dt") << "Pattern head : " << f << " " << f.getType() << std::endl;
           if( !type.isConstructor() ){
             PARSER_STATE->parseError("Pattern must be application of a constructor or a variable.");
           }
           if( Datatype::datatypeOf(f).isParametric() ){
             type = Datatype::datatypeOf(f)[Datatype::indexOf(f)].getSpecializedConstructorType(expr.getType());
           }
           match_ptypes = ((ConstructorType)type).getArgTypes();
         }
         //arguments
         ( symbol[name,CHECK_NONE,SYM_VARIABLE] {
             if( args.size()>=match_ptypes.size() ){
               PARSER_STATE->parseError("Too many arguments for pattern.");
             }
             //make of proper type
             Expr arg = PARSER_STATE->mkBoundVar(name, match_ptypes[args.size()]);
             args.push_back( arg );
           }
         )*
         RPAREN_TOK
         term[f3, f2] { 
           const DatatypeConstructor& dtc = Datatype::datatypeOf(f)[Datatype::indexOf(f)];
           if( args.size()!=dtc.getNumArgs() ){
             PARSER_STATE->parseError("Bad number of arguments for application of constructor in pattern.");
           }
           //FIXME: make MATCH a kind and make this a rewrite
           // build a lambda
           std::vector<Expr> largs;
           largs.push_back( MK_EXPR( CVC4::kind::BOUND_VAR_LIST, args ) );
           largs.push_back( f3 );
           std::vector< Expr > aargs;
           aargs.push_back( MK_EXPR( CVC4::kind::LAMBDA, largs ) );
           for( unsigned i=0; i<dtc.getNumArgs(); i++ ){
             //can apply total version since we will be guarded by ITE condition
             // however, we need to apply partial version since we don't have the internal selector available
             aargs.push_back( MK_EXPR( CVC4::kind::APPLY_SELECTOR, dtc[i].getSelector(), expr ) );
           }
           patexprs.push_back( MK_EXPR( CVC4::kind::APPLY, aargs ) );
           patconds.push_back( MK_EXPR( CVC4::kind::APPLY_TESTER, dtc.getTester(), expr ) );
         }
         RPAREN_TOK 
         { PARSER_STATE->popScope(); }
       | LPAREN_TOK symbol[name,CHECK_DECLARED,SYM_VARIABLE] {
           f = PARSER_STATE->getVariable(name);
           type = f.getType();
           if( !type.isConstructor() || !((ConstructorType)type).getArgTypes().empty() ){
             PARSER_STATE->parseError("Must apply constructors of arity greater than 0 to arguments in pattern.");
           }
         }
         term[f3, f2] {
           const DatatypeConstructor& dtc = Datatype::datatypeOf(f)[Datatype::indexOf(f)];
           patexprs.push_back( f3 );
           patconds.push_back( MK_EXPR( CVC4::kind::APPLY_TESTER, dtc.getTester(), expr ) );
         }
         RPAREN_TOK
    )+
    RPAREN_TOK RPAREN_TOK  { 
      if( match_vindex==-1 ){
        const Datatype& dt = ((DatatypeType)expr.getType()).getDatatype();
        std::map< unsigned, bool > processed;
        unsigned count = 0;
        //ensure that all datatype constructors are matched (to ensure exhaustiveness)
        for( unsigned i=0; i<patconds.size(); i++ ){
          unsigned curr_index = Datatype::indexOf(patconds[i].getOperator());
          if( curr_index<0 && curr_index>=dt.getNumConstructors() ){
            PARSER_STATE->parseError("Pattern is not legal for the head of a match.");
          }
          if( processed.find( curr_index )==processed.end() ){
            processed[curr_index] = true;
            count++;
          }
        }
        if( count!=dt.getNumConstructors() ){
          PARSER_STATE->parseError("Patterns are not exhaustive in a match construct.");
        }
      }
      //now, make the ITE
      int end_index = match_vindex==-1 ? patexprs.size()-1 : match_vindex;
      bool first_time = true;
      for( int index = end_index; index>=0; index-- ){
        if( first_time ){
          expr = patexprs[index];
          first_time = false;
        }else{
          expr = MK_EXPR( CVC4::kind::ITE, patconds[index], patexprs[index], expr );
        }
      }
    }
  | symbol[name,CHECK_NONE,SYM_VARIABLE] SYGUS_ENUM_CONS_TOK
    symbol[name2,CHECK_NONE,SYM_VARIABLE]
    { std::string cname = name + "__Enum__" + name2;
      Debug("parser-sygus") << "Check for enum const " << cname << std::endl;
      expr = PARSER_STATE->getVariable(cname);
      // expr.getType().isConstructor() &&
      // ConstructorType(expr.getType()).getArity()==0;
      expr = MK_EXPR(CVC4::kind::APPLY_CONSTRUCTOR, expr);
    }

    /* attributed expressions */
  | LPAREN_TOK ATTRIBUTE_TOK term[expr, f2]
    ( attribute[expr, attexpr, attr]
      { if( ! attexpr.isNull()) {
          patexprs.push_back( attexpr );
        }
      }
    )+ RPAREN_TOK
    {
      if(attr == ":rewrite-rule") {
        Expr guard;
        Expr body;
        if(expr[1].getKind() == kind::IMPLIES ||
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

        if( body.getKind()==kind::IMPLIES ){  
          kind = kind::RR_DEDUCTION;
        }else if( body.getKind()==kind::EQUAL ){
          kind = body[0].getType().isBoolean() ? kind::RR_REDUCTION : kind::RR_REWRITE;
        }else{
          PARSER_STATE->parseError("Error parsing rewrite rule.");
        }
        expr = MK_EXPR( kind, args );
      } else if(! patexprs.empty()) {
        if( !f2.isNull() && f2.getKind()==kind::INST_PATTERN_LIST ){
          for( size_t i=0; i<f2.getNumChildren(); i++ ){
            if( f2[i].getKind()==kind::INST_PATTERN ){
              patexprs.push_back( f2[i] );
            }else{
              std::stringstream ss;
              ss << "warning: rewrite rules do not support " << f2[i]
                 << " within instantiation pattern list";
              PARSER_STATE->warning(ss.str());
            }
          }
        }
        expr2 = MK_EXPR(kind::INST_PATTERN_LIST, patexprs);
      } else {
        expr2 = f2;
      }
    }
  | /* lambda */
    LPAREN_TOK HO_LAMBDA_TOK
    LPAREN_TOK sortedVarList[sortedVarNames] RPAREN_TOK
    {
      PARSER_STATE->pushScope(true);
      for(const std::pair<std::string, CVC4::Type>& svn : sortedVarNames){
        args.push_back(PARSER_STATE->mkBoundVar(svn.first, svn.second));
      }
      Expr bvl = MK_EXPR(kind::BOUND_VAR_LIST, args);
      args.clear();
      args.push_back(bvl);
    }
    term[f, f2] RPAREN_TOK
    {
      args.push_back( f );
      PARSER_STATE->popScope();
      expr = MK_EXPR( CVC4::kind::LAMBDA, args );
    }
    /* constants */
  | INTEGER_LITERAL
    { expr = MK_CONST( AntlrInput::tokenToInteger($INTEGER_LITERAL) ); }

  | DECIMAL_LITERAL
    { // FIXME: This doesn't work because an SMT rational is not a
      // valid GMP rational string
      expr = MK_CONST( AntlrInput::tokenToRational($DECIMAL_LITERAL) ); 
      if(expr.getType().isInteger()) {
        //must cast to Real to ensure correct type is passed to parametric type constructors
        expr = MK_EXPR(kind::TO_REAL, expr);
      }  
    }

  | LPAREN_TOK INDEX_TOK 
    ( bvLit=SIMPLE_SYMBOL size=INTEGER_LITERAL 
      { if(AntlrInput::tokenText($bvLit).find("bv") == 0) {
           expr = MK_CONST( AntlrInput::tokenToBitvector($bvLit, $size) );
        } else {
           PARSER_STATE->parseError("Unexpected symbol `" +
                                    AntlrInput::tokenText($bvLit) + "'");
        }
      }
    | FP_PINF_TOK eb=INTEGER_LITERAL sb=INTEGER_LITERAL
      { expr = MK_CONST(FloatingPoint::makeInf(FloatingPointSize(AntlrInput::tokenToUnsigned($eb),
                                                                 AntlrInput::tokenToUnsigned($sb)),
                                               false)); }
    | FP_NINF_TOK eb=INTEGER_LITERAL sb=INTEGER_LITERAL
      { expr = MK_CONST(FloatingPoint::makeInf(FloatingPointSize(AntlrInput::tokenToUnsigned($eb),
                                                                 AntlrInput::tokenToUnsigned($sb)),
                                               true)); }
    | FP_NAN_TOK eb=INTEGER_LITERAL sb=INTEGER_LITERAL
      { expr = MK_CONST(FloatingPoint::makeNaN(FloatingPointSize(AntlrInput::tokenToUnsigned($eb),
                                                                 AntlrInput::tokenToUnsigned($sb)))); }

    | FP_PZERO_TOK eb=INTEGER_LITERAL sb=INTEGER_LITERAL
      { expr = MK_CONST(FloatingPoint::makeZero(FloatingPointSize(AntlrInput::tokenToUnsigned($eb),
                                                                AntlrInput::tokenToUnsigned($sb)),
                                              false)); }
    | FP_NZERO_TOK eb=INTEGER_LITERAL sb=INTEGER_LITERAL
      { expr = MK_CONST(FloatingPoint::makeZero(FloatingPointSize(AntlrInput::tokenToUnsigned($eb),
                                                                AntlrInput::tokenToUnsigned($sb)),
                                              true)); }
    // NOTE: Theory parametric constants go here

    )
    RPAREN_TOK

  | HEX_LITERAL
    { assert( AntlrInput::tokenText($HEX_LITERAL).find("#x") == 0 );
      std::string hexString = AntlrInput::tokenTextSubstr($HEX_LITERAL, 2);
      expr = MK_CONST( BitVector(hexString, 16) ); }

  | BINARY_LITERAL
    { assert( AntlrInput::tokenText($BINARY_LITERAL).find("#b") == 0 );
      std::string binString = AntlrInput::tokenTextSubstr($BINARY_LITERAL, 2);
      expr = MK_CONST( BitVector(binString, 2) ); }

  | str[s,false]
    { expr = MK_CONST( ::CVC4::String(s, true) ); }
  | FP_RNE_TOK      { expr = MK_CONST(roundNearestTiesToEven); }
  | FP_RNA_TOK      { expr = MK_CONST(roundNearestTiesToAway); }
  | FP_RTP_TOK      { expr = MK_CONST(roundTowardPositive); }
  | FP_RTN_TOK      { expr = MK_CONST(roundTowardNegative); }
  | FP_RTZ_TOK      { expr = MK_CONST(roundTowardZero); }
  | FP_RNE_FULL_TOK { expr = MK_CONST(roundNearestTiesToEven); }
  | FP_RNA_FULL_TOK { expr = MK_CONST(roundNearestTiesToAway); }
  | FP_RTP_FULL_TOK { expr = MK_CONST(roundTowardPositive); }
  | FP_RTN_FULL_TOK { expr = MK_CONST(roundTowardNegative); }
  | FP_RTZ_FULL_TOK { expr = MK_CONST(roundTowardZero); }

  | REAL_PI_TOK {
      expr = EXPR_MANAGER->mkNullaryOperator(EXPR_MANAGER->realType(), kind::PI);
    }

  | RENOSTR_TOK
    { std::vector< Expr > nvec;
      expr = MK_EXPR( CVC4::kind::REGEXP_EMPTY, nvec );
    }

  | REALLCHAR_TOK
    { std::vector< Expr > nvec;
      expr = MK_EXPR( CVC4::kind::REGEXP_SIGMA, nvec );
    }

  | EMPTYSET_TOK
    { expr = MK_CONST( ::CVC4::EmptySet(Type())); }

  | UNIVSET_TOK
    { //booleanType is placeholder here since we don't have type info without type annotation
      expr = EXPR_MANAGER->mkNullaryOperator(EXPR_MANAGER->booleanType(), kind::UNIVERSE_SET); }

  | NILREF_TOK
    { //booleanType is placeholder here since we don't have type info without type annotation
      expr = EXPR_MANAGER->mkNullaryOperator(EXPR_MANAGER->booleanType(), kind::SEP_NIL); }
    // NOTE: Theory constants go here

  | LPAREN_TOK TUPLE_CONST_TOK termList[args,expr] RPAREN_TOK
    { std::vector<Type> types;
      for(std::vector<Expr>::const_iterator i = args.begin(); i != args.end(); ++i) {
        types.push_back((*i).getType());
      }
      DatatypeType t = EXPR_MANAGER->mkTupleType(types);
      const Datatype& dt = t.getDatatype();
      args.insert(args.begin(), dt[0].getConstructor());
      expr = MK_EXPR(kind::APPLY_CONSTRUCTOR, args);
    }
  
  | TUPLE_CONST_TOK
    { std::vector<Type> types;
      DatatypeType t = EXPR_MANAGER->mkTupleType(types);
      const Datatype& dt = t.getDatatype();
      args.insert(args.begin(), dt[0].getConstructor());
      expr = MK_EXPR(kind::APPLY_CONSTRUCTOR, args);
    }
  ;

/**
 * Read attribute
 */
attribute[CVC4::Expr& expr, CVC4::Expr& retExpr, std::string& attr]
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
        ss << "warning: Attribute " << attr
           << " does not take a value (ignoring)";
        PARSER_STATE->warning(ss.str());
      }
      // do nothing
    } else if(attr==":axiom" || attr==":conjecture" || attr==":fun-def" ||
              attr==":sygus" || attr==":synthesis") {
      if(hasValue) {
        std::stringstream ss;
        ss << "warning: Attribute " << attr
           << " does not take a value (ignoring)";
        PARSER_STATE->warning(ss.str());
      }
      Expr avar;
      bool success = true;
      std::string attr_name = attr;
      attr_name.erase( attr_name.begin() );
      if( attr==":fun-def" ){
        if( expr.getKind()!=kind::EQUAL || expr[0].getKind()!=kind::APPLY_UF ){
          success = false;
        }else{
          FunctionType t = (FunctionType)expr[0].getOperator().getType();
          for( unsigned i=0; i<expr[0].getNumChildren(); i++ ){
            if( expr[0][i].getKind() != kind::BOUND_VARIABLE ||
                expr[0][i].getType() != t.getArgTypes()[i] ){
              success = false;
              break;
            }else{
              for( unsigned j=0; j<i; j++ ){
                if( expr[0][j]==expr[0][i] ){
                  success = false;
                  break;
                }
              }
            }
          }
        }
        if( !success ){
          std::stringstream ss;
          ss << "warning: Function definition should be an equality whose LHS "
             << "is an uninterpreted function applied to unique variables.";
          PARSER_STATE->warning(ss.str());
        }else{
          avar = expr[0];
        }
      }else{
        Type t = EXPR_MANAGER->booleanType();
        avar = PARSER_STATE->mkVar(attr_name, t);
      }
      if( success ){
        //Will set the attribute on auxiliary var (preserves attribute on
        //formula through rewriting).
        retExpr = MK_EXPR(kind::INST_ATTRIBUTE, avar);
        Command* c = new SetUserAttributeCommand( attr_name, avar );
        c->setMuted(true);
        PARSER_STATE->preemptCommand(c);
      }
    } else {
      PARSER_STATE->attributeNotSupported(attr);
    }
  }
  | ATTRIBUTE_PATTERN_TOK LPAREN_TOK
    ( term[patexpr, e2]
      { patexprs.push_back( patexpr ); }
    )+ RPAREN_TOK
    {
      attr = std::string(":pattern");
      retExpr = MK_EXPR(kind::INST_PATTERN, patexprs);
    }
  | ATTRIBUTE_NO_PATTERN_TOK term[patexpr, e2]
    {
      attr = std::string(":no-pattern");
      retExpr = MK_EXPR(kind::INST_NO_PATTERN, patexpr);
    }
  | tok=( ATTRIBUTE_INST_LEVEL | ATTRIBUTE_RR_PRIORITY ) INTEGER_LITERAL
    {
      Expr n = MK_CONST( AntlrInput::tokenToInteger($INTEGER_LITERAL) );
      std::vector<Expr> values;
      values.push_back( n );
      std::string attr_name(AntlrInput::tokenText($tok));
      attr_name.erase( attr_name.begin() );
      Type t = EXPR_MANAGER->booleanType();
      Expr avar = PARSER_STATE->mkVar(attr_name, t);
      retExpr = MK_EXPR(kind::INST_ATTRIBUTE, avar);
      Command* c = new SetUserAttributeCommand( attr_name, avar, values );
      c->setMuted(true);
      PARSER_STATE->preemptCommand(c);
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
        ss << ":named annotations can only name terms that are closed; this "
           << "one contains free variables:";
        for(std::set<Expr>::const_iterator i = freeVars.begin();
            i != freeVars.end(); ++i) {
          ss << " " << *i;
        }
        PARSER_STATE->parseError(ss.str());
      }
      // check that sexpr is a fresh function symbol, and reserve it
      PARSER_STATE->reserveSymbolAtAssertionLevel(name);
      // define it
      Expr func = PARSER_STATE->mkFunction(name, expr.getType());
      // remember the last term to have been given a :named attribute
      PARSER_STATE->setLastNamedTerm(expr, name);
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
indexedFunctionName[CVC4::Expr& op, CVC4::Kind& kind]
@init {
  Expr expr;
  Expr expr2;
}
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
          PARSER_STATE->parseError(
              "bv2nat and int2bv are not part of SMT-LIB, and aren't available "
              "in SMT-LIB strict compliance mode");
        } }
    | FP_TO_FP_TOK eb=INTEGER_LITERAL sb=INTEGER_LITERAL
      { op = MK_CONST(FloatingPointToFPGeneric(
                AntlrInput::tokenToUnsigned($eb),
                AntlrInput::tokenToUnsigned($sb)));
      }
    | FP_TO_FPBV_TOK eb=INTEGER_LITERAL sb=INTEGER_LITERAL
      { op = MK_CONST(FloatingPointToFPIEEEBitVector(
                AntlrInput::tokenToUnsigned($eb),
                AntlrInput::tokenToUnsigned($sb)));
      }
    | FP_TO_FPFP_TOK eb=INTEGER_LITERAL sb=INTEGER_LITERAL
      { op = MK_CONST(FloatingPointToFPFloatingPoint(
                AntlrInput::tokenToUnsigned($eb),
                AntlrInput::tokenToUnsigned($sb)));
      }
    | FP_TO_FPR_TOK eb=INTEGER_LITERAL sb=INTEGER_LITERAL
      { op = MK_CONST(FloatingPointToFPReal(AntlrInput::tokenToUnsigned($eb),
                                            AntlrInput::tokenToUnsigned($sb)));
      }
    | FP_TO_FPS_TOK eb=INTEGER_LITERAL sb=INTEGER_LITERAL
      { op = MK_CONST(FloatingPointToFPSignedBitVector(
                AntlrInput::tokenToUnsigned($eb),
                AntlrInput::tokenToUnsigned($sb)));
      }
    | FP_TO_FPU_TOK eb=INTEGER_LITERAL sb=INTEGER_LITERAL
      { op = MK_CONST(FloatingPointToFPUnsignedBitVector(
                AntlrInput::tokenToUnsigned($eb),
                AntlrInput::tokenToUnsigned($sb)));
      }
    | FP_TO_UBV_TOK m=INTEGER_LITERAL
      { op = MK_CONST(FloatingPointToUBV(AntlrInput::tokenToUnsigned($m))); }
    | FP_TO_SBV_TOK m=INTEGER_LITERAL
      { op = MK_CONST(FloatingPointToSBV(AntlrInput::tokenToUnsigned($m))); }
    | TESTER_TOK term[expr, expr2] { 
        if( expr.getKind()==kind::APPLY_CONSTRUCTOR && expr.getNumChildren()==0 ){
          //for nullary constructors, must get the operator
          expr = expr.getOperator();
        }
        if( !expr.getType().isConstructor() ){
          PARSER_STATE->parseError("Bad syntax for test (_ is X), X must be a constructor.");
        }
        op = Datatype::datatypeOf(expr)[Datatype::indexOf(expr)].getTester();
        kind = CVC4::kind::APPLY_TESTER;
      }
    | TUPLE_SEL_TOK m=INTEGER_LITERAL {
        kind = CVC4::kind::APPLY_SELECTOR;
        //put m in op so that the caller (termNonVariable) can deal with this case
        op = MK_CONST(Rational(AntlrInput::tokenToUnsigned($m)));
      } 
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
  : id=(SIMPLE_SYMBOL | QUOTED_SYMBOL | UNTERMINATED_QUOTED_SYMBOL)
    { PARSER_STATE->parseError(std::string("Unknown indexed function `") +
          AntlrInput::tokenText($id) + "'");
    }
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
  : STRING_LITERAL_2_0
    { s = AntlrInput::tokenText($STRING_LITERAL_2_0);
      /* strip off the quotes */
      s = s.substr(1, s.size() - 2);
      for(size_t i=0; i<s.size(); i++) {
        if((unsigned)s[i] > 127 && !isprint(s[i])) {
          PARSER_STATE->parseError("Extended/unprintable characters are not "
                                   "part of SMT-LIB, and they must be encoded "
                                   "as escape sequences");
        }
      }
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
  | STRING_LITERAL_2_5
    { s = AntlrInput::tokenText($STRING_LITERAL_2_5);
      /* strip off the quotes */
      s = s.substr(1, s.size() - 2);
      for(size_t i=0; i<s.size(); i++) {
        if((unsigned)s[i] > 127 && !isprint(s[i])) {
          PARSER_STATE->parseError("Extended/unprintable characters are not "
                                   "part of SMT-LIB, and they must be encoded "
                                   "as escape sequences");
        }
      }
      // In the 2.5 version, always handle escapes (regardless of fsmtlib flag).
      char* p_orig = strdup(s.c_str());
      char *p = p_orig, *q = p_orig;
      while(*q != '\0') {
        if(*q == '"') {
          ++q;
          assert(*q == '"');
        }
        *p++ = *q++;
      }
      *p = '\0';
      s = p_orig;
      free(p_orig);
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

  | BV2NAT_TOK
    { $kind = CVC4::kind::BITVECTOR_TO_NAT;
      if(PARSER_STATE->strictModeEnabled()) {
        PARSER_STATE->parseError("bv2nat and int2bv are not part of SMT-LIB, "
                                 "and aren't available in SMT-LIB strict "
                                 "compliance mode");
      }
    }

  | DTSIZE_TOK       { $kind = CVC4::kind::DT_SIZE; }
  | FMFCARD_TOK      { $kind = CVC4::kind::CARDINALITY_CONSTRAINT; }
  | FMFCARDVAL_TOK   { $kind = CVC4::kind::CARDINALITY_VALUE; }
  | INST_CLOSURE_TOK { $kind = CVC4::kind::INST_CLOSURE; }
  
  // NOTE: Theory operators no longer go here, add to smt2.cpp. Only
  // special cases may go here. When this comment was written (2015
  // Apr), the special cases were: core theory operators, arith
  // operators which start with symbols like * / + >= etc, quantifier
  // theory operators, and operators which depended on parser's state
  // to accept or reject.
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
  : ( LPAREN_TOK symbol[name,CHECK_NONE,SYM_VARIABLE]
      sortSymbol[t,CHECK_DECLARED] RPAREN_TOK
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
  bool indexed = false;
}
  : sortName[name,CHECK_NONE]
    {
      if(check == CHECK_DECLARED || PARSER_STATE->isDeclared(name, SYM_SORT)) {
        t = PARSER_STATE->getSort(name);
      } else {
        t = PARSER_STATE->mkUnresolvedType(name);
      }
    }
  | LPAREN_TOK (INDEX_TOK {indexed = true;} | {indexed = false;})
    symbol[name,CHECK_NONE,SYM_SORT]
    ( nonemptyNumeralList[numerals]
      { // allow sygus inputs to elide the `_'
        if( !indexed && !PARSER_STATE->sygus() ) {
          std::stringstream ss;
          ss << "SMT-LIB requires use of an indexed sort here, e.g. (_ " << name
             << " ...)";
          PARSER_STATE->parseError(ss.str());
        }
        if( name == "BitVec" ) {
          if( numerals.size() != 1 ) {
            PARSER_STATE->parseError("Illegal bitvector type.");
          }
          if(numerals.front() == 0) {
            PARSER_STATE->parseError("Illegal bitvector size: 0");
          }
          t = EXPR_MANAGER->mkBitVectorType(numerals.front());
        } else if ( name == "FloatingPoint" ) {
          if( numerals.size() != 2 ) {
            PARSER_STATE->parseError("Illegal floating-point type.");
          }
          if(!validExponentSize(numerals[0])) {
            PARSER_STATE->parseError("Illegal floating-point exponent size");
          }
          if(!validSignificandSize(numerals[1])) {
            PARSER_STATE->parseError("Illegal floating-point significand size");
          }
          t = EXPR_MANAGER->mkFloatingPointType(numerals[0],numerals[1]);
        } else {
          std::stringstream ss;
          ss << "unknown indexed sort symbol `" << name << "'";
          PARSER_STATE->parseError(ss.str());
        }
      }
    | sortList[args]
      { if( indexed ) {
          std::stringstream ss;
          ss << "Unexpected use of indexing operator `_' before `" << name
             << "', try leaving it out";
          PARSER_STATE->parseError(ss.str());
        }
        if(args.empty()) {
          PARSER_STATE->parseError("Extra parentheses around sort name not "
                                   "permitted in SMT-LIB");
        } else if(name == "Array" &&
           PARSER_STATE->isTheoryEnabled(Smt2::THEORY_ARRAYS) ) {
          if(args.size() != 2) {
            PARSER_STATE->parseError("Illegal array type.");
          }
          t = EXPR_MANAGER->mkArrayType( args[0], args[1] );
        } else if(name == "Set" &&
                  PARSER_STATE->isTheoryEnabled(Smt2::THEORY_SETS) ) {
          if(args.size() != 1) {
            PARSER_STATE->parseError("Illegal set type.");
          }
          t = EXPR_MANAGER->mkSetType( args[0] );
        } else if(name == "Tuple") {
          t = EXPR_MANAGER->mkTupleType(args); 
        } else if(check == CHECK_DECLARED ||
                  PARSER_STATE->isDeclared(name, SYM_SORT)) {
          t = PARSER_STATE->getSort(name, args);
        } else {
          // make unresolved type
          if(args.empty()) {
            t = PARSER_STATE->mkUnresolvedType(name);
            Debug("parser-param") << "param: make unres type " << name
                                  << std::endl;
          } else {
            t = PARSER_STATE->mkUnresolvedTypeConstructor(name,args);
            t = SortConstructorType(t).instantiate( args );
            Debug("parser-param")
                << "param: make unres param type " << name << " " << args.size()
                << " " << PARSER_STATE->getArity( name ) << std::endl;
          }
        }
      }
    ) RPAREN_TOK
  | LPAREN_TOK HO_ARROW_TOK sortList[args] RPAREN_TOK
    {
      if(args.size()<2) {
        PARSER_STATE->parseError("Arrow types must have at least 2 arguments");
      }
      //flatten the type
      Type rangeType = args.back();
      args.pop_back();
      t = PARSER_STATE->mkFlatFunctionType( args, rangeType );
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
  | ( 'repeat' { id = "repeat"; }
    /* these are keywords in SyGuS but we don't want to inhibit their
     * use as symbols in SMT-LIB */
    | SET_OPTIONS_TOK { id = "set-options"; }
    | DECLARE_VAR_TOK { id = "declare-var"; }
    | DECLARE_PRIMED_VAR_TOK { id = "declare-primed-var"; }
    | SYNTH_FUN_TOK { id = "synth-fun"; }
    | SYNTH_INV_TOK { id = "synth-inv"; }
    | CONSTRAINT_TOK { id = "constraint"; }
    | INV_CONSTRAINT_TOK { id = "inv-constraint"; }
    | CHECK_SYNTH_TOK { id = "check-synth"; }
    )
    { PARSER_STATE->checkDeclaration(id, check, type); }
  | QUOTED_SYMBOL
    { id = AntlrInput::tokenText($QUOTED_SYMBOL);
      /* strip off the quotes */
      id = id.substr(1, id.size() - 2);
      if(!PARSER_STATE->isAbstractValue(id)) {
        // if an abstract value, SmtEngine handles declaration
        PARSER_STATE->checkDeclaration(id, check, type);
      }
    }
  | UNTERMINATED_QUOTED_SYMBOL
    ( EOF
      { PARSER_STATE->unexpectedEOF("unterminated |quoted| symbol"); }
    | '\\'
      { PARSER_STATE->unexpectedEOF("backslash not permitted in |quoted| "
                                    "symbol"); }
    )
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
datatypeDef[bool isCo, std::vector<CVC4::Datatype>& datatypes,
            std::vector< CVC4::Type >& params]
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
    { datatypes.push_back(Datatype(id,params,isCo));
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
  : symbol[id,CHECK_NONE,SYM_VARIABLE]
    { // make the tester
      std::string testerId("is-");
      testerId.append(id);
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
  : symbol[id,CHECK_NONE,SYM_SORT] sortSymbol[t,CHECK_NONE]
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
DEFINE_FUN_REC_TOK : 'define-fun-rec';
DEFINE_FUNS_REC_TOK : 'define-funs-rec';
DEFINE_SORT_TOK : 'define-sort';
GET_VALUE_TOK : 'get-value';
GET_ASSIGNMENT_TOK : 'get-assignment';
GET_ASSERTIONS_TOK : 'get-assertions';
GET_PROOF_TOK : 'get-proof';
GET_UNSAT_CORE_TOK : 'get-unsat-core';
EXIT_TOK : 'exit';
RESET_TOK : { PARSER_STATE->v2_5(false) }? 'reset';
RESET_ASSERTIONS_TOK : 'reset-assertions';
ITE_TOK : 'ite';
LET_TOK : { !PARSER_STATE->sygus() }? 'let';
SYGUS_LET_TOK : { PARSER_STATE->sygus() }? 'let';
ATTRIBUTE_TOK : '!';
LPAREN_TOK : '(';
RPAREN_TOK : ')';
INDEX_TOK : '_';
SET_LOGIC_TOK : 'set-logic';
SET_INFO_TOK : 'set-info';
META_INFO_TOK : 'meta-info';
GET_INFO_TOK : 'get-info';
SET_OPTION_TOK : 'set-option';
GET_OPTION_TOK : 'get-option';
PUSH_TOK : 'push';
POP_TOK : 'pop';
AS_TOK : 'as';
CONST_TOK : 'const';

// extended commands
DECLARE_CODATATYPE_TOK : { PARSER_STATE->v2_6() || PARSER_STATE->sygus() }? 'declare-codatatype';
DECLARE_DATATYPE_TOK : { PARSER_STATE->v2_6() || PARSER_STATE->sygus() }? 'declare-datatype';
DECLARE_DATATYPES_2_5_TOK : { !( PARSER_STATE->v2_6() || PARSER_STATE->sygus() ) }?'declare-datatypes';
DECLARE_DATATYPES_TOK : { PARSER_STATE->v2_6() || PARSER_STATE->sygus() }?'declare-datatypes';
DECLARE_CODATATYPES_2_5_TOK : { !( PARSER_STATE->v2_6() || PARSER_STATE->sygus() ) }?'declare-codatatypes';
DECLARE_CODATATYPES_TOK : { PARSER_STATE->v2_6() || PARSER_STATE->sygus() }?'declare-codatatypes';
PAR_TOK : { PARSER_STATE->v2_6() }?'par';
TESTER_TOK : { ( PARSER_STATE->v2_6() || PARSER_STATE->sygus() ) && PARSER_STATE->isTheoryEnabled(Smt2::THEORY_DATATYPES) }?'is';
MATCH_TOK : { ( PARSER_STATE->v2_6() || PARSER_STATE->sygus() ) && PARSER_STATE->isTheoryEnabled(Smt2::THEORY_DATATYPES) }?'match';
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
DEFINE_CONST_TOK : 'define-const';
SIMPLIFY_TOK : 'simplify';
INCLUDE_TOK : 'include';
GET_QE_TOK : 'get-qe';
GET_QE_DISJUNCT_TOK : 'get-qe-disjunct';

// SyGuS commands
SYNTH_FUN_TOK : 'synth-fun';
SYNTH_INV_TOK : 'synth-inv';
CHECK_SYNTH_TOK : 'check-synth';
DECLARE_VAR_TOK : 'declare-var';
DECLARE_PRIMED_VAR_TOK : 'declare-primed-var';
CONSTRAINT_TOK : 'constraint';
INV_CONSTRAINT_TOK : 'inv-constraint';
SET_OPTIONS_TOK : 'set-options';
SYGUS_ENUM_TOK : { PARSER_STATE->sygus() }? 'Enum';
SYGUS_ENUM_CONS_TOK : { PARSER_STATE->sygus() }? '::';
SYGUS_CONSTANT_TOK : { PARSER_STATE->sygus() }? 'Constant';
SYGUS_VARIABLE_TOK : { PARSER_STATE->sygus() }? 'Variable';
SYGUS_INPUT_VARIABLE_TOK : { PARSER_STATE->sygus() }? 'InputVariable';
SYGUS_LOCAL_VARIABLE_TOK : { PARSER_STATE->sygus() }? 'LocalVariable';

// attributes
ATTRIBUTE_PATTERN_TOK : ':pattern';
ATTRIBUTE_NO_PATTERN_TOK : ':no-pattern';
ATTRIBUTE_NAMED_TOK : ':named';
ATTRIBUTE_INST_LEVEL : ':quant-inst-max-level';
ATTRIBUTE_RR_PRIORITY : ':rr-priority';

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
LESS_THAN_TOK     : '<';
LESS_THAN_EQUAL_TOK     : '<=';
MINUS_TOK         : '-';
NOT_TOK           : 'not';
OR_TOK            : 'or';
// PERCENT_TOK       : '%';
PLUS_TOK          : '+';
//POUND_TOK         : '#';
STAR_TOK          : '*';
// TILDE_TOK         : '~';
XOR_TOK           : 'xor';


DIVISIBLE_TOK : 'divisible';

BV2NAT_TOK : 'bv2nat';
INT2BV_TOK : 'int2bv';

RENOSTR_TOK : 're.nostr';
REALLCHAR_TOK : 're.allchar';

DTSIZE_TOK : 'dt.size';

FMFCARD_TOK : 'fmf.card';
FMFCARDVAL_TOK : 'fmf.card.val';

INST_CLOSURE_TOK : 'inst-closure';

EMPTYSET_TOK: { PARSER_STATE->isTheoryEnabled(Smt2::THEORY_SETS) }? 'emptyset';
UNIVSET_TOK: { PARSER_STATE->isTheoryEnabled(Smt2::THEORY_SETS) }? 'univset';
NILREF_TOK: { PARSER_STATE->isTheoryEnabled(Smt2::THEORY_SEP) }? 'sep.nil';
TUPLE_CONST_TOK: { PARSER_STATE->isTheoryEnabled(Smt2::THEORY_DATATYPES) }? 'mkTuple';
TUPLE_SEL_TOK: { PARSER_STATE->isTheoryEnabled(Smt2::THEORY_DATATYPES) }? 'tupSel';
// Other set theory operators are not
// tokenized and handled directly when
// processing a term

REAL_PI_TOK : 'real.pi';

FP_PINF_TOK : '+oo';
FP_NINF_TOK : '-oo';
FP_PZERO_TOK : '+zero';
FP_NZERO_TOK : '-zero';
FP_NAN_TOK : { PARSER_STATE->isTheoryEnabled(Smt2::THEORY_FP) }? 'NaN';

FP_TO_FP_TOK : { PARSER_STATE->isTheoryEnabled(Smt2::THEORY_FP) }? 'to_fp';
FP_TO_FPBV_TOK : { PARSER_STATE->isTheoryEnabled(Smt2::THEORY_FP) }? 'to_fp_bv';
FP_TO_FPFP_TOK : { PARSER_STATE->isTheoryEnabled(Smt2::THEORY_FP) }? 'to_fp_fp';
FP_TO_FPR_TOK : { PARSER_STATE->isTheoryEnabled(Smt2::THEORY_FP) }? 'to_fp_real';
FP_TO_FPS_TOK : { PARSER_STATE->isTheoryEnabled(Smt2::THEORY_FP) }? 'to_fp_signed';
FP_TO_FPU_TOK : { PARSER_STATE->isTheoryEnabled(Smt2::THEORY_FP) }? 'to_fp_unsigned';
FP_TO_UBV_TOK : { PARSER_STATE->isTheoryEnabled(Smt2::THEORY_FP) }? 'fp.to_ubv';
FP_TO_SBV_TOK : { PARSER_STATE->isTheoryEnabled(Smt2::THEORY_FP) }? 'fp.to_sbv';
FP_RNE_TOK : { PARSER_STATE->isTheoryEnabled(Smt2::THEORY_FP) }? 'RNE';
FP_RNA_TOK : { PARSER_STATE->isTheoryEnabled(Smt2::THEORY_FP) }? 'RNA';
FP_RTP_TOK : { PARSER_STATE->isTheoryEnabled(Smt2::THEORY_FP) }? 'RTP';
FP_RTN_TOK : { PARSER_STATE->isTheoryEnabled(Smt2::THEORY_FP) }? 'RTN';
FP_RTZ_TOK : { PARSER_STATE->isTheoryEnabled(Smt2::THEORY_FP) }? 'RTZ';
FP_RNE_FULL_TOK : { PARSER_STATE->isTheoryEnabled(Smt2::THEORY_FP) }? 'roundNearestTiesToEven';
FP_RNA_FULL_TOK : { PARSER_STATE->isTheoryEnabled(Smt2::THEORY_FP) }? 'roundNearestTiesToAway';
FP_RTP_FULL_TOK : { PARSER_STATE->isTheoryEnabled(Smt2::THEORY_FP) }? 'roundTowardPositive';
FP_RTN_FULL_TOK : { PARSER_STATE->isTheoryEnabled(Smt2::THEORY_FP) }? 'roundTowardNegative';
FP_RTZ_FULL_TOK : { PARSER_STATE->isTheoryEnabled(Smt2::THEORY_FP) }? 'roundTowardZero';

HO_ARROW_TOK : { PARSER_STATE->getLogic().isHigherOrder() }? '->';
HO_LAMBDA_TOK : { PARSER_STATE->getLogic().isHigherOrder() }? 'lambda';

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
 * Matches a double-quoted string literal from SMT-LIB 2.0.
 * Escaping is supported, and * escape character '\' has to be escaped.
 *
 * You shouldn't generally use this in parser rules, as the quotes
 * will be part of the token text.  Use the str[] parser rule instead.
 */
STRING_LITERAL_2_0
  : { PARSER_STATE->v2_0() }?=>
    '"' ('\\' . | ~('\\' | '"'))* '"'
  ;

/**
 * Matches a double-quoted string literal from SMT-LIB 2.5.
 * You escape a double-quote inside the string with "", e.g.,
 * "This is a string literal with "" a single, embedded double quote."
 *
 * You shouldn't generally use this in parser rules, as the quotes
 * will be part of the token text.  Use the str[] parser rule instead.
 */
STRING_LITERAL_2_5
  : { PARSER_STATE->v2_5(false) || PARSER_STATE->sygus() }?=>
    '"' (~('"') | '""')* '"'
  ;

/**
 * Matches sygus quoted literal 
 */
SYGUS_QUOTED_LITERAL
 : { PARSER_STATE->sygus() }?=>
   '"' (ALPHA|DIGIT)* '"'
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
