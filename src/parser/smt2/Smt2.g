/* *******************                                                        */
/*! \file Smt2.g
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
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

#include <memory>

#include "parser/antlr_tracing.h"
#include "parser/parse_op.h"
#include "parser/parser.h"
#include "smt/command.h"

namespace CVC4 {
  class Expr;

  namespace api {
    class Term;
    class Sort;
  }

  namespace parser {
    namespace smt2 {
      /**
       * Just exists to provide the uintptr_t constructor that ANTLR
       * requires.
       */
      struct myExpr : public CVC4::api::Term {
        myExpr() : CVC4::api::Term() {}
        myExpr(void*) : CVC4::api::Term() {}
        myExpr(const Expr& e) : CVC4::api::Term(d_solver, e) {}
        myExpr(const myExpr& e) : CVC4::api::Term(e) {}
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

#include "api/cvc4cpp.h"
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
#undef SOLVER
#define SOLVER PARSER_STATE->getSolver()
#undef MK_TERM
#define MK_TERM SOLVER->mkTerm
#define UNSUPPORTED PARSER_STATE->unimplementedFeature

}/* parser::postinclude */

/**
 * Parses an expression.
 * @return the parsed expression, or the Null Expr if we've reached the
 * end of the input
 */
parseExpr returns [CVC4::parser::smt2::myExpr expr]
@declarations {
  CVC4::api::Term expr2;
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
  std::string name;
}
@after {
  cmd_return = cmd.release();
}
  : LPAREN_TOK cmd=sygusCommand RPAREN_TOK
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
  CVC4::api::Term expr, expr2;
  CVC4::api::Sort t;
  std::vector<CVC4::api::Term> terms;
  std::vector<api::Sort> sorts;
  std::vector<std::pair<std::string, CVC4::api::Sort> > sortedVarNames;
  std::vector<CVC4::api::Term> flattenVars;
}
  : /* set the logic */
    SET_LOGIC_TOK symbol[name,CHECK_NONE,SYM_SORT]
    {
      cmd->reset(PARSER_STATE->setLogic(name));
    }
  | /* set-info */
    SET_INFO_TOK setInfoInternal[cmd]
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
    DECLARE_SORT_TOK
    {
      PARSER_STATE->checkThatLogicIsSet();
      PARSER_STATE->checkLogicAllowsFreeSorts();
    }
    symbol[name,CHECK_UNDECLARED,SYM_SORT]
    { PARSER_STATE->checkUserSymbol(name); }
    n=INTEGER_LITERAL
    { Debug("parser") << "declare sort: '" << name
                      << "' arity=" << n << std::endl;
      unsigned arity = AntlrInput::tokenToUnsigned(n);
      if(arity == 0) {
        api::Sort type = PARSER_STATE->mkSort(name);
        cmd->reset(new DeclareTypeCommand(name, 0, type.getType()));
      } else {
        api::Sort type = PARSER_STATE->mkSortConstructor(name, arity);
        cmd->reset(new DeclareTypeCommand(name, arity, type.getType()));
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
      cmd->reset(new DefineTypeCommand(
          name, api::sortVectorToTypes(sorts), t.getType()));
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
      if(t.isFunction())
      {
        PARSER_STATE->checkLogicAllowsFunctions();
      }
      // we allow overloading for function declarations
      if( PARSER_STATE->sygus() )
      {
        PARSER_STATE->parseErrorLogic("declare-fun are not allowed in sygus "
                                      "version 2.0");
      }
      else
      {
        api::Term func =
            PARSER_STATE->bindVar(name, t, ExprManager::VAR_FLAG_NONE, true);
        cmd->reset(
            new DeclareFunctionCommand(name, func.getExpr(), t.getType()));
      }
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
        for(std::vector<std::pair<std::string, api::Sort> >::const_iterator i =
              sortedVarNames.begin(), iend = sortedVarNames.end();
            i != iend;
            ++i) {
          sorts.push_back((*i).second);
        }
        t = PARSER_STATE->mkFlatFunctionType(sorts, t, flattenVars);
      }
      PARSER_STATE->pushScope(true);
      terms = PARSER_STATE->bindBoundVars(sortedVarNames);
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
      api::Term func = PARSER_STATE->bindVar(name, t,
                                      ExprManager::VAR_FLAG_DEFINED, true);
      cmd->reset(
          new DefineFunctionCommand(name,
                                    func.getExpr(),
                                    api::termVectorToExprs(terms),
                                    expr.getExpr(),
                                    PARSER_STATE->getGlobalDeclarations()));
    }
  | DECLARE_DATATYPE_TOK datatypeDefCommand[false, cmd]
  | DECLARE_DATATYPES_TOK datatypesDefCommand[false, cmd]
  | /* value query */
    GET_VALUE_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    ( LPAREN_TOK termList[terms,expr] RPAREN_TOK
      { cmd->reset(new GetValueCommand(api::termVectorToExprs(terms))); }
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
    { PARSER_STATE->clearLastNamedTerm(); }
    term[expr, expr2]
    { bool inUnsatCore = PARSER_STATE->lastNamedTerm().first == expr;
      cmd->reset(new AssertCommand(expr.getExpr(), inUnsatCore));
      if(inUnsatCore) {
        // set the expression name, if there was a named term
        std::pair<api::Term, std::string> namedTerm =
            PARSER_STATE->lastNamedTerm();
        Command* csen = new SetExpressionNameCommand(namedTerm.first.getExpr(),
                                                     namedTerm.second);
        csen->setMuted(true);
        PARSER_STATE->preemptCommand(csen);
      }
    }
  | /* check-sat */
    CHECK_SAT_TOK { PARSER_STATE->checkThatLogicIsSet(); }
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
    | { expr = api::Term(); }
    )
    { cmd->reset(new CheckSatCommand(expr.getExpr())); }
  | /* check-sat-assuming */
    CHECK_SAT_ASSUMING_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    ( LPAREN_TOK termList[terms,expr] RPAREN_TOK
      {
        cmd->reset(new CheckSatAssumingCommand(api::termVectorToExprs(terms)));
      }
    | ~LPAREN_TOK
      { PARSER_STATE->parseError("The check-sat-assuming command expects a "
                                 "list of terms.  Perhaps you forgot a pair of "
                                 "parentheses?");
      }
    )
  | /* get-assertions */
    GET_ASSERTIONS_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    { cmd->reset(new GetAssertionsCommand()); }
  | /* get-proof */
    GET_PROOF_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    { cmd->reset(new GetProofCommand()); }
  | /* get-unsat-assumptions */
    GET_UNSAT_ASSUMPTIONS_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    { cmd->reset(new GetUnsatAssumptionsCommand); }
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
      { unsigned num = AntlrInput::tokenToUnsigned(k);
        if(num == 0) {
          cmd->reset(new EmptyCommand());
        } else if(num == 1) {
          PARSER_STATE->pushScope();
          cmd->reset(new PushCommand());
        } else {
          std::unique_ptr<CommandSequence> seq(new CommandSequence());
          do {
            PARSER_STATE->pushScope();
            Command* push_cmd = new PushCommand();
            push_cmd->setMuted(num > 1);
            seq->addCommand(push_cmd);
            --num;
            } while(num > 0);
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
      { unsigned num = AntlrInput::tokenToUnsigned(k);
        if(num > PARSER_STATE->scopeLevel()) {
          PARSER_STATE->parseError("Attempted to pop above the top stack "
                                   "frame.");
        }
        if(num == 0) {
          cmd->reset(new EmptyCommand());
        } else if(num == 1) {
          PARSER_STATE->popScope();
          cmd->reset(new PopCommand());
        } else {
          std::unique_ptr<CommandSequence> seq(new CommandSequence());
          do {
            PARSER_STATE->popScope();
            Command* pop_command = new PopCommand();
            pop_command->setMuted(num > 1);
            seq->addCommand(pop_command);
            --num;
          } while(num > 0);
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
            "In SMT-LIBv2 mode, but got something that looks like SMT-LIBv1, "
            "which is not supported anymore.");
      } else {
        PARSER_STATE->parseError("expected SMT-LIBv2 command, got `" + id +
                                 "'.");
      }
    }
  ;

sygusCommand returns [std::unique_ptr<CVC4::Command> cmd]
@declarations {
  CVC4::api::Term expr, expr2;
  CVC4::api::Sort t, range;
  std::vector<std::string> names;
  std::vector<std::pair<std::string, CVC4::api::Sort> > sortedVarNames;
  std::unique_ptr<Smt2::SynthFunFactory> synthFunFactory;
  std::string name, fun;
  bool isInv;
  CVC4::api::Sort grammar;
}
  : /* declare-var */
    DECLARE_VAR_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    symbol[name,CHECK_UNDECLARED,SYM_VARIABLE]
    { PARSER_STATE->checkUserSymbol(name); }
    sortSymbol[t,CHECK_DECLARED]
    {
      api::Term var = PARSER_STATE->bindBoundVar(name, t);
      cmd.reset(new DeclareSygusVarCommand(name, var.getExpr(), t.getType()));
    }

  | /* synth-fun */
    ( SYNTH_FUN_TOK { isInv = false; }
      | SYNTH_INV_TOK { isInv = true; range = SOLVER->getBooleanSort(); }
    )
    { PARSER_STATE->checkThatLogicIsSet(); }
    symbol[fun,CHECK_UNDECLARED,SYM_VARIABLE]
    LPAREN_TOK sortedVarList[sortedVarNames] RPAREN_TOK
    ( sortSymbol[range,CHECK_DECLARED] )?
    {
      synthFunFactory.reset(new Smt2::SynthFunFactory(
          PARSER_STATE, fun, isInv, range, sortedVarNames));
    }
    (
      // optionally, read the sygus grammar
      //
      // `grammar` specifies the required grammar for the function to
      // synthesize, expressed as a type
      sygusGrammar[grammar, synthFunFactory->getSygusVars(), fun]
    )?
    {
      cmd = synthFunFactory->mkCommand(grammar);
    }
  | /* constraint */
    CONSTRAINT_TOK {
      PARSER_STATE->checkThatLogicIsSet();
      Debug("parser-sygus") << "Sygus : define sygus funs..." << std::endl;
      Debug("parser-sygus") << "Sygus : read constraint..." << std::endl;
    }
    term[expr, expr2]
    { Debug("parser-sygus") << "...read constraint " << expr << std::endl;
      cmd.reset(new SygusConstraintCommand(expr.getExpr()));
    }
  | /* inv-constraint */
    INV_CONSTRAINT_TOK
    ( symbol[name,CHECK_NONE,SYM_VARIABLE] { names.push_back(name); } )+
    {
      cmd = PARSER_STATE->invConstraint(names);
    }
  | /* check-synth */
    CHECK_SYNTH_TOK
    { PARSER_STATE->checkThatLogicIsSet(); }
    {
      cmd.reset(new CheckSynthCommand());
    }
  | command[&cmd]
  ;


/** Reads a sygus grammar in the sygus version 2 format
 *
 * The resulting sygus datatype encoding the grammar is stored in ret.
 * The argument sygusVars indicates the sygus bound variable list, which is
 * the argument list of the function-to-synthesize (or null if the grammar
 * has bound variables).
 * The argument fun is a unique identifier to avoid naming clashes for the
 * datatypes constructed by this call.
 */
sygusGrammar[CVC4::api::Sort & ret,
             const std::vector<CVC4::api::Term>& sygusVars,
             const std::string& fun]
@declarations
{
  // the pre-declaration
  std::vector<std::pair<std::string, CVC4::api::Sort> > sortedVarNames;
  // non-terminal symbols of the grammar
  std::vector<CVC4::api::Term> ntSyms;
  CVC4::api::Sort t;
  std::string name;
  CVC4::api::Term e, e2;
  std::vector<api::DatatypeDecl> datatypes;
  std::set<api::Sort> unresTypes;
  std::map<CVC4::api::Term, CVC4::api::Sort> ntsToUnres;
  unsigned dtProcessed = 0;
  std::unordered_set<unsigned> allowConst;
}
  :
  // predeclaration
  LPAREN_TOK
  // We read a sorted variable list here in a custom way that throws an
  // error to recognize if the user is using the (deprecated) version 1.0
  // sygus syntax.
  ( LPAREN_TOK symbol[name,CHECK_NONE,SYM_VARIABLE]
    sortSymbol[t,CHECK_DECLARED] (
      // SyGuS version 1.0 expects a grammar ((Start Int ( ...
      // SyGuS version 2.0 expects a predeclaration ((Start Int) ...
      LPAREN_TOK
      {
        std::stringstream sse;
        if (sortedVarNames.empty())
        {
          sse << "The expected SyGuS language is version 2.0, whereas the "
              << "input appears to be SyGuS version 1.0 format. The version "
              << "2.0 format requires a predeclaration of the non-terminal "
              << "symbols of the grammar to be given prior to the definition "
              << "of the grammar. See https://sygus.org/language/ for details "
              << "and examples. CVC4 versions past 1.8 do not support SyGuS "
              << "version 1.0.";
        }
        else
        {
          // an unknown syntax error
          sse << "Unexpected syntax for SyGuS predeclaration.";
        }
        PARSER_STATE->parseError(sse.str().c_str());
      }
    | RPAREN_TOK )
    { sortedVarNames.push_back(make_pair(name, t)); }
  )*
  RPAREN_TOK
  {
    // non-terminal symbols in the pre-declaration are locally scoped
    PARSER_STATE->pushScope(true);
    for (std::pair<std::string, api::Sort>& i : sortedVarNames)
    {
      Trace("parser-sygus2") << "Declare datatype " << i.first << std::endl;
      // make the datatype, which encodes terms generated by this non-terminal
      std::string dname = i.first;
      datatypes.push_back(SOLVER->mkDatatypeDecl(dname));
      // make its unresolved type, used for referencing the final version of
      // the datatype
      PARSER_STATE->checkDeclaration(dname, CHECK_UNDECLARED, SYM_SORT);
      api::Sort urt = PARSER_STATE->mkUnresolvedType(dname);
      unresTypes.insert(urt);
      // make the non-terminal symbol, which will be parsed as an ordinary
      // free variable.
      api::Term nts = PARSER_STATE->bindBoundVar(i.first, i.second);
      ntSyms.push_back(nts);
      ntsToUnres[nts] = urt;
    }
  }
  // the grouped rule listing
  LPAREN_TOK
  (
    LPAREN_TOK
    symbol[name, CHECK_DECLARED, SYM_VARIABLE] sortSymbol[t, CHECK_DECLARED]
    {
      // check that it matches sortedVarNames
      if (sortedVarNames[dtProcessed].first != name)
      {
        std::stringstream sse;
        sse << "Grouped rule listing " << name
            << " does not match the name (in order) from the predeclaration ("
            << sortedVarNames[dtProcessed].first << ")." << std::endl;
        PARSER_STATE->parseError(sse.str().c_str());
      }
      if (sortedVarNames[dtProcessed].second != t)
      {
        std::stringstream sse;
        sse << "Type for grouped rule listing " << name
            << " does not match the type (in order) from the predeclaration ("
            << sortedVarNames[dtProcessed].second << ")." << std::endl;
        PARSER_STATE->parseError(sse.str().c_str());
      }
    }
    LPAREN_TOK
    (
      term[e,e2] {
        // add term as constructor to datatype
        PARSER_STATE->addSygusConstructorTerm(
            datatypes[dtProcessed], e, ntsToUnres);
      }
      | LPAREN_TOK SYGUS_CONSTANT_TOK sortSymbol[t, CHECK_DECLARED] RPAREN_TOK {
        // allow constants in datatypes[dtProcessed]
        allowConst.insert(dtProcessed);
      }
      | LPAREN_TOK SYGUS_VARIABLE_TOK sortSymbol[t, CHECK_DECLARED] RPAREN_TOK {
        // add variable constructors to datatype
        PARSER_STATE->addSygusConstructorVariables(
            datatypes[dtProcessed], sygusVars, t);
      }
    )+
    RPAREN_TOK
    RPAREN_TOK
    {
      dtProcessed++;
    }
  )+
  RPAREN_TOK
  {
    if (dtProcessed != sortedVarNames.size())
    {
      PARSER_STATE->parseError(
          "Number of grouped rule listings does not match "
          "number of symbols in predeclaration.");
    }
    api::Term bvl;
    if (!sygusVars.empty())
    {
      bvl = MK_TERM(api::BOUND_VAR_LIST, sygusVars);
    }
    Trace("parser-sygus2") << "Process " << dtProcessed << " sygus datatypes..." << std::endl;
    for (unsigned i = 0; i < dtProcessed; i++)
    {
      bool aci = allowConst.find(i)!=allowConst.end();
      api::Sort btt = sortedVarNames[i].second;
      datatypes[i].getDatatype().setSygus(btt.getType(), bvl.getExpr(), aci, false);
      Trace("parser-sygus2") << "- " << datatypes[i].getName()
                             << ", #cons= " << datatypes[i].getNumConstructors()
                             << ", aci= " << aci << std::endl;
      // We can be in a case where the only rule specified was (Variable T)
      // and there are no variables of type T, in which case this is a bogus
      // grammar. This results in the error below.
      if (datatypes[i].getNumConstructors() == 0)
      {
        std::stringstream se;
        se << "Grouped rule listing for " << datatypes[i].getName()
           << " produced an empty rule list.";
        PARSER_STATE->parseError(se.str());
      }
    }
    // pop scope from the pre-declaration
    PARSER_STATE->popScope();
    // now, make the sygus datatype
    Trace("parser-sygus2") << "Make the sygus datatypes..." << std::endl;
    std::vector<api::Sort> datatypeTypes =
      SOLVER->mkDatatypeSorts(datatypes, unresTypes);
    // return is the first datatype
    ret = api::Sort(datatypeTypes[0]);
  }
;

setInfoInternal[std::unique_ptr<CVC4::Command>* cmd]
@declarations {
  std::string name;
  SExpr sexpr;
}
  : KEYWORD symbolicExpr[sexpr]
    { name = AntlrInput::tokenText($KEYWORD);
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
  CVC4::api::Term expr, expr2;
  std::vector<std::pair<std::string, CVC4::api::Sort> > sortedVarNames;
  SExpr sexpr;
  CVC4::api::Sort t;
  CVC4::api::Term func;
  std::vector<CVC4::api::Term> bvs;
  std::vector<std::vector<std::pair<std::string, CVC4::api::Sort>>>
      sortedVarNamesList;
  std::vector<std::vector<CVC4::api::Term>> flattenVarsList;
  std::vector<std::vector<CVC4::api::Term>> formals;
  std::vector<CVC4::api::Term> funcs;
  std::vector<CVC4::api::Term> func_defs;
  CVC4::api::Term aexpr;
  std::unique_ptr<CVC4::CommandSequence> seq;
  std::vector<api::Sort> sorts;
  std::vector<CVC4::api::Term> flattenVars;
}
    /* declare-const */
  : DECLARE_CONST_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    symbol[name,CHECK_NONE,SYM_VARIABLE]
    { PARSER_STATE->checkUserSymbol(name); }
    sortSymbol[t,CHECK_DECLARED]
    { // allow overloading here
      api::Term c =
          PARSER_STATE->bindVar(name, t, ExprManager::VAR_FLAG_NONE, true);
      cmd->reset(new DeclareFunctionCommand(name, c.getExpr(), t.getType())); }

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
      func =
          PARSER_STATE->bindDefineFunRec(fname, sortedVarNames, t, flattenVars);
      PARSER_STATE->pushDefineFunRecScope(
          sortedVarNames, func, flattenVars, bvs, true);
    }
    term[expr, expr2]
    { PARSER_STATE->popScope();
      if( !flattenVars.empty() ){
        expr = PARSER_STATE->mkHoApply( expr, flattenVars );
      }
      cmd->reset(new DefineFunctionRecCommand(
          SOLVER, func, bvs, expr, PARSER_STATE->getGlobalDeclarations()));
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
        func = PARSER_STATE->bindDefineFunRec(
            fname, sortedVarNames, t, flattenVars);
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
      cmd->reset(
          new DefineFunctionRecCommand(SOLVER,
                                       funcs,
                                       formals,
                                       func_defs,
                                       PARSER_STATE->getGlobalDeclarations()));
    }
  ;

extendedCommand[std::unique_ptr<CVC4::Command>* cmd]
@declarations {
  std::vector<api::DatatypeDecl> dts;
  CVC4::api::Term e, e2;
  CVC4::api::Sort t;
  std::string name;
  std::vector<std::string> names;
  std::vector<CVC4::api::Term> terms;
  std::vector<api::Sort> sorts;
  std::vector<std::pair<std::string, CVC4::api::Sort> > sortedVarNames;
  std::unique_ptr<CVC4::CommandSequence> seq;
}
    /* Extended SMT-LIB set of commands syntax, not permitted in
     * --smtlib2 compliance mode. */
  : DECLARE_DATATYPES_2_5_TOK datatypes_2_5_DefCommand[false, cmd]
  | DECLARE_CODATATYPES_2_5_TOK datatypes_2_5_DefCommand[true, cmd]
  | DECLARE_CODATATYPE_TOK datatypeDefCommand[true, cmd]
  | DECLARE_CODATATYPES_TOK datatypesDefCommand[true, cmd]

    /* Support some of Z3's extended SMT-LIB commands */

  | DECLARE_SORTS_TOK
    {
      PARSER_STATE->checkThatLogicIsSet();
      PARSER_STATE->checkLogicAllowsFreeSorts();
      seq.reset(new CVC4::CommandSequence());
    }
    LPAREN_TOK
    ( symbol[name,CHECK_UNDECLARED,SYM_SORT]
      { PARSER_STATE->checkUserSymbol(name);
        api::Sort type = PARSER_STATE->mkSort(name);
        seq->addCommand(new DeclareTypeCommand(name, 0, type.getType()));
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
      { api::Sort tt;
        if(sorts.size() > 1) {
          PARSER_STATE->checkLogicAllowsFunctions();
          // must flatten
          api::Sort range = sorts.back();
          sorts.pop_back();
          tt = PARSER_STATE->mkFlatFunctionType(sorts, range);
        } else {
          tt = sorts[0];
        }
        // allow overloading
        api::Term func =
            PARSER_STATE->bindVar(name, tt, ExprManager::VAR_FLAG_NONE, true);
        seq->addCommand(
            new DeclareFunctionCommand(name, func.getExpr(), tt.getType()));
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
      { t = SOLVER->getBooleanSort();
        if(sorts.size() > 0) {
          PARSER_STATE->checkLogicAllowsFunctions();
          t = SOLVER->mkFunctionSort(sorts, t);
        }
        // allow overloading
        api::Term func =
            PARSER_STATE->bindVar(name, t, ExprManager::VAR_FLAG_NONE, true);
        seq->addCommand(
            new DeclareFunctionCommand(name, func.getExpr(), t.getType()));
        sorts.clear();
      }
    )+
    RPAREN_TOK
    { cmd->reset(seq.release()); }

  | DEFINE_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    ( // (define f t)
      symbol[name,CHECK_UNDECLARED,SYM_VARIABLE]
      { PARSER_STATE->checkUserSymbol(name); }
      term[e,e2]
      {
        api::Term func = PARSER_STATE->bindVar(name, e.getSort(),
                                        ExprManager::VAR_FLAG_DEFINED);
        cmd->reset(
            new DefineFunctionCommand(name,
                                      func.getExpr(),
                                      e.getExpr(),
                                      PARSER_STATE->getGlobalDeclarations()));
      }
    | // (define (f (v U) ...) t)
      LPAREN_TOK
      symbol[name,CHECK_UNDECLARED,SYM_VARIABLE]
      { PARSER_STATE->checkUserSymbol(name); }
      sortedVarList[sortedVarNames] RPAREN_TOK
      { /* add variables to parser state before parsing term */
        Debug("parser") << "define fun: '" << name << "'" << std::endl;
        PARSER_STATE->pushScope(true);
        terms = PARSER_STATE->bindBoundVars(sortedVarNames);
      }
      term[e,e2]
      {
        PARSER_STATE->popScope();
        // declare the name down here (while parsing term, signature
        // must not be extended with the name itself; no recursion
        // permitted)
        api::Sort tt = e.getSort();
        if( sortedVarNames.size() > 0 ) {
          sorts.reserve(sortedVarNames.size());
          for(std::vector<std::pair<std::string, api::Sort> >::const_iterator
                i = sortedVarNames.begin(), iend = sortedVarNames.end();
              i != iend; ++i) {
            sorts.push_back((*i).second);
          }
          tt = SOLVER->mkFunctionSort(sorts, tt);
        }
        api::Term func = PARSER_STATE->bindVar(name, tt,
                                        ExprManager::VAR_FLAG_DEFINED);
        cmd->reset(
            new DefineFunctionCommand(name,
                                      func.getExpr(),
                                      api::termVectorToExprs(terms),
                                      e.getExpr(),
                                      PARSER_STATE->getGlobalDeclarations()));
      }
    )
  | // (define-const x U t)
    DEFINE_CONST_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    symbol[name,CHECK_UNDECLARED,SYM_VARIABLE]
    { PARSER_STATE->checkUserSymbol(name); }
    sortSymbol[t,CHECK_DECLARED]
    { /* add variables to parser state before parsing term */
      Debug("parser") << "define const: '" << name << "'" << std::endl;
      PARSER_STATE->pushScope(true);
      terms = PARSER_STATE->bindBoundVars(sortedVarNames);
    }
    term[e, e2]
    {
      PARSER_STATE->popScope();
      // declare the name down here (while parsing term, signature
      // must not be extended with the name itself; no recursion
      // permitted)
      api::Term func = PARSER_STATE->bindVar(name, t,
                                      ExprManager::VAR_FLAG_DEFINED);
      cmd->reset(
          new DefineFunctionCommand(name,
                                    func.getExpr(),
                                    api::termVectorToExprs(terms),
                                    e.getExpr(),
                                    PARSER_STATE->getGlobalDeclarations()));
    }

  | SIMPLIFY_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    term[e,e2]
    { cmd->reset(new SimplifyCommand(e.getExpr())); }
  | GET_QE_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    term[e,e2]
    { cmd->reset(new GetQuantifierEliminationCommand(e.getExpr(), true)); }
  | GET_QE_DISJUNCT_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    term[e,e2]
    { cmd->reset(new GetQuantifierEliminationCommand(e.getExpr(), false)); }
  | GET_ABDUCT_TOK {
      PARSER_STATE->checkThatLogicIsSet();
    }
    symbol[name,CHECK_UNDECLARED,SYM_VARIABLE]
    term[e,e2]
    (
      sygusGrammar[t, terms, name]
    )?
    {
      cmd->reset(new GetAbductCommand(name,e.getExpr(), t.getType()));
    }
  | GET_INTERPOL_TOK {
      PARSER_STATE->checkThatLogicIsSet();
    }
    symbol[name,CHECK_UNDECLARED,SYM_VARIABLE]
    term[e,e2]
    (
      sygusGrammar[t, terms, name]
    )?
    {
      cmd->reset(new GetInterpolCommand(SOLVER, name, e, t.getType()));
    }
  | DECLARE_HEAP LPAREN_TOK
    sortSymbol[t, CHECK_DECLARED]
    sortSymbol[t, CHECK_DECLARED]
    // We currently do nothing with the type information declared for the heap.
    { cmd->reset(new EmptyCommand()); }
    RPAREN_TOK
  | BLOCK_MODEL_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    { cmd->reset(new BlockModelCommand()); }

  | BLOCK_MODEL_VALUES_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    ( LPAREN_TOK termList[terms,e] RPAREN_TOK
      { cmd->reset(new BlockModelValuesCommand(api::termVectorToExprs(terms))); }
    | ~LPAREN_TOK
      { PARSER_STATE->parseError("The block-model-value command expects a list "
                                 "of terms.  Perhaps you forgot a pair of "
                                 "parentheses?");
      }
    )
  ;


datatypes_2_5_DefCommand[bool isCo, std::unique_ptr<CVC4::Command>* cmd]
@declarations {
  std::vector<api::DatatypeDecl> dts;
  std::string name;
  std::vector<api::Sort> sorts;
  std::vector<std::string> dnames;
  std::vector<unsigned> arities;
}
  : { PARSER_STATE->checkThatLogicIsSet();
    /* open a scope to keep the UnresolvedTypes contained */
    PARSER_STATE->pushScope(true); }
  LPAREN_TOK /* parametric sorts */
  ( symbol[name,CHECK_UNDECLARED,SYM_SORT]
    {
      sorts.push_back(PARSER_STATE->mkSort(name, ExprManager::SORT_FLAG_PLACEHOLDER));
    }
  )*
  RPAREN_TOK
  LPAREN_TOK ( LPAREN_TOK datatypeDef[isCo, dts, sorts] RPAREN_TOK )+ RPAREN_TOK
  { PARSER_STATE->popScope();
    cmd->reset(new DatatypeDeclarationCommand(
      api::sortVectorToTypes(
        PARSER_STATE->bindMutualDatatypeTypes(dts, true))));
  }
  ;

datatypeDefCommand[bool isCo, std::unique_ptr<CVC4::Command>* cmd]
@declarations {
  std::vector<api::DatatypeDecl> dts;
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
  std::vector<api::DatatypeDecl> dts;
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
 * arity for the corresponding datatype has not been fixed: notice that we do
 * not know the arity of datatypes in the declare-datatype command prior to
 * parsing their body, whereas the arity of datatypes in declare-datatypes is
 * given in the preamble of that command and thus is known prior to this call.
 */
datatypesDef[bool isCo,
             const std::vector<std::string>& dnames,
             const std::vector<int>& arities,
             std::unique_ptr<CVC4::Command>* cmd]
@declarations {
  std::vector<api::DatatypeDecl> dts;
  std::string name;
  std::vector<api::Sort> params;
}
  : { PARSER_STATE->pushScope(true);
      // Declare the datatypes that are currently being defined as unresolved
      // types. If we do not know the arity of the datatype yet, we wait to
      // define it until parsing the preamble of its body, which may optionally
      // involve `par`. This is limited to the case of single datatypes defined
      // via declare-datatype, and hence no datatype body is parsed without
      // having all types declared. This ensures we can parse datatypes with
      // nested recursion, e.g. datatypes D having a subfield type
      // (Array Int D).
      for (unsigned i=0, dsize=dnames.size(); i<dsize; i++)
      {
        if( arities[i]<0 )
        {
          // do not know the arity yet
          continue;
        }
        unsigned arity = static_cast<unsigned>(arities[i]);
        PARSER_STATE->mkUnresolvedType(dnames[i], arity);
      }
    }
    ( LPAREN_TOK {
      params.clear();
      Debug("parser-dt") << "Processing datatype #" << dts.size() << std::endl;
      if( dts.size()>=dnames.size() ){
        PARSER_STATE->parseError("Too many datatypes defined in this block.");
      }
    }
    ( PAR_TOK { PARSER_STATE->pushScope(true); } LPAREN_TOK
      ( symbol[name,CHECK_UNDECLARED,SYM_SORT]
        {
          params.push_back( PARSER_STATE->mkSort(name, ExprManager::SORT_FLAG_PLACEHOLDER)); }
      )*
      RPAREN_TOK {
        // if the arity was fixed by prelude and is not equal to the number of parameters
        if( arities[dts.size()]>=0 && static_cast<int>(params.size())!=arities[dts.size()] ){
          PARSER_STATE->parseError("Wrong number of parameters for datatype.");
        }
        if (arities[dts.size()]<0)
        {
          // now declare it as an unresolved type
          PARSER_STATE->mkUnresolvedType(dnames[dts.size()], params.size());
        }
        Debug("parser-dt") << params.size() << " parameters for " << dnames[dts.size()] << std::endl;
        dts.push_back(SOLVER->mkDatatypeDecl(dnames[dts.size()], params, isCo));
      }
      LPAREN_TOK
      ( LPAREN_TOK constructorDef[dts.back()] RPAREN_TOK )+
      RPAREN_TOK { PARSER_STATE->popScope(); }
    | { // if the arity was fixed by prelude and is not equal to 0
        if( arities[dts.size()]>0 ){
          PARSER_STATE->parseError("No parameters given for datatype.");
        }
        else if (arities[dts.size()]<0)
        {
          // now declare it as an unresolved type
          PARSER_STATE->mkUnresolvedType(dnames[dts.size()], 0);
        }
        Debug("parser-dt") << params.size() << " parameters for " << dnames[dts.size()] << std::endl;
        dts.push_back(SOLVER->mkDatatypeDecl(dnames[dts.size()],
                                             params,
                                             isCo));
      }
      ( LPAREN_TOK constructorDef[dts.back()] RPAREN_TOK )+
    )
    RPAREN_TOK
    )+
  {
    PARSER_STATE->popScope();
    cmd->reset(new DatatypeDeclarationCommand(
      api::sortVectorToTypes(
        PARSER_STATE->bindMutualDatatypeTypes(dts, true))));
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
  | symbol[s,CHECK_NONE,SYM_SORT]
    { sexpr = SExpr(SExpr::Keyword(s)); }
  | tok=(ASSERT_TOK | CHECK_SAT_TOK | CHECK_SAT_ASSUMING_TOK | DECLARE_FUN_TOK
        | DECLARE_SORT_TOK
        | DEFINE_FUN_TOK | DEFINE_FUN_REC_TOK | DEFINE_FUNS_REC_TOK
        | DEFINE_SORT_TOK | GET_VALUE_TOK | GET_ASSIGNMENT_TOK
        | GET_ASSERTIONS_TOK | GET_PROOF_TOK | GET_UNSAT_ASSUMPTIONS_TOK
        | GET_UNSAT_CORE_TOK | EXIT_TOK
        | RESET_TOK | RESET_ASSERTIONS_TOK | SET_LOGIC_TOK | SET_INFO_TOK
        | GET_INFO_TOK | SET_OPTION_TOK | GET_OPTION_TOK | PUSH_TOK | POP_TOK
        | DECLARE_DATATYPES_TOK | GET_MODEL_TOK | ECHO_TOK | SIMPLIFY_TOK)
    { sexpr = SExpr(SExpr::Keyword(AntlrInput::tokenText($tok))); }
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
 * @return the expression representing the term.
 */
term[CVC4::api::Term& expr, CVC4::api::Term& expr2]
@init {
  api::Kind kind = api::NULL_EXPR;
  CVC4::api::Term f;
  std::string name;
  CVC4::api::Sort type;
  ParseOp p;
}
: termNonVariable[expr, expr2]

  // a qualified identifier (section 3.6 of SMT-LIB version 2.6)

  | qualIdentifier[p]
    {
      expr = PARSER_STATE->parseOpToExpr(p);
    }
  ;

/**
 * Matches a non-variable term.
 * @return the expression expr representing the term or formula, and expr2, an
 * optional annotation for expr (for instance, for attributed expressions).
 */
termNonVariable[CVC4::api::Term& expr, CVC4::api::Term& expr2]
@init {
  Debug("parser") << "term: " << AntlrInput::tokenText(LT(1)) << std::endl;
  api::Kind kind = api::NULL_EXPR;
  std::string name;
  std::vector<CVC4::api::Term> args;
  std::vector< std::pair<std::string, CVC4::api::Sort> > sortedVarNames;
  CVC4::api::Term bvl;
  CVC4::api::Term f, f2, f3;
  std::string attr;
  CVC4::api::Term attexpr;
  std::vector<CVC4::api::Term> patexprs;
  std::vector<CVC4::api::Term> matchcases;
  std::unordered_set<std::string> names;
  std::vector< std::pair<std::string, CVC4::api::Term> > binders;
  CVC4::api::Sort type;
  CVC4::api::Sort type2;
  api::Term atomTerm;
  ParseOp p;
  std::vector<api::Sort> argTypes;
}
  : LPAREN_TOK quantOp[kind]
    {
      if (!PARSER_STATE->isTheoryEnabled(theory::THEORY_QUANTIFIERS))
      {
        PARSER_STATE->parseError("Quantifier used in non-quantified logic.");
      }
      PARSER_STATE->pushScope(true);
    }
    boundVarList[bvl]
    term[f, f2] RPAREN_TOK
    {
      args.push_back(bvl);

      PARSER_STATE->popScope();
      args.push_back(f);
      if(! f2.isNull()){
        args.push_back(f2);
      }
      expr = MK_TERM(kind, args);
    }
  | LPAREN_TOK COMPREHENSION_TOK
    { PARSER_STATE->pushScope(true); }
    boundVarList[bvl]
    {
      args.push_back(bvl);
    }
    term[f, f2] { args.push_back(f); }
    term[f, f2] {
      args.push_back(f);
      expr = MK_TERM(api::COMPREHENSION, args);
    }
    RPAREN_TOK
  | LPAREN_TOK qualIdentifier[p]
    termList[args,expr] RPAREN_TOK
    {
      expr = PARSER_STATE->applyParseOp(p, args);
    }
  | /* a let or sygus let binding */
    LPAREN_TOK 
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
          binders.push_back(std::make_pair(name, expr)); } )+
    { // now implement these bindings
      for (const std::pair<std::string, api::Term>& binder : binders)
      {
        {
          PARSER_STATE->defineVar(binder.first, binder.second);
        }
      }
    }
    RPAREN_TOK
    term[expr, f2]
    RPAREN_TOK
    { PARSER_STATE->popScope(); }
  | /* match expression */
    LPAREN_TOK MATCH_TOK term[expr, f2] {
      if( !expr.getSort().isDatatype() ){
        PARSER_STATE->parseError("Cannot match on non-datatype term.");
      }
    }
    LPAREN_TOK
    (
      // case with non-nullary pattern
      LPAREN_TOK LPAREN_TOK term[f, f2] {
          args.clear();
          PARSER_STATE->pushScope(true);
          // f should be a constructor
          type = f.getSort();
          Debug("parser-dt") << "Pattern head : " << f << " " << type << std::endl;
          if (!type.isConstructor())
          {
            PARSER_STATE->parseError("Pattern must be application of a constructor or a variable.");
          }
          Expr ef = f.getExpr();
          if (Datatype::datatypeOf(ef).isParametric())
          {
            type = api::Sort(
                SOLVER,
                Datatype::datatypeOf(ef)[Datatype::indexOf(ef)]
                    .getSpecializedConstructorType(expr.getSort().getType()));
          }
          argTypes = type.getConstructorDomainSorts();
        }
        // arguments of the pattern
        ( symbol[name,CHECK_NONE,SYM_VARIABLE] {
            if (args.size() >= argTypes.size())
            {
              PARSER_STATE->parseError("Too many arguments for pattern.");
            }
            //make of proper type
            api::Term arg = PARSER_STATE->bindBoundVar(name, argTypes[args.size()]);
            args.push_back( arg );
          }
        )*
        RPAREN_TOK term[f3, f2] {
          // make the match case
          std::vector<CVC4::api::Term> cargs;
          cargs.push_back(f);
          cargs.insert(cargs.end(),args.begin(),args.end());
          api::Term c = MK_TERM(api::APPLY_CONSTRUCTOR,cargs);
          api::Term bvla = MK_TERM(api::BOUND_VAR_LIST,args);
          api::Term mc = MK_TERM(api::MATCH_BIND_CASE, bvla, c, f3);
          matchcases.push_back(mc);
          // now, pop the scope
          PARSER_STATE->popScope();
        }
        RPAREN_TOK
      // case with nullary or variable pattern
      | LPAREN_TOK symbol[name,CHECK_NONE,SYM_VARIABLE] {
          if (PARSER_STATE->isDeclared(name,SYM_VARIABLE))
          {
            f = PARSER_STATE->getVariable(name);
            type = f.getSort();
            if (!type.isConstructor() ||
                !type.getConstructorDomainSorts().empty())
            {
              PARSER_STATE->parseError("Must apply constructors of arity greater than 0 to arguments in pattern.");
            }
            // make nullary constructor application
            f = MK_TERM(api::APPLY_CONSTRUCTOR, f);
          }
          else
          {
            // it has the type of the head expr
            f = PARSER_STATE->bindBoundVar(name, expr.getSort());
          }
        }
        term[f3, f2] {
          api::Term mc;
          if (f.getKind() == api::VARIABLE)
          {
            api::Term bvlf = MK_TERM(api::BOUND_VAR_LIST, f);
            mc = MK_TERM(api::MATCH_BIND_CASE, bvlf, f, f3);
          }
          else
          {
            mc = MK_TERM(api::MATCH_CASE, f, f3);
          }
          matchcases.push_back(mc);
        }
        RPAREN_TOK
    )+
    RPAREN_TOK RPAREN_TOK  {
      //now, make the match
      if (matchcases.empty())
      {
        PARSER_STATE->parseError("Must have at least one case in match.");
      }
      std::vector<api::Term> mchildren;
      mchildren.push_back(expr);
      mchildren.insert(mchildren.end(), matchcases.begin(), matchcases.end());
      expr = MK_TERM(api::MATCH, mchildren);
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
      if(! patexprs.empty()) {
        if( !f2.isNull() && f2.getKind()==api::INST_PATTERN_LIST ){
          for( size_t i=0; i<f2.getNumChildren(); i++ ){
            if( f2[i].getKind()==api::INST_PATTERN ){
              patexprs.push_back( f2[i] );
            }else{
              std::stringstream ss;
              ss << "warning: rewrite rules do not support " << f2[i]
                 << " within instantiation pattern list";
              PARSER_STATE->warning(ss.str());
            }
          }
        }
        expr2 = MK_TERM(api::INST_PATTERN_LIST, patexprs);
      } else {
        expr2 = f2;
      }
    }
  | /* lambda */
    LPAREN_TOK HO_LAMBDA_TOK
    { PARSER_STATE->pushScope(true); }
    boundVarList[bvl]
    term[f, f2] RPAREN_TOK
    {
      args.push_back(bvl);
      args.push_back(f);
      PARSER_STATE->popScope();
      expr = MK_TERM(api::LAMBDA, args);
    }
  | LPAREN_TOK TUPLE_CONST_TOK termList[args,expr] RPAREN_TOK
  {
    std::vector<api::Sort> sorts;
    std::vector<api::Term> terms;
    for (const api::Term& arg : args)
    {
      sorts.emplace_back(arg.getSort());
      terms.emplace_back(arg);
    }
    expr = SOLVER->mkTuple(sorts, terms);
  }
  | /* an atomic term (a term with no subterms) */
    termAtomic[atomTerm] { expr = atomTerm; }
  ;


/**
 * Matches a qualified identifier, which can be a combination of one or more of
 * the following, stored in the ParseOp utility class:
 * (1) A kind.
 * (2) A string name.
 * (3) An expression expr.
 * (4) A type t.
 *
 * A qualified identifier is the generic case of function heads.
 * With respect to the standard definition (Section 3.6 of SMT-LIB version 2.6)
 * of qualified identifiers, we additionally parse:
 * - "Array constant specifications" of the form (as const (Array T1 T2)),
 * which notice are used as function heads e.g. ((as const (Array Int Int)) 0)
 * specifies the constant array over integers consisting of constant 0. This
 * is handled as if it were a special case of an operator here.
 *
 * Examples:
 *
 * (Identifiers)
 *
 * - For declared functions f, we return (2).
 * - For indexed functions like testers (_ is C) and bitvector extract
 * (_ extract n m), we return (3) for the appropriate operator.
 * - For tuple selectors (_ tupSel n), we return (1) and (3). api::Kind is set to
 * APPLY_SELECTOR, and expr is set to n, which is to be interpreted by the
 * caller as the n^th generic tuple selector. We do this since there is no
 * AST expression representing generic tuple select, and we do not have enough
 * type information at this point to know the type of the tuple we will be
 * selecting from.
 *
 * (Ascripted Identifiers)
 *
 * - For ascripted nullary parametric datatype constructors like
 * (as nil (List Int)), we return (APPLY_CONSTRUCTOR C) for the appropriate
 * specialized constructor C as (3).
 * - For ascripted non-nullary parametric datatype constructors like
 * (as cons (List Int)), we return the appropriate specialized constructor C
 * as (3).
 * - Overloaded non-parametric constructors (as C T) return the appropriate
 * expression, analogous to the parametric cases above.
 * - For other ascripted nullary constants like (as emptyset (Set T)),
 * (as sep.nil T), we return the appropriate expression (3).
 * - For array constant specifications (as const (Array T1 T2)), we return (1)
 * and (4), where kind is set to STORE_ALL and type is set to (Array T1 T2),
 * where this is to be interpreted by the caller as converting the next parsed
 * constant of type T2 to an Array of type (Array T1 T2) over that constant.
 * - For ascriptions on normal symbols (as f T), we return the appropriate
 * expression (3), which may involve disambiguating f based on type T if it is
 * overloaded.
 */
qualIdentifier[CVC4::ParseOp& p]
@init {
  api::Kind k;
  std::string baseName;
  CVC4::api::Term f;
  CVC4::api::Sort type;
}
: identifier[p]
  | LPAREN_TOK AS_TOK
    ( CONST_TOK sortSymbol[type, CHECK_DECLARED]
      {
        p.d_kind = api::CONST_ARRAY;
        PARSER_STATE->parseOpApplyTypeAscription(p, type);
      }
    | identifier[p]
      sortSymbol[type, CHECK_DECLARED]
      {
        PARSER_STATE->parseOpApplyTypeAscription(p, type);
      }
    )
    RPAREN_TOK
  ;

/**
 * Matches an identifier, which can be a combination of one or more of the
 * following, stored in the ParseOp utility class:
 * (1) A kind.
 * (2) A string name.
 * (3) An expression expr.
 * For examples, see documentation of qualIdentifier.
 */
identifier[CVC4::ParseOp& p]
@init {
  CVC4::api::Term f;
  CVC4::api::Term f2;
  std::vector<uint64_t> numerals;
}
: functionName[p.d_name, CHECK_NONE]

  // indexed functions

  | LPAREN_TOK INDEX_TOK
    ( TESTER_TOK term[f, f2]
      {
        if (f.getKind() == api::APPLY_CONSTRUCTOR && f.getNumChildren() == 1)
        {
          // for nullary constructors, must get the operator
          f = f[0];
        }
        if (!f.getSort().isConstructor())
        {
          PARSER_STATE->parseError(
              "Bad syntax for test (_ is X), X must be a constructor.");
        }
        // get the datatype that f belongs to
        api::Sort sf = f.getSort().getConstructorCodomainSort();
        api::Datatype d = sf.getDatatype();
        // lookup by name
        api::DatatypeConstructor dc = d.getConstructor(f.toString());
        p.d_expr = dc.getTesterTerm();
      }
    | TUPLE_SEL_TOK m=INTEGER_LITERAL
      {
        // we adopt a special syntax (_ tupSel n)
        p.d_kind = api::APPLY_SELECTOR;
        // put m in expr so that the caller can deal with this case
        p.d_expr = SOLVER->mkReal(AntlrInput::tokenToUnsigned($m));
      }
    | sym=SIMPLE_SYMBOL nonemptyNumeralList[numerals]
      {
        p.d_op = PARSER_STATE->mkIndexedOp(AntlrInput::tokenText($sym), numerals);
      }
    )
    RPAREN_TOK
  ;

/**
 * Matches an atomic term (a term with no subterms).
 * @return the expression expr representing the term or formula.
 */
termAtomic[CVC4::api::Term& atomTerm]
@init {
  CVC4::api::Sort type;
  CVC4::api::Sort type2;
  std::string s;
  std::vector<uint64_t> numerals;
}
    /* constants */
  : INTEGER_LITERAL
    {
      std::string intStr = AntlrInput::tokenText($INTEGER_LITERAL);
      atomTerm = SOLVER->mkReal(intStr);
    }
  | DECIMAL_LITERAL
    {
      std::string realStr = AntlrInput::tokenText($DECIMAL_LITERAL);
      atomTerm = SOLVER->ensureTermSort(SOLVER->mkReal(realStr),
                                        SOLVER->getRealSort());
    }

  // Constants using indexed identifiers, e.g. (_ +oo 8 24) (positive infinity
  // as a 32-bit floating-point constant)
  | LPAREN_TOK INDEX_TOK
    ( EMP_TOK
      sortSymbol[type,CHECK_DECLARED]
      sortSymbol[type2,CHECK_DECLARED]
      {
        // Empty heap constant in seperation logic
        api::Term v1 = SOLVER->mkConst(api::Sort(type), "_emp1");
        api::Term v2 = SOLVER->mkConst(api::Sort(type2), "_emp2");
        atomTerm = SOLVER->mkTerm(api::SEP_EMP, v1, v2);
      }
    | CHAR_TOK HEX_LITERAL 
      {
        std::string hexStr = AntlrInput::tokenTextSubstr($HEX_LITERAL, 2);
        atomTerm = SOLVER->mkChar(hexStr);
      }
    | sym=SIMPLE_SYMBOL nonemptyNumeralList[numerals]
      {
        atomTerm =
          PARSER_STATE->mkIndexedConstant(AntlrInput::tokenText($sym),
                                          numerals);
      }
    )
    RPAREN_TOK

  // Bit-vector constants
  | HEX_LITERAL
    {
      assert(AntlrInput::tokenText($HEX_LITERAL).find("#x") == 0);
      std::string hexStr = AntlrInput::tokenTextSubstr($HEX_LITERAL, 2);
      atomTerm = SOLVER->mkBitVector(hexStr, 16);
    }
  | BINARY_LITERAL
    {
      assert(AntlrInput::tokenText($BINARY_LITERAL).find("#b") == 0);
      std::string binStr = AntlrInput::tokenTextSubstr($BINARY_LITERAL, 2);
      atomTerm = SOLVER->mkBitVector(binStr, 2);
    }

  // String constant
  | str[s,false] { atomTerm = PARSER_STATE->mkStringConstant(s); }

  // NOTE: Theory constants go here

  // Empty tuple constant
  | TUPLE_CONST_TOK
    {
      atomTerm = SOLVER->mkTuple(std::vector<api::Sort>(),
                                 std::vector<api::Term>());
    }
  ;

/**
 * Read attribute
 */
attribute[CVC4::api::Term& expr, CVC4::api::Term& retExpr, std::string& attr]
@init {
  SExpr sexpr;
  CVC4::api::Term patexpr;
  std::vector<CVC4::api::Term> patexprs;
  CVC4::api::Term e2;
  bool hasValue = false;
}
  : KEYWORD ( simpleSymbolicExprNoKeyword[sexpr] { hasValue = true; } )?
  {
    attr = AntlrInput::tokenText($KEYWORD);
    PARSER_STATE->attributeNotSupported(attr);
  }
  | ATTRIBUTE_PATTERN_TOK LPAREN_TOK
    ( term[patexpr, e2]
      { patexprs.push_back( patexpr ); }
    )+ RPAREN_TOK
    {
      attr = std::string(":pattern");
      retExpr = MK_TERM(api::INST_PATTERN, patexprs);
    }
  | ATTRIBUTE_NO_PATTERN_TOK term[patexpr, e2]
    {
      attr = std::string(":no-pattern");
      retExpr = MK_TERM(api::INST_NO_PATTERN, patexpr);
    }
  | tok=( ATTRIBUTE_INST_LEVEL ) INTEGER_LITERAL
    {
      std::stringstream sIntLit;
      sIntLit << $INTEGER_LITERAL;
      api::Term n = SOLVER->mkReal(sIntLit.str());
      std::vector<api::Term> values;
      values.push_back( n );
      std::string attr_name(AntlrInput::tokenText($tok));
      attr_name.erase( attr_name.begin() );
      api::Sort boolType = SOLVER->getBooleanSort();
      api::Term avar = PARSER_STATE->bindVar(attr_name, boolType);
      retExpr = MK_TERM(api::INST_ATTRIBUTE, avar);
      Command* c = new SetUserAttributeCommand(
          attr_name, avar.getExpr(), api::termVectorToExprs(values));
      c->setMuted(true);
      PARSER_STATE->preemptCommand(c);
    }
  | tok=( ATTRIBUTE_QUANTIFIER_ID_TOK ) symbolicExpr[sexpr]
    {
      api::Sort boolType = SOLVER->getBooleanSort();
      api::Term avar = SOLVER->mkConst(boolType, sexpr.toString());
      attr = std::string(":qid");
      retExpr = MK_TERM(api::INST_ATTRIBUTE, avar);
      Command* c = new SetUserAttributeCommand("qid", avar.getExpr());
      c->setMuted(true);
      PARSER_STATE->preemptCommand(c);
    }
  | ATTRIBUTE_NAMED_TOK symbolicExpr[sexpr]
    {
      attr = std::string(":named");
      api::Term func = PARSER_STATE->setNamedAttribute(expr, sexpr);
      std::string name = sexpr.getValue();
      // bind name to expr with define-fun
      Command* c = new DefineNamedFunctionCommand(
          name, func.getExpr(), std::vector<Expr>(), expr.getExpr(), PARSER_STATE->getGlobalDeclarations());
      c->setMuted(true);
      PARSER_STATE->preemptCommand(c);
    }
  ;

/**
 * Matches a sequence of terms and puts them into the formulas
 * vector.
 * @param formulas the vector to fill with terms
 * @param expr an CVC4::api::Term reference for the elements of the sequence
 */
/* NOTE: We pass an CVC4::api::Term in here just to avoid allocating a fresh CVC4::api::Term every
 * time through this rule. */
termList[std::vector<CVC4::api::Term>& formulas, CVC4::api::Term& expr]
@declarations {
  CVC4::api::Term expr2;
}
  : ( term[expr, expr2] { formulas.push_back(expr); } )+
  ;

/**
 * Matches a string, and strips off the quotes.
 */
str[std::string& s, bool fsmtlib]
  : STRING_LITERAL
    {
      s = AntlrInput::tokenText($STRING_LITERAL);
      /* strip off the quotes */
      s = s.substr(1, s.size() - 2);
      for (size_t i = 0; i < s.size(); i++)
      {
        if ((unsigned)s[i] > 127 && !isprint(s[i]))
        {
          PARSER_STATE->parseError(
              "Extended/unprintable characters are not "
              "part of SMT-LIB, and they must be encoded "
              "as escape sequences");
        }
      }
      if (fsmtlib || PARSER_STATE->escapeDupDblQuote())
      {
        char* p_orig = strdup(s.c_str());
        char *p = p_orig, *q = p_orig;
        while (*q != '\0')
        {
          if (PARSER_STATE->escapeDupDblQuote() && *q == '"')
          {
            // Handle SMT-LIB >=2.5 standard escape '""'.
            ++q;
            assert(*q == '"');
          }
          else if (!PARSER_STATE->escapeDupDblQuote() && *q == '\\')
          {
            ++q;
            // Handle SMT-LIB 2.0 standard escapes '\\' and '\"'.
            if (*q != '\\' && *q != '"')
            {
              assert(*q != '\0');
              *p++ = '\\';
            }
          }
          *p++ = *q++;
        }
        *p = '\0';
        s = p_orig;
        free(p_orig);
      }
    }
  ;

quantOp[CVC4::api::Kind& kind]
@init {
  Debug("parser") << "quant: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
  : EXISTS_TOK    { $kind = api::EXISTS; }
  | FORALL_TOK    { $kind = api::FORALL; }
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
sortList[std::vector<CVC4::api::Sort>& sorts]
@declarations {
  CVC4::api::Sort t;
}
  : ( sortSymbol[t,CHECK_DECLARED] { sorts.push_back(t); } )*
  ;

nonemptySortList[std::vector<CVC4::api::Sort>& sorts]
@declarations {
  CVC4::api::Sort t;
}
  : ( sortSymbol[t,CHECK_DECLARED] { sorts.push_back(t); } )+
  ;

/**
 * Matches a sequence of (variable,sort) symbol pairs and fills them
 * into the given vector.
 */
sortedVarList[std::vector<std::pair<std::string, CVC4::api::Sort> >& sortedVars]
@declarations {
  std::string name;
  CVC4::api::Sort t;
}
  : ( LPAREN_TOK symbol[name,CHECK_NONE,SYM_VARIABLE]
      sortSymbol[t,CHECK_DECLARED] RPAREN_TOK
      { sortedVars.push_back(make_pair(name, t)); }
    )*
  ;

/**
 * Matches a sequence of (variable, sort) symbol pairs, registers them as bound
 * variables, and returns a term corresponding to the list of pairs.
 */
boundVarList[CVC4::api::Term& expr]
@declarations {
  std::vector<std::pair<std::string, CVC4::api::Sort>> sortedVarNames;
}
 : LPAREN_TOK sortedVarList[sortedVarNames] RPAREN_TOK
   {
     std::vector<CVC4::api::Term> args =
         PARSER_STATE->bindBoundVars(sortedVarNames);
     expr = MK_TERM(api::BOUND_VAR_LIST, args);
   }
 ;

/**
 * Matches the sort symbol, which can be an arbitrary symbol.
 * @param check the check to perform on the name
 */
sortName[std::string& name, CVC4::parser::DeclarationCheck check]
  : symbol[name,check,SYM_SORT]
  ;

sortSymbol[CVC4::api::Sort& t, CVC4::parser::DeclarationCheck check]
@declarations {
  std::string name;
  std::vector<CVC4::api::Sort> args;
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
      { 
        if (!indexed) 
        {
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
          t = SOLVER->mkBitVectorSort(numerals.front());
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
          t = SOLVER->mkFloatingPointSort(numerals[0],numerals[1]);
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
           PARSER_STATE->isTheoryEnabled(theory::THEORY_ARRAYS) ) {
          if(args.size() != 2) {
            PARSER_STATE->parseError("Illegal array type.");
          }
          t = SOLVER->mkArraySort( args[0], args[1] );
        } else if(name == "Set" &&
                  PARSER_STATE->isTheoryEnabled(theory::THEORY_SETS) ) {
          if(args.size() != 1) {
            PARSER_STATE->parseError("Illegal set type.");
          }
          t = SOLVER->mkSetSort( args[0] );
        } else if(name == "Seq" && !PARSER_STATE->strictModeEnabled() &&
                  PARSER_STATE->isTheoryEnabled(theory::THEORY_STRINGS) ) {
          if(args.size() != 1) {
            PARSER_STATE->parseError("Illegal sequence type.");
          }
          t = SOLVER->mkSequenceSort( args[0] );
        } else if (name == "Tuple" && !PARSER_STATE->strictModeEnabled()) {
          t = SOLVER->mkTupleSort(args);
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
            t = t.instantiate( args );
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
      api::Sort rangeType = args.back();
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
datatypeDef[bool isCo, std::vector<CVC4::api::DatatypeDecl>& datatypes,
            std::vector< CVC4::api::Sort >& params]
@init {
  std::string id;
}
    /* This really needs to be CHECK_NONE, or mutually-recursive
     * datatypes won't work, because this type will already be
     * "defined" as an unresolved type; don't worry, we check
     * below. */
  : symbol[id,CHECK_NONE,SYM_SORT] { PARSER_STATE->pushScope(true); }
    {
      datatypes.push_back(SOLVER->mkDatatypeDecl(id, params, isCo));
    }
    ( LPAREN_TOK constructorDef[datatypes.back()] RPAREN_TOK )+
    { PARSER_STATE->popScope(); }
  ;

/**
 * Parses a constructor defintion for type
 */
constructorDef[CVC4::api::DatatypeDecl& type]
@init {
  std::string id;
  CVC4::api::DatatypeConstructorDecl* ctor = NULL;
}
  : symbol[id,CHECK_NONE,SYM_VARIABLE]
    {
      ctor = new api::DatatypeConstructorDecl(
          SOLVER->mkDatatypeConstructorDecl(id));
    }
    ( LPAREN_TOK selector[*ctor] RPAREN_TOK )*
    { // make the constructor
      type.addConstructor(*ctor);
      Debug("parser-idt") << "constructor: " << id.c_str() << std::endl;
      delete ctor;
    }
  ;

selector[CVC4::api::DatatypeConstructorDecl& ctor]
@init {
  std::string id;
  CVC4::api::Sort t, t2;
}
  : symbol[id,CHECK_NONE,SYM_SORT] sortSymbol[t,CHECK_NONE]
    { 
      ctor.addSelector(id, t);
      Debug("parser-idt") << "selector: " << id.c_str()
                          << " of type " << t << std::endl;
    }
  ;

// Base SMT-LIB tokens
ASSERT_TOK : 'assert';
CHECK_SAT_TOK : 'check-sat';
CHECK_SAT_ASSUMING_TOK : 'check-sat-assuming';
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
GET_UNSAT_ASSUMPTIONS_TOK : 'get-unsat-assumptions';
GET_UNSAT_CORE_TOK : 'get-unsat-core';
EXIT_TOK : 'exit';
RESET_TOK : { PARSER_STATE->v2_5() }? 'reset';
RESET_ASSERTIONS_TOK : 'reset-assertions';
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
CONST_TOK : { !PARSER_STATE->strictModeEnabled() }? 'const';

// extended commands
DECLARE_CODATATYPE_TOK : { PARSER_STATE->v2_6() || PARSER_STATE->sygus() }? 'declare-codatatype';
DECLARE_DATATYPE_TOK : { PARSER_STATE->v2_6() || PARSER_STATE->sygus() }? 'declare-datatype';
DECLARE_DATATYPES_2_5_TOK : { !( PARSER_STATE->v2_6() || PARSER_STATE->sygus() ) }?'declare-datatypes';
DECLARE_DATATYPES_TOK : { PARSER_STATE->v2_6() || PARSER_STATE->sygus() }?'declare-datatypes';
DECLARE_CODATATYPES_2_5_TOK : { !( PARSER_STATE->v2_6() || PARSER_STATE->sygus() ) }?'declare-codatatypes';
DECLARE_CODATATYPES_TOK : { PARSER_STATE->v2_6() || PARSER_STATE->sygus() }?'declare-codatatypes';
PAR_TOK : { PARSER_STATE->v2_6() }?'par';
COMPREHENSION_TOK : { PARSER_STATE->isTheoryEnabled(theory::THEORY_SETS) }?'comprehension';
TESTER_TOK : { ( PARSER_STATE->v2_6() || PARSER_STATE->sygus() ) && PARSER_STATE->isTheoryEnabled(theory::THEORY_DATATYPES) }?'is';
MATCH_TOK : { ( PARSER_STATE->v2_6() || PARSER_STATE->sygus() ) && PARSER_STATE->isTheoryEnabled(theory::THEORY_DATATYPES) }?'match';
GET_MODEL_TOK : 'get-model';
BLOCK_MODEL_TOK : 'block-model';
BLOCK_MODEL_VALUES_TOK : 'block-model-values';
ECHO_TOK : 'echo';
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
GET_ABDUCT_TOK : 'get-abduct';
GET_INTERPOL_TOK : 'get-interpol';
DECLARE_HEAP : 'declare-heap';

// SyGuS commands
SYNTH_FUN_TOK : { PARSER_STATE->sygus() }?'synth-fun';
SYNTH_INV_TOK : { PARSER_STATE->sygus()}?'synth-inv';
CHECK_SYNTH_TOK : { PARSER_STATE->sygus()}?'check-synth';
DECLARE_VAR_TOK : { PARSER_STATE->sygus()}?'declare-var';
CONSTRAINT_TOK : { PARSER_STATE->sygus()}?'constraint';
INV_CONSTRAINT_TOK : { PARSER_STATE->sygus()}?'inv-constraint';
SET_OPTIONS_TOK : { PARSER_STATE->sygus() }? 'set-options';
SYGUS_CONSTANT_TOK : { PARSER_STATE->sygus() }? 'Constant';
SYGUS_VARIABLE_TOK : { PARSER_STATE->sygus() }? 'Variable';

// attributes
ATTRIBUTE_PATTERN_TOK : ':pattern';
ATTRIBUTE_NO_PATTERN_TOK : ':no-pattern';
ATTRIBUTE_NAMED_TOK : ':named';
ATTRIBUTE_INST_LEVEL : ':quant-inst-max-level';
ATTRIBUTE_QUANTIFIER_ID_TOK : ':qid';

// operators (NOTE: theory symbols go here)
EXISTS_TOK        : 'exists';
FORALL_TOK        : 'forall';

EMP_TOK : { PARSER_STATE->isTheoryEnabled(theory::THEORY_SEP) }? 'emp';
CHAR_TOK : { PARSER_STATE->isTheoryEnabled(theory::THEORY_STRINGS) }? 'char';
TUPLE_CONST_TOK: { PARSER_STATE->isTheoryEnabled(theory::THEORY_DATATYPES) }? 'mkTuple';
TUPLE_SEL_TOK: { PARSER_STATE->isTheoryEnabled(theory::THEORY_DATATYPES) }? 'tupSel';

HO_ARROW_TOK : { PARSER_STATE->isHoEnabled() }? '->';
HO_LAMBDA_TOK : { PARSER_STATE->isHoEnabled() }? 'lambda';

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
  : ALPHA (ALPHA | DIGIT | SYMBOL_CHAR)*
  | SYMBOL_CHAR (ALPHA | DIGIT | SYMBOL_CHAR)+
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
 * Matches a double-quoted string literal. Depending on the language that is
 * being parsed, different escape sequences are supported:
 *
 * For SMT-LIB 2.0 the sequence \" is interpreted as a double quote (") and the
 * sequence \\ is interpreted as a backslash (\).
 *
 * For SMT-LIB >=2.5 and SyGuS a double-quote inside a string is escaped with
 * "", e.g., "This is a string literal with "" a single, embedded double
 * quote."
 *
 * You shouldn't generally use this in parser rules, as the quotes
 * will be part of the token text.  Use the str[] parser rule instead.
 */
STRING_LITERAL
  : { !PARSER_STATE->escapeDupDblQuote() }?=>
    '"' ('\\' . | ~('\\' | '"'))* '"'
  | { PARSER_STATE->escapeDupDblQuote() }?=>
    '"' (~('"') | '""')* '"'
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
