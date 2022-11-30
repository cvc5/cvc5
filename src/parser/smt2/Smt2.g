/* ****************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Parser for SMT-LIB v2 input language.
 */

grammar Smt2;

options {
  // C output for antlr
  language = 'C';

  // Skip the default error handling, just break with exceptions
  // defaultErrorHandler = false;

  // Only lookahead of <= k requested (disable for LL* parsing)
  // Note that cvc5's BoundedTokenBuffer requires a fixed k !
  // If you change this k, change it also in smt2_input.cpp !
  k = 2;
}/* options */

@header {
/* ****************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 */
}/* @header */

@lexer::includes {

/** This suppresses warnings about the redefinition of token symbols between
  * different parsers. The redefinitions should be harmless as long as no
  * client: (a) #include's the lexer headers for two grammars AND (b) uses the
  * token symbol definitions.
  */
#pragma GCC system_header

#if defined(CVC5_COMPETITION_MODE) && !defined(CVC5_SMTCOMP_APPLICATION_TRACK)
/* This improves performance by ~10 percent on big inputs.
 * This option is only valid if we know the input is ASCII (or some 8-bit encoding).
 * If we know the input is UTF-16, we can use ANTLR3_INLINE_INPUT_UTF16.
 * Otherwise, we have to let the lexer detect the encoding at runtime.
 */
#  define ANTLR3_INLINE_INPUT_ASCII
#  define ANTLR3_INLINE_INPUT_8BIT
#endif /* CVC5_COMPETITION_MODE && !CVC5_SMTCOMP_APPLICATION_TRACK */

}/* @lexer::includes */

@lexer::postinclude {
#include "parser/smt2/smt2.h"
#include "parser/antlr_input.h"

using namespace cvc5;
using namespace cvc5::parser;

#undef PARSER_STATE
#define PARSER_STATE ((Smt2*)LEXER->super)
}/* @lexer::postinclude */

@parser::includes {

#include <memory>

#include "base/check.h"
#include "parser/parse_op.h"
#include "parser/parser.h"
#include "parser/api/cpp/command.h"

namespace cvc5 {

class Term;
class Sort;

}/* cvc5 namespace */

}/* @parser::includes */

@parser::postinclude {

#include <set>
#include <sstream>
#include <string>
#include <unordered_set>
#include <vector>

#include "api/cpp/cvc5.h"
#include "base/output.h"
#include "parser/antlr_input.h"
#include "parser/parser.h"
#include "parser/smt2/smt2.h"
#include "util/floatingpoint_size.h"
#include "util/hash.h"

using namespace cvc5;
using namespace cvc5::parser;

/* These need to be macros so they can refer to the PARSER macro, which
 * will be defined by ANTLR *after* this section. (If they were functions,
 * PARSER would be undefined.) */
#undef PARSER_STATE
#define PARSER_STATE ((Smt2*)PARSER->super)
#undef SOLVER
#define SOLVER PARSER_STATE->getSolver()
#undef SYM_MAN
#define SYM_MAN PARSER_STATE->getSymbolManager()
#undef MK_TERM
#define MK_TERM(KIND, ...) SOLVER->mkTerm(KIND, {__VA_ARGS__})
#define UNSUPPORTED PARSER_STATE->unimplementedFeature

}/* parser::postinclude */

/**
 * Parses an expression.
 * @return the parsed expression, or the Null Expr if we've reached the
 * end of the input
 */
parseExpr returns [cvc5::Term expr = cvc5::Term()]
@declarations {
  cvc5::Term expr2;
}
  : term[expr, expr2]
  | EOF
  ;

/**
 * Parses a command
 * @return the parsed command, or NULL if we've reached the end of the input
 */
parseCommand returns [cvc5::parser::Command* cmd_return = NULL]
@declarations {
  std::unique_ptr<cvc5::parser::Command> cmd;
  std::string name;
}
@after {
  cmd_return = cmd.release();
}
  : LPAREN_TOK command[&cmd] RPAREN_TOK

    /* This extended command has to be in the outermost production so that
     * the RPAREN_TOK is properly eaten and we are in a good state to read
     * the included file's tokens. */
  | LPAREN_TOK INCLUDE_TOK str[name, true] RPAREN_TOK
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
parseSygus returns [cvc5::parser::Command* cmd_return = NULL]
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
command [std::unique_ptr<cvc5::parser::Command>* cmd]
@declarations {
  std::string name;
  std::vector<std::string> names;
  cvc5::Term expr, expr2;
  cvc5::Sort t;
  std::vector<cvc5::Term> terms;
  std::vector<cvc5::Sort> sorts;
  std::vector<std::pair<std::string, cvc5::Sort> > sortedVarNames;
  std::vector<cvc5::Term> flattenVars;
  bool readKeyword = false;
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
    { Trace("parser") << "declare sort: '" << name
                      << "' arity=" << n << std::endl;
      unsigned arity = AntlrInput::tokenToUnsigned(n);
      if(arity == 0) {
        cvc5::Sort type = PARSER_STATE->mkSort(name);
        cmd->reset(new DeclareSortCommand(name, 0, type));
      } else {
        cvc5::Sort type = PARSER_STATE->mkSortConstructor(name, arity);
        cmd->reset(new DeclareSortCommand(name, arity, type));
      }
    }
  | /* sort definition */
    DEFINE_SORT_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    symbol[name,CHECK_UNDECLARED,SYM_SORT]
    { PARSER_STATE->checkUserSymbol(name); }
    LPAREN_TOK symbolList[names,CHECK_UNDECLARED,SYM_SORT] RPAREN_TOK
    { PARSER_STATE->pushScope();
      for(std::vector<std::string>::const_iterator i = names.begin(),
            iend = names.end();
          i != iend;
          ++i) {
        sorts.push_back(PARSER_STATE->mkSort(*i));
      }
    }
    sortSymbol[t]
    { PARSER_STATE->popScope();
      // Do NOT call mkSort, since that creates a new sort!
      // This name is not its own distinct sort, it's an alias.
      PARSER_STATE->defineParameterizedType(name, sorts, t);
      cmd->reset(new DefineSortCommand(name, sorts, t));
    }
  | /* function declaration */
    DECLARE_FUN_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    symbol[name,CHECK_NONE,SYM_VARIABLE]
    { PARSER_STATE->checkUserSymbol(name); }
    LPAREN_TOK sortList[sorts] RPAREN_TOK
    sortSymbol[t]
    { Trace("parser") << "declare fun: '" << name << "'" << std::endl;
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
        PARSER_STATE->parseError("declare-fun are not allowed in sygus "
                                 "version 2.0");
      }
      else
      {
        cvc5::Term func =
            PARSER_STATE->bindVar(name, t, true);
        cmd->reset(new DeclareFunctionCommand(name, func, t));
      }
    }
  | /* function definition */
    DEFINE_FUN_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    symbol[name,CHECK_UNDECLARED,SYM_VARIABLE]
    { PARSER_STATE->checkUserSymbol(name); }
    LPAREN_TOK sortedVarList[sortedVarNames] RPAREN_TOK
    sortSymbol[t]
    { /* add variables to parser state before parsing term */
      Trace("parser") << "define fun: '" << name << "'" << std::endl;
      if( sortedVarNames.size() > 0 ) {
        sorts.reserve(sortedVarNames.size());
        for(std::vector<std::pair<std::string, cvc5::Sort> >::const_iterator i =
              sortedVarNames.begin(), iend = sortedVarNames.end();
            i != iend;
            ++i) {
          sorts.push_back((*i).second);
        }
      }

      t = PARSER_STATE->mkFlatFunctionType(sorts, t, flattenVars);
      if (t.isFunction())
      {
        t = t.getFunctionCodomainSort();
      }
      if (sortedVarNames.size() > 0)
      {
        PARSER_STATE->pushScope();
      }
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
      if (sortedVarNames.size() > 0)
      {
        PARSER_STATE->popScope();
      }
      cmd->reset(new DefineFunctionCommand(name, terms, t, expr));
    }
  | DECLARE_DATATYPE_TOK datatypeDefCommand[false, cmd]
  | DECLARE_DATATYPES_TOK datatypesDefCommand[false, cmd]
  | /* value query */
    GET_VALUE_TOK
    {
      PARSER_STATE->checkThatLogicIsSet();
      // bind all symbols specific to the model, e.g. uninterpreted constant
      // values
      PARSER_STATE->pushGetValueScope();
    }
    ( LPAREN_TOK termList[terms,expr] RPAREN_TOK
      { cmd->reset(new GetValueCommand(terms)); }
    | ~LPAREN_TOK
      { PARSER_STATE->parseError("The get-value command expects a list of "
                                 "terms.  Perhaps you forgot a pair of "
                                 "parentheses?");
      }
    )
    { PARSER_STATE->popScope(); }
  | /* get-assignment */
    GET_ASSIGNMENT_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    { cmd->reset(new GetAssignmentCommand()); }
  | /* assertion */
    ASSERT_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    { PARSER_STATE->clearLastNamedTerm(); }
    term[expr, expr2]
    { cmd->reset(new AssertCommand(expr));
      if (PARSER_STATE->lastNamedTerm().first == expr)
      {
        Trace("parser") << "Process top-level name: " << expr << std::endl;
        // set the expression name, if there was a named term
        std::pair<cvc5::Term, std::string> namedTerm =
            PARSER_STATE->lastNamedTerm();
        SYM_MAN->setExpressionName(namedTerm.first, namedTerm.second, true);
        Trace("parser") << "finished process top-level name" << std::endl;
      }
    }
  | /* check-sat */
    CHECK_SAT_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    {
      if (PARSER_STATE->sygus()) {
        PARSER_STATE->parseError("Sygus does not support check-sat command.");
      }
      cmd->reset(new CheckSatCommand());
    }
  | /* check-sat-assuming */
    CHECK_SAT_ASSUMING_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    ( LPAREN_TOK termList[terms,expr] RPAREN_TOK
      {
        cmd->reset(new CheckSatAssumingCommand(terms));
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
    GET_PROOF_TOK ( KEYWORD { readKeyword = true; }  )? {
      PARSER_STATE->checkThatLogicIsSet();
      modes::ProofComponent pc = modes::PROOF_COMPONENT_FULL;
      if (readKeyword)
      {
        pc = PARSER_STATE->getProofComponent(
               AntlrInput::tokenText($KEYWORD).c_str() + 1);
      }
      cmd->reset(new GetProofCommand(pc));
    }
  | /* get-unsat-assumptions */
    GET_UNSAT_ASSUMPTIONS_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    { cmd->reset(new GetUnsatAssumptionsCommand); }
  | /* get-unsat-core */
    GET_UNSAT_CORE_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    { cmd->reset(new GetUnsatCoreCommand); }
  | /* get-difficulty */
    GET_DIFFICULTY_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    { cmd->reset(new GetDifficultyCommand); }
  | /* get-learned-literals */
    GET_LEARNED_LITERALS_TOK ( KEYWORD { readKeyword = true; } )? {
      PARSER_STATE->checkThatLogicIsSet();
      modes::LearnedLitType llt = modes::LEARNED_LIT_INPUT;
      if (readKeyword)
      {
        llt = PARSER_STATE->getLearnedLitType(
                AntlrInput::tokenText($KEYWORD).c_str() + 1);
      }
      cmd->reset(new GetLearnedLiteralsCommand(llt)); }
  | /* push */
    PUSH_TOK
    ( k=INTEGER_LITERAL
      {
        uint32_t num = AntlrInput::tokenToUnsigned(k);
        *cmd = PARSER_STATE->handlePush(num);
      }
    | {
        *cmd = PARSER_STATE->handlePush(std::nullopt);
      }
    )
  | /* pop */
    POP_TOK
    ( k=INTEGER_LITERAL
      {
        uint32_t num = AntlrInput::tokenToUnsigned(k);
        *cmd = PARSER_STATE->handlePop(num);
      }
    | {
        *cmd = PARSER_STATE->handlePop(std::nullopt);
      }
    )
    /* exit */
  | EXIT_TOK
    { cmd->reset(new QuitCommand()); }

    /* New SMT-LIB 2.5 command set */
  | smt25Command[cmd]

    /* cvc5-extended SMT-LIB commands */
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

sygusCommand returns [std::unique_ptr<cvc5::parser::Command> cmd]
@declarations {
  cvc5::Term expr, expr2, fun;
  cvc5::Sort t, range;
  std::vector<std::string> names;
  std::vector<std::pair<std::string, cvc5::Sort> > sortedVarNames;
  std::vector<cvc5::Term> sygusVars;
  std::string name;
  bool isAssume;
  bool isInv;
  cvc5::Grammar* grammar = nullptr;
}
  : /* declare-var */
    DECLARE_VAR_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    symbol[name,CHECK_UNDECLARED,SYM_VARIABLE]
    { PARSER_STATE->checkUserSymbol(name); }
    sortSymbol[t]
    {
      cvc5::Term var = SOLVER->declareSygusVar(name, t);
      PARSER_STATE->defineVar(name, var);
      cmd.reset(new DeclareSygusVarCommand(name, var, t));
    }
  | /* synth-fun */
    ( SYNTH_FUN_TOK { isInv = false; }
      | SYNTH_INV_TOK { isInv = true; range = SOLVER->getBooleanSort(); }
    )
    { PARSER_STATE->checkThatLogicIsSet(); }
    symbol[name,CHECK_UNDECLARED,SYM_VARIABLE]
    LPAREN_TOK sortedVarList[sortedVarNames] RPAREN_TOK
    ( sortSymbol[range] )?
    {
      PARSER_STATE->pushScope();
      sygusVars = PARSER_STATE->bindBoundVars(sortedVarNames);
    }
    (
      // optionally, read the sygus grammar
      //
      // `grammar` specifies the required grammar for the function to
      // synthesize, expressed as a type
      sygusGrammar[grammar, sygusVars, name]
    )?
    {
      Trace("parser-sygus") << "Define synth fun : " << name << std::endl;

      fun = isInv ? (grammar == nullptr
                         ? SOLVER->synthInv(name, sygusVars)
                         : SOLVER->synthInv(name, sygusVars, *grammar))
                  : (grammar == nullptr
                         ? SOLVER->synthFun(name, sygusVars, range)
                         : SOLVER->synthFun(name, sygusVars, range, *grammar));

      Trace("parser-sygus") << "...read synth fun " << name << std::endl;
      PARSER_STATE->popScope();
      // we do not allow overloading for synth fun
      PARSER_STATE->defineVar(name, fun);
      cmd = std::unique_ptr<cvc5::parser::Command>(
          new SynthFunCommand(name, fun, sygusVars, range, isInv, grammar));
    }
  | /* constraint */
    ( CONSTRAINT_TOK { isAssume = false; } | ASSUME_TOK { isAssume = true; } )
    {
      PARSER_STATE->checkThatLogicIsSet();
    }
    term[expr, expr2]
    { Trace("parser-sygus") << "...read constraint " << expr << std::endl;
      cmd.reset(new SygusConstraintCommand(expr, isAssume));
    }
  | /* inv-constraint */
    INV_CONSTRAINT_TOK
    ( symbol[name,CHECK_NONE,SYM_VARIABLE] { names.push_back(name); } )+
    {
      cmd = PARSER_STATE->invConstraint(names);
    }
  | /* check-synth */
    CHECK_SYNTH_TOK
    {
      PARSER_STATE->checkThatLogicIsSet();
      cmd.reset(new CheckSynthCommand());
    }
  | /* check-synth-next */
    CHECK_SYNTH_NEXT_TOK
    {
      PARSER_STATE->checkThatLogicIsSet();
      cmd.reset(new CheckSynthCommand(true));
    }
  | /* set-feature */
    SET_FEATURE_TOK keyword[name] symbolicExpr[expr]
    {
      PARSER_STATE->checkThatLogicIsSet();
      // ":grammars" is defined in the SyGuS version 2.1 standard and is by
      // default supported, all other features are not.
      if (name != ":grammars")
      {
        std::stringstream ss;
        ss << "SyGuS feature " << name << " not currently supported";
        PARSER_STATE->warning(ss.str());
      }
      cmd.reset(new EmptyCommand());
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
sygusGrammar[cvc5::Grammar*& ret,
             const std::vector<cvc5::Term>& sygusVars,
             const std::string& fun]
@declarations
{
  // the pre-declaration
  std::vector<std::pair<std::string, cvc5::Sort>> sortedVarNames;
  // non-terminal symbols of the grammar
  std::vector<cvc5::Term> ntSyms;
  cvc5::Sort t;
  std::string name;
  cvc5::Term e, e2;
  unsigned dtProcessed = 0;
}
  :
  // predeclaration
  LPAREN_TOK
  // We read a sorted variable list here in a custom way that throws an
  // error to recognize if the user is using the (deprecated) version 1.0
  // sygus syntax.
  ( LPAREN_TOK symbol[name,CHECK_NONE,SYM_VARIABLE]
    sortSymbol[t] (
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
              << "and examples. cvc5 versions past 1.8 do not support SyGuS "
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
    PARSER_STATE->pushScope();
    for (std::pair<std::string, cvc5::Sort>& i : sortedVarNames)
    {
      PARSER_STATE->checkDeclaration(name, CHECK_UNDECLARED, SYM_SORT);
      // make the non-terminal symbol, which will be parsed as an ordinary
      // free variable.
      cvc5::Term nts = PARSER_STATE->bindBoundVar(i.first, i.second);
      ntSyms.push_back(nts);
    }
    ret = PARSER_STATE->mkGrammar(sygusVars, ntSyms);
  }
  // the grouped rule listing
  LPAREN_TOK
  (
    LPAREN_TOK
    symbol[name, CHECK_DECLARED, SYM_VARIABLE] sortSymbol[t]
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
        ret->addRule(ntSyms[dtProcessed], e);
      }
      | LPAREN_TOK SYGUS_CONSTANT_TOK sortSymbol[t] RPAREN_TOK {
        // allow constants in datatype for ntSyms[dtProcessed]
        ret->addAnyConstant(ntSyms[dtProcessed]);
      }
      | LPAREN_TOK SYGUS_VARIABLE_TOK sortSymbol[t] RPAREN_TOK {
        // add variable constructors to datatype
        ret->addAnyVariable(ntSyms[dtProcessed]);
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
    // pop scope from the pre-declaration
    PARSER_STATE->popScope();
  }
;

setInfoInternal[std::unique_ptr<cvc5::parser::Command>* cmd]
@declarations {
  std::string name;
  cvc5::Term sexpr;
}
  : keyword[name] symbolicExpr[sexpr]
    { cmd->reset(new SetInfoCommand(name.c_str() + 1, sexprToString(sexpr))); }
  ;

setOptionInternal[std::unique_ptr<cvc5::parser::Command>* cmd]
@init {
  std::string name;
  cvc5::Term sexpr;
}
  : keyword[name] symbolicExpr[sexpr]
    { cmd->reset(new SetOptionCommand(name.c_str() + 1, sexprToString(sexpr)));
      // Ugly that this changes the state of the parser; but
      // global-declarations affects parsing, so we can't hold off
      // on this until some SolverEngine eventually (if ever) executes it.
      if(name == ":global-declarations")
      {
        SYM_MAN->setGlobalDeclarations(sexprToString(sexpr) == "true");
      }
    }
  ;

smt25Command[std::unique_ptr<cvc5::parser::Command>* cmd]
@declarations {
  std::string name;
  std::string fname;
  cvc5::Term expr, expr2;
  std::vector<std::pair<std::string, cvc5::Sort> > sortedVarNames;
  std::string s;
  cvc5::Sort t;
  cvc5::Term func;
  std::vector<cvc5::Term> bvs;
  std::vector<std::vector<std::pair<std::string, cvc5::Sort>>>
      sortedVarNamesList;
  std::vector<std::vector<cvc5::Term>> flattenVarsList;
  std::vector<std::vector<cvc5::Term>> formals;
  std::vector<cvc5::Term> funcs;
  std::vector<cvc5::Term> func_defs;
  cvc5::Term aexpr;
  std::vector<cvc5::Sort> sorts;
  std::vector<cvc5::Term> flattenVars;
}
    /* declare-const */
  : DECLARE_CONST_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    symbol[name,CHECK_NONE,SYM_VARIABLE]
    { PARSER_STATE->checkUserSymbol(name); }
    sortSymbol[t]
    { // allow overloading here
      if( PARSER_STATE->sygus() )
      {
        PARSER_STATE->parseError("declare-const is not allowed in sygus "
                                 "version 2.0");
      }
      cvc5::Term c =
          PARSER_STATE->bindVar(name, t, true);
      cmd->reset(new DeclareFunctionCommand(name, c, t)); }

    /* get model */
  | GET_MODEL_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    { cmd->reset(new GetModelCommand()); }

    /* echo */
  | ECHO_TOK
    ( str[s, true]
      { cmd->reset(new EchoCommand(s)); }
    | { cmd->reset(new EchoCommand()); }
    )

    /* reset: reset everything, returning solver to initial state.
     * Logic and options must be set again. */
  | RESET_TOK
    {
      cmd->reset(new ResetCommand());
      // reset the state of the parser, which is independent of the symbol
      // manager
      PARSER_STATE->reset();
    }
    /* reset-assertions: reset assertions, assertion stack, declarations,
     * etc., but the logic and options remain as they were. */
  | RESET_ASSERTIONS_TOK
    { cmd->reset(new ResetAssertionsCommand());
    }
  | DEFINE_FUN_REC_TOK
    { PARSER_STATE->checkThatLogicIsSet(); }
    symbol[fname,CHECK_NONE,SYM_VARIABLE]
    { PARSER_STATE->checkUserSymbol(fname); }
    LPAREN_TOK sortedVarList[sortedVarNames] RPAREN_TOK
    sortSymbol[t]
    {
      func =
          PARSER_STATE->bindDefineFunRec(fname, sortedVarNames, t, flattenVars);
      PARSER_STATE->pushDefineFunRecScope(
          sortedVarNames, func, flattenVars, bvs);
    }
    term[expr, expr2]
    { PARSER_STATE->popScope();
      if( !flattenVars.empty() ){
        expr = PARSER_STATE->mkHoApply( expr, flattenVars );
      }
      cmd->reset(new DefineFunctionRecCommand(func, bvs, expr));
    }
  | DEFINE_FUNS_REC_TOK
    { PARSER_STATE->checkThatLogicIsSet();}
    LPAREN_TOK
    ( LPAREN_TOK
      symbol[fname,CHECK_UNDECLARED,SYM_VARIABLE]
      { PARSER_STATE->checkUserSymbol(fname); }
      LPAREN_TOK sortedVarList[sortedVarNames] RPAREN_TOK
      sortSymbol[t]
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
                                           flattenVarsList[0], bvs);
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
                                             flattenVarsList[j], bvs);
      }
    }
    )+
    RPAREN_TOK
    { if( funcs.size()!=func_defs.size() ){
        PARSER_STATE->parseError(std::string(
            "Number of functions defined does not match number listed in "
            "define-funs-rec"));
      }
      cmd->reset(new DefineFunctionRecCommand(funcs, formals, func_defs));
    }
  ;

extendedCommand[std::unique_ptr<cvc5::parser::Command>* cmd]
@declarations {
  std::vector<cvc5::DatatypeDecl> dts;
  cvc5::Term e, e2;
  cvc5::Sort t, s;
  std::string name;
  std::vector<std::string> names;
  std::vector<cvc5::Term> terms;
  std::vector<cvc5::Sort> sorts;
  std::vector<std::pair<std::string, cvc5::Sort> > sortedVarNames;
  cvc5::Grammar* g = nullptr;
}
    /* Extended SMT-LIB set of commands syntax, not permitted in
     * --smtlib2 compliance mode. */
  : DECLARE_CODATATYPE_TOK datatypeDefCommand[true, cmd]
  | DECLARE_CODATATYPES_TOK datatypesDefCommand[true, cmd]

    /* Support some of Z3's extended SMT-LIB commands */

  | // (define-const x U t)
    DEFINE_CONST_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    symbol[name,CHECK_UNDECLARED,SYM_VARIABLE]
    { PARSER_STATE->checkUserSymbol(name); }
    sortSymbol[t]
    term[e, e2]
    {
      // declare the name down here (while parsing term, signature
      // must not be extended with the name itself; no recursion
      // permitted)
      cmd->reset(new DefineFunctionCommand(name, t, e));
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
  | GET_ABDUCT_TOK {
      PARSER_STATE->checkThatLogicIsSet();
    }
    symbol[name,CHECK_UNDECLARED,SYM_VARIABLE]
    term[e,e2]
    (
      sygusGrammar[g, terms, name]
    )?
    {
      cmd->reset(new GetAbductCommand(name, e, g));
    }
  | GET_ABDUCT_NEXT_TOK {
      PARSER_STATE->checkThatLogicIsSet();
      cmd->reset(new GetAbductNextCommand);
    }
  | GET_INTERPOL_TOK {
      PARSER_STATE->checkThatLogicIsSet();
    }
    symbol[name,CHECK_UNDECLARED,SYM_VARIABLE]
    term[e,e2]
    (
      sygusGrammar[g, terms, name]
    )?
    {
      cmd->reset(new GetInterpolantCommand(name, e, g));
    }
  | GET_INTERPOL_NEXT_TOK {
      PARSER_STATE->checkThatLogicIsSet();
      cmd->reset(new GetInterpolantNextCommand);
    }
  | DECLARE_HEAP LPAREN_TOK
    sortSymbol[t]
    sortSymbol[s]
    { cmd->reset(new DeclareHeapCommand(t, s)); }
    RPAREN_TOK
  | DECLARE_POOL { PARSER_STATE->checkThatLogicIsSet(); }
    symbol[name,CHECK_NONE,SYM_VARIABLE]
    { PARSER_STATE->checkUserSymbol(name); }
    sortSymbol[t]
    LPAREN_TOK
    ( term[e, e2]
      { terms.push_back( e ); }
    )* RPAREN_TOK
    { Trace("parser") << "declare pool: '" << name << "'" << std::endl;
      cvc5::Term pool = SOLVER->declarePool(name, t, terms);
      PARSER_STATE->defineVar(name, pool);
      cmd->reset(new DeclarePoolCommand(name, pool, t, terms));
    }
  | BLOCK_MODEL_TOK KEYWORD { PARSER_STATE->checkThatLogicIsSet(); }
    {
      modes::BlockModelsMode mode =
        PARSER_STATE->getBlockModelsMode(
          AntlrInput::tokenText($KEYWORD).c_str() + 1);
      cmd->reset(new BlockModelCommand(mode));
    }
  | BLOCK_MODEL_VALUES_TOK { PARSER_STATE->checkThatLogicIsSet(); }
    ( LPAREN_TOK termList[terms,e] RPAREN_TOK
      { cmd->reset(new BlockModelValuesCommand(terms)); }
    | ~LPAREN_TOK
      { PARSER_STATE->parseError("The block-model-value command expects a list "
                                 "of terms.  Perhaps you forgot a pair of "
                                 "parentheses?");
      }
    )
  ;

datatypeDefCommand[bool isCo, std::unique_ptr<cvc5::parser::Command>* cmd]
@declarations {
  std::vector<cvc5::DatatypeDecl> dts;
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

datatypesDefCommand[bool isCo, std::unique_ptr<cvc5::parser::Command>* cmd]
@declarations {
  std::vector<cvc5::DatatypeDecl> dts;
  std::string name;
  std::vector<std::string> dnames;
  std::vector<int> arities;
}
  : { PARSER_STATE->checkThatLogicIsSet(); }
  LPAREN_TOK /* datatype definition prelude */
  ( LPAREN_TOK symbol[name,CHECK_UNDECLARED,SYM_SORT] n=INTEGER_LITERAL RPAREN_TOK
    { unsigned arity = AntlrInput::tokenToUnsigned(n);
      Trace("parser-dt") << "Datatype : " << name << ", arity = " << arity << std::endl;
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
             std::unique_ptr<cvc5::parser::Command>* cmd]
@declarations {
  std::vector<cvc5::DatatypeDecl> dts;
  std::string name;
  std::vector<cvc5::Sort> params;
}
  : { PARSER_STATE->pushScope();
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
      Trace("parser-dt") << "Processing datatype #" << dts.size() << std::endl;
      if( dts.size()>=dnames.size() ){
        PARSER_STATE->parseError("Too many datatypes defined in this block.");
      }
    }
    ( PAR_TOK { PARSER_STATE->pushScope(); } LPAREN_TOK
      ( symbol[name,CHECK_UNDECLARED,SYM_SORT]
        {
          params.push_back( PARSER_STATE->mkSort(name)); }
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
        Trace("parser-dt") << params.size() << " parameters for " << dnames[dts.size()] << std::endl;
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
        Trace("parser-dt") << params.size() << " parameters for " << dnames[dts.size()] << std::endl;
        dts.push_back(SOLVER->mkDatatypeDecl(dnames[dts.size()],
                                             params,
                                             isCo));
      }
      ( LPAREN_TOK constructorDef[dts.back()] RPAREN_TOK )+
    )
    RPAREN_TOK
    )+
  {
    if (dts.size() != dnames.size())
    {
      PARSER_STATE->parseError("Wrong number of datatypes provided.");
    }
    PARSER_STATE->popScope();
    cmd->reset(new DatatypeDeclarationCommand(
        PARSER_STATE->bindMutualDatatypeTypes(dts, true)));
  }
  ;

simpleSymbolicExprNoKeyword[std::string& s]
  : INTEGER_LITERAL
    { s = AntlrInput::tokenText($INTEGER_LITERAL); }
  | DECIMAL_LITERAL
    { s = AntlrInput::tokenText($DECIMAL_LITERAL); }
  | HEX_LITERAL
    { s = AntlrInput::tokenText($HEX_LITERAL); }
  | BINARY_LITERAL
    { s = AntlrInput::tokenText($BINARY_LITERAL); }
  | symbol[s, CHECK_NONE, SYM_VERBATIM]
  | str[s, false]
  | tok=(ASSERT_TOK | CHECK_SAT_TOK | CHECK_SAT_ASSUMING_TOK | DECLARE_FUN_TOK
        | DECLARE_SORT_TOK
        | DEFINE_FUN_TOK | DEFINE_FUN_REC_TOK | DEFINE_FUNS_REC_TOK
        | DEFINE_SORT_TOK | GET_VALUE_TOK | GET_ASSIGNMENT_TOK
        | GET_ASSERTIONS_TOK | GET_PROOF_TOK | GET_UNSAT_ASSUMPTIONS_TOK
        | GET_UNSAT_CORE_TOK | GET_DIFFICULTY_TOK | EXIT_TOK
        | RESET_TOK | RESET_ASSERTIONS_TOK | SET_LOGIC_TOK | SET_INFO_TOK
        | GET_INFO_TOK | SET_OPTION_TOK | GET_OPTION_TOK | PUSH_TOK | POP_TOK
        | DECLARE_DATATYPES_TOK | GET_MODEL_TOK | ECHO_TOK | SIMPLIFY_TOK)
    { s = AntlrInput::tokenText($tok); }
  ;

keyword[std::string& s]
  : KEYWORD
    { s = AntlrInput::tokenText($KEYWORD); }
  ;

simpleSymbolicExpr[std::string& s]
  : simpleSymbolicExprNoKeyword[s]
  | KEYWORD { s = AntlrInput::tokenText($KEYWORD); }
  ;

symbolicExpr[cvc5::Term& sexpr]
@declarations {
  std::string s;
  std::vector<cvc5::Term> children;
}
  : simpleSymbolicExpr[s]
    { sexpr = SOLVER->mkString(PARSER_STATE->processAdHocStringEsc(s)); }
  | LPAREN_TOK
    ( symbolicExpr[sexpr] { children.push_back(sexpr); } )* RPAREN_TOK
    { sexpr = SOLVER->mkTerm(cvc5::SEXPR, children); }
  ;

/**
 * Matches a term.
 * @return the expression representing the term.
 */
term[cvc5::Term& expr, cvc5::Term& expr2]
@init {
  cvc5::Kind kind = cvc5::NULL_TERM;
  cvc5::Term f;
  std::string name;
  cvc5::Sort type;
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
termNonVariable[cvc5::Term& expr, cvc5::Term& expr2]
@init {
  Trace("parser") << "term: " << AntlrInput::tokenText(LT(1)) << std::endl;
  cvc5::Kind kind = cvc5::NULL_TERM;
  std::string name;
  std::vector<cvc5::Term> args;
  std::vector< std::pair<std::string, cvc5::Sort> > sortedVarNames;
  cvc5::Term bvl;
  cvc5::Term f, f2, f3;
  std::string attr;
  cvc5::Term attexpr;
  std::vector<cvc5::Term> patexprs;
  std::vector<cvc5::Term> matchcases;
  std::unordered_set<std::string> names;
  std::vector< std::pair<std::string, cvc5::Term> > binders;
  cvc5::Sort type;
  cvc5::Sort type2;
  cvc5::Term atomTerm;
  ParseOp p;
  std::vector<cvc5::Sort> argTypes;
}
  : LPAREN_TOK quantOp[kind]
    {
      if (!PARSER_STATE->isTheoryEnabled(internal::theory::THEORY_QUANTIFIERS))
      {
        PARSER_STATE->parseError("Quantifier used in non-quantified logic.");
      }
      PARSER_STATE->pushScope();
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
  | LPAREN_TOK SET_COMPREHENSION_TOK
    { PARSER_STATE->pushScope(); }
    boundVarList[bvl]
    {
      args.push_back(bvl);
    }
    term[f, f2] { args.push_back(f); }
    term[f, f2] {
      args.push_back(f);
      expr = MK_TERM(cvc5::SET_COMPREHENSION, args);
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
      { PARSER_STATE->pushScope(); }
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
      for (const std::pair<std::string, cvc5::Term>& binder : binders)
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
          PARSER_STATE->pushScope();
          // f should be a constructor
          type = f.getSort();
          Trace("parser-dt") << "Pattern head : " << f << " " << type << std::endl;
          if (!type.isDatatypeConstructor())
          {
            PARSER_STATE->parseError("Pattern must be application of a constructor or a variable.");
          }
          cvc5::Datatype dt =
              type.getDatatypeConstructorCodomainSort().getDatatype();
          if (dt.isParametric())
          {
            // lookup constructor by name
            cvc5::DatatypeConstructor dc = dt.getConstructor(f.toString());
            cvc5::Term scons = dc.getInstantiatedTerm(expr.getSort());
            // take the type of the specialized constructor instead
            type = scons.getSort();
          }
          argTypes = type.getDatatypeConstructorDomainSorts();
        }
        // arguments of the pattern
        ( symbol[name,CHECK_NONE,SYM_VARIABLE] {
            if (args.size() >= argTypes.size())
            {
              PARSER_STATE->parseError("Too many arguments for pattern.");
            }
            //make of proper type
            cvc5::Term arg = PARSER_STATE->bindBoundVar(name, argTypes[args.size()]);
            args.push_back( arg );
          }
        )*
        RPAREN_TOK term[f3, f2] {
          // make the match case
          std::vector<cvc5::Term> cargs;
          cargs.push_back(f);
          cargs.insert(cargs.end(),args.begin(),args.end());
          cvc5::Term c = MK_TERM(cvc5::APPLY_CONSTRUCTOR,cargs);
          cvc5::Term bvla = MK_TERM(cvc5::VARIABLE_LIST,args);
          cvc5::Term mc = MK_TERM(cvc5::MATCH_BIND_CASE, bvla, c, f3);
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
            if (!type.isDatatypeConstructor() ||
                !type.getDatatypeConstructorDomainSorts().empty())
            {
              PARSER_STATE->parseError("Must apply constructors of arity greater than 0 to arguments in pattern.");
            }
            // make nullary constructor application
            f = MK_TERM(cvc5::APPLY_CONSTRUCTOR, f);
          }
          else
          {
            // it has the type of the head expr
            f = PARSER_STATE->bindBoundVar(name, expr.getSort());
          }
        }
        term[f3, f2] {
          cvc5::Term mc;
          if (f.getKind() == cvc5::VARIABLE)
          {
            cvc5::Term bvlf = MK_TERM(cvc5::VARIABLE_LIST, f);
            mc = MK_TERM(cvc5::MATCH_BIND_CASE, bvlf, f, f3);
          }
          else
          {
            mc = MK_TERM(cvc5::MATCH_CASE, f, f3);
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
      std::vector<cvc5::Term> mchildren;
      mchildren.push_back(expr);
      mchildren.insert(mchildren.end(), matchcases.begin(), matchcases.end());
      expr = MK_TERM(cvc5::MATCH, mchildren);
    }

    /* attributed expressions */
  | LPAREN_TOK ATTRIBUTE_TOK term[expr, f2]
    ( attribute[expr, attexpr]
      { if( ! attexpr.isNull()) {
          patexprs.push_back( attexpr );
        }
      }
    )+ RPAREN_TOK
    {
      if(! patexprs.empty()) {
        if( !f2.isNull() && f2.getKind()==cvc5::INST_PATTERN_LIST ){
          for( size_t i=0; i<f2.getNumChildren(); i++ ){
            patexprs.push_back( f2[i] );
          }
        }
        expr2 = MK_TERM(cvc5::INST_PATTERN_LIST, patexprs);
      } else {
        expr2 = f2;
      }
    }
  | /* lambda */
    LPAREN_TOK HO_LAMBDA_TOK
    { PARSER_STATE->pushScope(); }
    boundVarList[bvl]
    term[f, f2] RPAREN_TOK
    {
      args.push_back(bvl);
      args.push_back(f);
      PARSER_STATE->popScope();
      expr = MK_TERM(cvc5::LAMBDA, args);
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
 * - For tuple selectors (_ tuple_select n) and updaters (_ tuple_update n), we
 * return (1) and (3). cvc5::Kind is set to APPLY_SELECTOR or APPLY_UPDATER
 * respectively, and expr is set to n, which is to be interpreted by the
 * caller as the n^th generic tuple selector or updater. We do this since there
 * is no AST expression representing generic tuple select, and we do not have
 * enough type information at this point to know the type of the tuple we will
 * be selecting from.
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
 * - For other ascripted nullary constants like (as set.empty (Set T)),
 * (as sep.nil T), we return the appropriate expression (3).
 * - For array constant specifications (as const (Array T1 T2)), we return (1)
 * and (4), where kind is set to STORE_ALL and type is set to (Array T1 T2),
 * where this is to be interpreted by the caller as converting the next parsed
 * constant of type T2 to an Array of type (Array T1 T2) over that constant.
 * - For ascriptions on normal symbols (as f T), we return the appropriate
 * expression (3), which may involve disambiguating f based on type T if it is
 * overloaded.
 */
qualIdentifier[cvc5::ParseOp& p]
@init {
  cvc5::Kind k;
  std::string baseName;
  cvc5::Term f;
  cvc5::Sort type;
}
: identifier[p]
  | LPAREN_TOK AS_TOK
    ( CONST_TOK sortSymbol[type]
      {
        p.d_kind = cvc5::CONST_ARRAY;
        PARSER_STATE->parseOpApplyTypeAscription(p, type);
      }
    | identifier[p]
      sortSymbol[type]
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
identifier[cvc5::ParseOp& p]
@init {
  cvc5::Term f;
  cvc5::Term f2;
  std::vector<uint32_t> numerals;
  std::string opName;
}
: functionName[p.d_name, CHECK_NONE]

  // indexed functions

  | LPAREN_TOK INDEX_TOK
    ( TESTER_TOK term[f, f2]
      {
        if (f.getKind() == cvc5::APPLY_CONSTRUCTOR && f.getNumChildren() == 1)
        {
          // for nullary constructors, must get the operator
          f = f[0];
        }
        if (!f.getSort().isDatatypeConstructor())
        {
          PARSER_STATE->parseError(
              "Bad syntax for (_ is X), X must be a constructor.");
        }
        // get the datatype that f belongs to
        cvc5::Sort sf = f.getSort().getDatatypeConstructorCodomainSort();
        cvc5::Datatype d = sf.getDatatype();
        // lookup by name
        cvc5::DatatypeConstructor dc = d.getConstructor(f.toString());
        p.d_expr = dc.getTesterTerm();
      }
    | UPDATE_TOK term[f, f2]
      {
        if (!f.getSort().isDatatypeSelector())
        {
          PARSER_STATE->parseError(
              "Bad syntax for (_ update X), X must be a selector.");
        }
        std::string sname = f.toString();
        // get the datatype that f belongs to
        cvc5::Sort sf = f.getSort().getDatatypeSelectorDomainSort();
        cvc5::Datatype d = sf.getDatatype();
        // find the selector
        cvc5::DatatypeSelector ds = d.getSelector(f.toString());
        // get the updater term
        p.d_expr = ds.getUpdaterTerm();
      }
    | functionName[opName, CHECK_NONE] nonemptyNumeralList[numerals]
      {
        cvc5::Kind k = PARSER_STATE->getIndexedOpKind(opName);
        if (k == cvc5::UNDEFINED_KIND)
        {
          // We don't know which kind to use until we know the type of the
          // arguments
          p.d_name = opName;
          p.d_indices = numerals;
          p.d_kind = cvc5::UNDEFINED_KIND;
        }
        else if (k == cvc5::APPLY_SELECTOR || k == cvc5::APPLY_UPDATER)
        {
          // we adopt a special syntax (_ tuple_select n) and (_ tuple_update n)
          // for tuple selectors and updaters
          if (numerals.size() != 1)
          {
            PARSER_STATE->parseError(
                "Unexpected syntax for tuple selector or updater.");
          }
          // The operator is dependent upon inferring the type of the arguments,
          // and hence the type is not available yet. Hence, we remember the
          // index as a numeral in the parse operator.
          p.d_kind = k;
          p.d_expr = SOLVER->mkInteger(numerals[0]);
        }
        else
        {
          p.d_op = SOLVER->mkOp(k, numerals);
        }
      }
    )
    RPAREN_TOK
  ;

/**
 * Matches an atomic term (a term with no subterms).
 * @return the expression expr representing the term or formula.
 */
termAtomic[cvc5::Term& atomTerm]
@init {
  cvc5::Sort t;
  std::string s;
  std::vector<uint32_t> numerals;
}
    /* constants */
  : INTEGER_LITERAL
    {
      std::string intStr = AntlrInput::tokenText($INTEGER_LITERAL);
      atomTerm = PARSER_STATE->mkRealOrIntFromNumeral(intStr);
    }
  | DECIMAL_LITERAL
    {
      std::string realStr = AntlrInput::tokenText($DECIMAL_LITERAL);
      atomTerm = SOLVER->mkReal(realStr);
    }

  // Constants using indexed identifiers, e.g. (_ +oo 8 24) (positive infinity
  // as a 32-bit floating-point constant)
  | LPAREN_TOK INDEX_TOK
    ( CHAR_TOK HEX_LITERAL
      {
        std::string hexStr = AntlrInput::tokenTextSubstr($HEX_LITERAL, 2);
        atomTerm = PARSER_STATE->mkCharConstant(hexStr);
      }
    | FMF_CARD_TOK sortSymbol[t] INTEGER_LITERAL
      {
        uint32_t ubound = AntlrInput::tokenToUnsigned($INTEGER_LITERAL);
        atomTerm = SOLVER->mkCardinalityConstraint(t, ubound);
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
      Assert(AntlrInput::tokenText($HEX_LITERAL).find("#x") == 0);
      std::string hexStr = AntlrInput::tokenTextSubstr($HEX_LITERAL, 2);
      atomTerm = SOLVER->mkBitVector(hexStr.size() * 4, hexStr, 16);
    }
  | BINARY_LITERAL
    {
      Assert(AntlrInput::tokenText($BINARY_LITERAL).find("#b") == 0);
      std::string binStr = AntlrInput::tokenTextSubstr($BINARY_LITERAL, 2);
      atomTerm = SOLVER->mkBitVector(binStr.size(), binStr, 2);
    }

  // String constant
  | str[s, true] { atomTerm = SOLVER->mkString(s, true); }
  ;

/**
 * Read attribute
 */
attribute[cvc5::Term& expr, cvc5::Term& retExpr]
@init {
  cvc5::Term sexpr;
  std::string s;
  cvc5::Term patexpr;
  std::vector<cvc5::Term> patexprs;
  cvc5::Term e2;
  bool hasValue = false;
  cvc5::Kind k;
}
  : KEYWORD ( simpleSymbolicExprNoKeyword[s] { hasValue = true; } )?
  {
    PARSER_STATE->attributeNotSupported(AntlrInput::tokenText($KEYWORD));
  }
  | ( ATTRIBUTE_PATTERN_TOK { k = cvc5::INST_PATTERN; } |
      ATTRIBUTE_POOL_TOK { k = cvc5::INST_POOL; }  |
      ATTRIBUTE_INST_ADD_TO_POOL_TOK { k = cvc5::INST_ADD_TO_POOL; }  |
      ATTRIBUTE_SKOLEM_ADD_TO_POOL_TOK{ k = cvc5::SKOLEM_ADD_TO_POOL; }
    )
    LPAREN_TOK
    ( term[patexpr, e2]
      { patexprs.push_back( patexpr ); }
    )+ RPAREN_TOK
    {
      retExpr = MK_TERM(k, patexprs);
    }
  | ATTRIBUTE_NO_PATTERN_TOK term[patexpr, e2]
    {
      retExpr = MK_TERM(cvc5::INST_NO_PATTERN, patexpr);
    }
  | tok=( ATTRIBUTE_INST_LEVEL ) INTEGER_LITERAL
    {
      std::stringstream sIntLit;
      sIntLit << $INTEGER_LITERAL;
      cvc5::Term keyword = SOLVER->mkString("quant-inst-max-level");
      cvc5::Term n = SOLVER->mkInteger(sIntLit.str());
      retExpr = MK_TERM(cvc5::INST_ATTRIBUTE, keyword, n);
    }
  | tok=( ATTRIBUTE_QUANTIFIER_ID_TOK ) symbol[s,CHECK_UNDECLARED,SYM_VARIABLE]
    {
      cvc5::Term keyword = SOLVER->mkString("qid");
      // must create a variable whose name is the name of the quantified
      // formula, not a string.
      cvc5::Term name = SOLVER->mkConst(SOLVER->getBooleanSort(), s);
      retExpr = MK_TERM(cvc5::INST_ATTRIBUTE, keyword, name);
    }
  | ATTRIBUTE_NAMED_TOK symbol[s,CHECK_UNDECLARED,SYM_VARIABLE]
    {
      Trace("parser") << "Named: " << s << " for " << expr << std::endl;
      PARSER_STATE->notifyNamedExpression(expr, s);
    }
  ;

/**
 * Matches a sequence of terms and puts them into the formulas
 * vector.
 * @param formulas the vector to fill with terms
 * @param expr an cvc5::Term reference for the elements of the sequence
 */
/* NOTE: We pass an cvc5::Term in here just to avoid allocating a fresh cvc5::Term every
 * time through this rule. */
termList[std::vector<cvc5::Term>& formulas, cvc5::Term& expr]
@declarations {
  cvc5::Term expr2;
}
  : ( term[expr, expr2] { formulas.push_back(expr); } )+
  ;

/**
 * Matches a string, and (optionally) strips off the quotes/unescapes the
 * string when `unescape` is set to true.
 */
str[std::string& s, bool unescape]
  : STRING_LITERAL
    {
      s = AntlrInput::tokenText($STRING_LITERAL);
      if (unescape)
      {
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
        char* p_orig = strdup(s.c_str());
        char *p = p_orig, *q = p_orig;
        while (*q != '\0')
        {
          if (*q == '"')
          {
            // Handle SMT-LIB >=2.5 standard escape '""'.
            ++q;
            Assert(*q == '"');
          }
          *p++ = *q++;
        }
        *p = '\0';
        s = p_orig;
        free(p_orig);
      }
    }
  | UNTERMINATED_STRING_LITERAL EOF
    { PARSER_STATE->unexpectedEOF("unterminated string literal"); }
  ;

quantOp[cvc5::Kind& kind]
@init {
  Trace("parser") << "quant: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
  : EXISTS_TOK    { $kind = cvc5::EXISTS; }
  | FORALL_TOK    { $kind = cvc5::FORALL; }
  ;

/**
 * Matches a (possibly undeclared) function symbol (returning the string)
 * @param check what kind of check to do with the symbol
 */
functionName[std::string& name, cvc5::parser::DeclarationCheck check]
  : symbol[name,check,SYM_VARIABLE]
  ;

/**
 * Matches a sequence of sort symbols and fills them into the given
 * vector.
 */
sortList[std::vector<cvc5::Sort>& sorts]
@declarations {
  cvc5::Sort t;
}
  : ( sortSymbol[t] { sorts.push_back(t); } )*
  ;

nonemptySortList[std::vector<cvc5::Sort>& sorts]
@declarations {
  cvc5::Sort t;
}
  : ( sortSymbol[t] { sorts.push_back(t); } )+
  ;

/**
 * Matches a sequence of (variable,sort) symbol pairs and fills them
 * into the given vector.
 */
sortedVarList[std::vector<std::pair<std::string, cvc5::Sort> >& sortedVars]
@declarations {
  std::string name;
  cvc5::Sort t;
}
  : ( LPAREN_TOK symbol[name,CHECK_NONE,SYM_VARIABLE]
      sortSymbol[t] RPAREN_TOK
      { sortedVars.push_back(make_pair(name, t)); }
    )*
  ;

/**
 * Matches a sequence of (variable, sort) symbol pairs, registers them as bound
 * variables, and returns a term corresponding to the list of pairs.
 */
boundVarList[cvc5::Term& expr]
@declarations {
  std::vector<std::pair<std::string, cvc5::Sort>> sortedVarNames;
}
 : LPAREN_TOK sortedVarList[sortedVarNames] RPAREN_TOK
   {
     std::vector<cvc5::Term> args =
         PARSER_STATE->bindBoundVars(sortedVarNames);
     expr = MK_TERM(cvc5::VARIABLE_LIST, args);
   }
 ;

/**
 * Matches the sort symbol, which can be an arbitrary symbol.
 * @param check the check to perform on the name
 */
sortName[std::string& name, cvc5::parser::DeclarationCheck check]
  : symbol[name,check,SYM_SORT]
  ;

sortSymbol[cvc5::Sort& t]
@declarations {
  std::string name;
  std::vector<cvc5::Sort> args;
  std::vector<uint32_t> numerals;
  bool indexed = false;
}
  : sortName[name,CHECK_NONE]
    {
      t = PARSER_STATE->getSort(name);
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
          if(!internal::validExponentSize(numerals[0])) {
            PARSER_STATE->parseError("Illegal floating-point exponent size");
          }
          if(!internal::validSignificandSize(numerals[1])) {
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
           PARSER_STATE->isTheoryEnabled(internal::theory::THEORY_ARRAYS) ) {
          if(args.size() != 2) {
            PARSER_STATE->parseError("Illegal array type.");
          }
          t = SOLVER->mkArraySort( args[0], args[1] );
        } else if(name == "Set" &&
                  PARSER_STATE->isTheoryEnabled(internal::theory::THEORY_SETS) ) {
          if(args.size() != 1) {
            PARSER_STATE->parseError("Illegal set type.");
          }
          t = SOLVER->mkSetSort( args[0] );
        }
        else if(name == "Bag" &&
                  PARSER_STATE->isTheoryEnabled(internal::theory::THEORY_BAGS) ) {
          if(args.size() != 1) {
            PARSER_STATE->parseError("Illegal bag type.");
          }
          t = SOLVER->mkBagSort( args[0] );
        }
        else if(name == "Seq" && !PARSER_STATE->strictModeEnabled() &&
                  PARSER_STATE->isTheoryEnabled(internal::theory::THEORY_STRINGS) ) {
          if(args.size() != 1) {
            PARSER_STATE->parseError("Illegal sequence type.");
          }
          t = SOLVER->mkSequenceSort( args[0] );
        } else if (name == "Tuple" && !PARSER_STATE->strictModeEnabled()) {
          t = SOLVER->mkTupleSort(args);
        } else if (name == "Relation" && !PARSER_STATE->strictModeEnabled()) {
          cvc5::Sort tupleSort = SOLVER->mkTupleSort(args);
          t = SOLVER->mkSetSort(tupleSort);
        } else if (name == "Table" && !PARSER_STATE->strictModeEnabled()) {
          cvc5::Sort tupleSort = SOLVER->mkTupleSort(args);
          t = SOLVER->mkBagSort(tupleSort);
        } else if (name == "->" && PARSER_STATE->isHoEnabled()) {
          if(args.size()<2) {
            PARSER_STATE->parseError("Arrow types must have at least 2 arguments");
          }
          //flatten the type
          cvc5::Sort rangeType = args.back();
          args.pop_back();
          t = PARSER_STATE->mkFlatFunctionType( args, rangeType );
        } else {
          t = PARSER_STATE->getSort(name, args);
        }
      }
    ) RPAREN_TOK
  ;

/**
 * Matches a list of symbols, with check and type arguments as for the
 * symbol[] rule below.
 */
symbolList[std::vector<std::string>& names,
           cvc5::parser::DeclarationCheck check,
           cvc5::parser::SymbolType type]
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
       cvc5::parser::DeclarationCheck check,
       cvc5::parser::SymbolType type]
  : SIMPLE_SYMBOL
    { id = AntlrInput::tokenText($SIMPLE_SYMBOL);
      if(!PARSER_STATE->isAbstractValue(id)) {
        // if an abstract value, SolverEngine handles declaration
        PARSER_STATE->checkDeclaration(id, check, type);
      }
    }
  | QUOTED_SYMBOL
    { id = AntlrInput::tokenText($QUOTED_SYMBOL);
      if (type != SymbolType::SYM_VERBATIM)
      {
        /* strip off the quotes */
        id = id.substr(1, id.size() - 2);
      }
      if(!PARSER_STATE->isAbstractValue(id)) {
        // if an abstract value, SolverEngine handles declaration
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
nonemptyNumeralList[std::vector<uint32_t>& numerals]
  : ( INTEGER_LITERAL
      { numerals.push_back(AntlrInput::tokenToUnsigned($INTEGER_LITERAL)); }
    )+
  ;

/**
 * Parses a datatype definition
 */
datatypeDef[bool isCo, std::vector<cvc5::DatatypeDecl>& datatypes,
            std::vector< cvc5::Sort >& params]
@init {
  std::string id;
}
    /* This really needs to be CHECK_NONE, or mutually-recursive
     * datatypes won't work, because this type will already be
     * "defined" as an unresolved type; don't worry, we check
     * below. */
  : symbol[id,CHECK_NONE,SYM_SORT] { PARSER_STATE->pushScope(); }
    {
      datatypes.push_back(SOLVER->mkDatatypeDecl(id, params, isCo));
    }
    ( LPAREN_TOK constructorDef[datatypes.back()] RPAREN_TOK )+
    { PARSER_STATE->popScope(); }
  ;

/**
 * Parses a constructor defintion for type
 */
constructorDef[cvc5::DatatypeDecl& type]
@init {
  std::string id;
  cvc5::DatatypeConstructorDecl* ctor = NULL;
}
  : symbol[id,CHECK_NONE,SYM_VARIABLE]
    {
      ctor = new cvc5::DatatypeConstructorDecl(
          SOLVER->mkDatatypeConstructorDecl(id));
    }
    ( LPAREN_TOK selector[*ctor] RPAREN_TOK )*
    { // make the constructor
      type.addConstructor(*ctor);
      Trace("parser-idt") << "constructor: " << id.c_str() << std::endl;
      delete ctor;
    }
  ;

selector[cvc5::DatatypeConstructorDecl& ctor]
@init {
  std::string id;
  cvc5::Sort t, t2;
}
  : symbol[id,CHECK_NONE,SYM_SORT] sortSymbol[t]
    {
      ctor.addSelector(id, t);
      Trace("parser-idt") << "selector: " << id.c_str()
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
GET_DIFFICULTY_TOK : 'get-difficulty';
GET_LEARNED_LITERALS_TOK : { !PARSER_STATE->strictModeEnabled() }? 'get-learned-literals';
EXIT_TOK : 'exit';
RESET_TOK : 'reset';
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
DECLARE_CODATATYPE_TOK : 'declare-codatatype';
DECLARE_DATATYPE_TOK : 'declare-datatype';
DECLARE_DATATYPES_TOK : 'declare-datatypes';
DECLARE_CODATATYPES_TOK : 'declare-codatatypes';
PAR_TOK : 'par';
SET_COMPREHENSION_TOK : { PARSER_STATE->isTheoryEnabled(internal::theory::THEORY_SETS) }?'set.comprehension';
TESTER_TOK : { PARSER_STATE->isTheoryEnabled(internal::theory::THEORY_DATATYPES) }?'is';
UPDATE_TOK : { PARSER_STATE->isTheoryEnabled(internal::theory::THEORY_DATATYPES) }?'update';
MATCH_TOK : 'match';
GET_MODEL_TOK : 'get-model';
BLOCK_MODEL_TOK : 'block-model';
BLOCK_MODEL_VALUES_TOK : 'block-model-values';
ECHO_TOK : 'echo';
DECLARE_CONST_TOK : 'declare-const';
DEFINE_CONST_TOK : 'define-const';
SIMPLIFY_TOK : 'simplify';
INCLUDE_TOK : 'include';
GET_QE_TOK : 'get-qe';
GET_QE_DISJUNCT_TOK : 'get-qe-disjunct';
GET_ABDUCT_TOK : 'get-abduct';
GET_ABDUCT_NEXT_TOK : 'get-abduct-next';
GET_INTERPOL_TOK : 'get-interpolant';
GET_INTERPOL_NEXT_TOK : 'get-interpolant-next';
DECLARE_HEAP : 'declare-heap';
DECLARE_POOL : 'declare-pool';

// SyGuS commands
SYNTH_FUN_TOK : { PARSER_STATE->sygus() }?'synth-fun';
SYNTH_INV_TOK : { PARSER_STATE->sygus()}?'synth-inv';
CHECK_SYNTH_TOK : { PARSER_STATE->sygus()}?'check-synth';
CHECK_SYNTH_NEXT_TOK : { PARSER_STATE->sygus()}?'check-synth-next';
DECLARE_VAR_TOK : { PARSER_STATE->sygus()}?'declare-var';
CONSTRAINT_TOK : { PARSER_STATE->sygus()}?'constraint';
ASSUME_TOK : { PARSER_STATE->sygus()}?'assume';
INV_CONSTRAINT_TOK : { PARSER_STATE->sygus()}?'inv-constraint';
SET_FEATURE_TOK : { PARSER_STATE->sygus() }? 'set-feature';
SYGUS_CONSTANT_TOK : { PARSER_STATE->hasGrammars() }? 'Constant';
SYGUS_VARIABLE_TOK : { PARSER_STATE->sygus() }? 'Variable';

// attributes
ATTRIBUTE_PATTERN_TOK : ':pattern';
ATTRIBUTE_NO_PATTERN_TOK : ':no-pattern';
ATTRIBUTE_POOL_TOK : ':pool';
ATTRIBUTE_INST_ADD_TO_POOL_TOK : ':inst-add-to-pool';
ATTRIBUTE_SKOLEM_ADD_TO_POOL_TOK : ':skolem-add-to-pool';
ATTRIBUTE_NAMED_TOK : ':named';
ATTRIBUTE_INST_LEVEL : ':quant-inst-max-level';
ATTRIBUTE_QUANTIFIER_ID_TOK : ':qid';

// operators (NOTE: theory symbols go here)
EXISTS_TOK        : 'exists';
FORALL_TOK        : 'forall';

CHAR_TOK : { PARSER_STATE->isTheoryEnabled(internal::theory::THEORY_STRINGS) }? 'char';
FMF_CARD_TOK: { !PARSER_STATE->strictModeEnabled() && PARSER_STATE->hasCardinalityConstraints() }? 'fmf.card';

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
    { Trace("parser-extra") << "NUMERAL: "
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
 * Matches a double-quoted string literal. A double-quote inside a string is
 * escaped with "", e.g., "This is a string literal with "" a single, embedded
 * double quote."
 *
 * You shouldn't generally use this in parser rules, as the quotes will be part
 * of the token text.  Use the str[] parser rule instead.
 */
STRING_LITERAL
  : '"' (~('"') | '""')* '"'
  ;

UNTERMINATED_STRING_LITERAL
  : '"' (~('"') | '""')*
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
