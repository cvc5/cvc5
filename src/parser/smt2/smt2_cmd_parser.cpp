/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The smt2 command parser.
 */

#include "parser/smt2/smt2_cmd_parser.h"

#include "base/check.h"
#include "base/output.h"
#include "parser/api/cpp/command.h"

namespace cvc5 {
namespace parser {

Smt2CmdParser::Smt2CmdParser(Smt2Lexer& lex,
                             Smt2State& state,
                             Smt2TermParser& tparser)
    : d_lex(lex), d_state(state), d_tparser(tparser)
{
}

std::unique_ptr<Command> Smt2CmdParser::parseNextCommand()
{
  // if we are at the end of file, return the null command
  if (d_lex.eatTokenChoice(Token::EOF_TOK, Token::LPAREN_TOK))
  {
    return nullptr;
  }
  std::unique_ptr<Command> cmd;
  Token tok = d_lex.nextToken();
  switch (tok)
  {
    // (assert <term>)
    case Token::ASSERT_TOK:
    {
      d_state.checkThatLogicIsSet();
      d_state.clearLastNamedTerm();
      Term t = d_tparser.parseTerm();
      cmd.reset(new AssertCommand(t));
      if (d_state.lastNamedTerm().first == t)
      {
        Trace("parser") << "Process top-level name: " << t << std::endl;
        // set the expression name, if there was a named term
        std::pair<Term, std::string> namedTerm = d_state.lastNamedTerm();
        d_state.getSymbolManager()->setExpressionName(
            namedTerm.first, namedTerm.second, true);
        Trace("parser") << "finished process top-level name" << std::endl;
      }
    }
    break;
    // sygus assume/constraint
    // (assume <term>)
    // (constraint <term>)
    case Token::ASSUME_TOK:
    case Token::CONSTRAINT_TOK:
    {
      bool isAssume = (tok == Token::ASSUME_TOK);
      d_state.checkThatLogicIsSet();
      Term t = d_tparser.parseTerm();
      cmd.reset(new SygusConstraintCommand(t, isAssume));
    }
    break;
    // (block-model <keyword>)
    case Token::BLOCK_MODEL_TOK:
    {
      std::string key = d_tparser.parseKeyword();
      d_state.checkThatLogicIsSet();
      modes::BlockModelsMode mode = d_state.getBlockModelsMode(key);
      cmd.reset(new BlockModelCommand(mode));
    }
    break;
    // (block-model-values (<term>*))
    case Token::BLOCK_MODEL_VALUES_TOK:
    {
      d_state.checkThatLogicIsSet();
      std::vector<Term> terms = d_tparser.parseTermList();
      cmd.reset(new BlockModelValuesCommand(terms));
    }
    break;
    // (check-sat)
    case Token::CHECK_SAT_TOK:
    {
      d_state.checkThatLogicIsSet();
      if (d_state.sygus())
      {
        d_lex.parseError("Sygus does not support check-sat command.");
      }
      cmd.reset(new CheckSatCommand());
    }
    break;
    // (check-sat-assuming (<term>*))
    case Token::CHECK_SAT_ASSUMING_TOK:
    {
      d_state.checkThatLogicIsSet();
      std::vector<Term> terms = d_tparser.parseTermList();
      cmd.reset(new CheckSatAssumingCommand(terms));
    }
    break;
    // (check-synth)
    case Token::CHECK_SYNTH_TOK:
    {
      d_state.checkThatLogicIsSet();
      cmd.reset(new CheckSynthCommand());
    }
    break;
    // (check-synth-next)
    case Token::CHECK_SYNTH_NEXT_TOK:
    {
      d_state.checkThatLogicIsSet();
      cmd.reset(new CheckSynthCommand(true));
    }
    break;
    // single datatype
    // (declare-datatype <symbol> <datatype_dec>)
    // (declare-codatatype <symbol> <datatype_dec>)
    case Token::DECLARE_CODATATYPE_TOK:
    case Token::DECLARE_DATATYPE_TOK:
    {
      d_state.checkThatLogicIsSet();
      std::vector<std::string> dnames;
      std::vector<size_t> arities;
      std::string name = d_tparser.parseSymbol(CHECK_UNDECLARED, SYM_SORT);
      dnames.push_back(name);
      bool isCo = (tok == Token::DECLARE_CODATATYPE_TOK);
      // parse <datatype_dec>
      std::vector<DatatypeDecl> dts =
          d_tparser.parseDatatypesDef(isCo, dnames, arities);
      cmd.reset(new DatatypeDeclarationCommand(
          d_state.bindMutualDatatypeTypes(dts, true)));
    }
    break;
    // multiple datatype
    // (declare-datatypes (<sort_dec>^{n+1}) (<datatype_dec>^{n+1}) )
    // (declare-codatatypes (<sort_dec>^{n+1}) (<datatype_dec>^{n+1}) )
    case Token::DECLARE_CODATATYPES_TOK:
    case Token::DECLARE_DATATYPES_TOK:
    {
      d_state.checkThatLogicIsSet();
      d_lex.eatToken(Token::LPAREN_TOK);
      std::vector<std::string> dnames;
      std::vector<size_t> arities;
      // parse (<sort_dec>^{n+1})
      // while the next token is LPAREN, exit if RPAREN
      while (d_lex.eatTokenChoice(Token::LPAREN_TOK, Token::RPAREN_TOK))
      {
        std::string name = d_tparser.parseSymbol(CHECK_UNDECLARED, SYM_SORT);
        size_t arity = d_tparser.parseIntegerNumeral();
        dnames.push_back(name);
        arities.push_back(arity);
        d_lex.eatToken(Token::RPAREN_TOK);
      }
      if (dnames.empty())
      {
        d_lex.parseError("Empty list of datatypes");
      }
      bool isCo = (tok == Token::DECLARE_CODATATYPES_TOK);
      // parse (<datatype_dec>^{n+1})
      d_lex.eatToken(Token::LPAREN_TOK);
      std::vector<DatatypeDecl> dts =
          d_tparser.parseDatatypesDef(isCo, dnames, arities);
      d_lex.eatToken(Token::RPAREN_TOK);
      cmd.reset(new DatatypeDeclarationCommand(
          d_state.bindMutualDatatypeTypes(dts, true)));
    }
    break;
    // (declare-fun <symbol> (<sort>∗) <sort>)
    // (declare-const <symbol> <sort>)
    case Token::DECLARE_CONST_TOK:
    case Token::DECLARE_FUN_TOK:
    {
      d_state.checkThatLogicIsSet();
      std::string name = d_tparser.parseSymbol(CHECK_NONE, SYM_VARIABLE);
      d_state.checkUserSymbol(name);
      std::vector<Sort> sorts;
      if (tok == Token::DECLARE_FUN_TOK)
      {
        sorts = d_tparser.parseSortList();
      }
      Sort t = d_tparser.parseSort();
      Trace("parser") << "declare fun: '" << name << "'" << std::endl;
      if (!sorts.empty())
      {
        t = d_state.mkFlatFunctionType(sorts, t);
      }
      if (t.isFunction())
      {
        d_state.checkLogicAllowsFunctions();
      }
      // we allow overloading for function declarations
      if (d_state.sygus())
      {
        d_lex.parseError("declare-fun are not allowed in sygus version 2.0");
      }
      else
      {
        Term func = d_state.getSolver()->mkConst(t, name);
        cmd.reset(new DeclareFunctionCommand(name, func, t));
      }
    }
    break;
    // (declare-heap (<sort> <sort>))
    case Token::DECLARE_HEAP:
    {
      d_lex.eatToken(Token::LPAREN_TOK);
      Sort t = d_tparser.parseSort();
      Sort s = d_tparser.parseSort();
      cmd.reset(new DeclareHeapCommand(t, s));
      d_lex.eatToken(Token::RPAREN_TOK);
    }
    break;
    // (declare-pool <symbol> <sort> (<term>∗))
    case Token::DECLARE_POOL:
    {
      d_state.checkThatLogicIsSet();
      std::string name = d_tparser.parseSymbol(CHECK_NONE, SYM_VARIABLE);
      d_state.checkUserSymbol(name);
      Sort t = d_tparser.parseSort();
      std::vector<Term> terms = d_tparser.parseTermList();
      Trace("parser") << "declare pool: '" << name << "'" << std::endl;
      Term pool = d_state.getSolver()->declarePool(name, t, terms);
      cmd.reset(new DeclarePoolCommand(name, pool, t, terms));
    }
    break;
    // (declare-sort <symbol> <numeral>)
    case Token::DECLARE_SORT_TOK:
    {
      d_state.checkThatLogicIsSet();
      d_state.checkLogicAllowsFreeSorts();
      std::string name = d_tparser.parseSymbol(CHECK_UNDECLARED, SYM_SORT);
      d_state.checkUserSymbol(name);
      size_t arity = d_tparser.parseIntegerNumeral();
      Trace("parser") << "declare sort: '" << name << "' arity=" << arity
                      << std::endl;
      if (arity == 0)
      {
        Sort type = d_state.getSolver()->mkUninterpretedSort(name);
        cmd.reset(new DeclareSortCommand(name, 0, type));
      }
      else
      {
        Sort type = d_state.getSolver()->mkUninterpretedSortConstructorSort(
            arity, name);
        cmd.reset(new DeclareSortCommand(name, arity, type));
      }
    }
    break;
    // (declare-var <symbol> <sort>)
    case Token::DECLARE_VAR_TOK:
    {
      d_state.checkThatLogicIsSet();
      std::string name = d_tparser.parseSymbol(CHECK_UNDECLARED, SYM_VARIABLE);
      d_state.checkUserSymbol(name);
      Sort t = d_tparser.parseSort();
      Term var = d_state.getSolver()->declareSygusVar(name, t);
      cmd.reset(new DeclareSygusVarCommand(name, var, t));
    }
    break;
    // (define-const <symbol> <sort> <term>)
    case Token::DEFINE_CONST_TOK:
    {
      d_state.checkThatLogicIsSet();
      std::string name = d_tparser.parseSymbol(CHECK_UNDECLARED, SYM_VARIABLE);
      d_state.checkUserSymbol(name);
      Sort t = d_tparser.parseSort();
      Term e = d_tparser.parseTerm();

      // declare the name down here (while parsing term, signature
      // must not be extended with the name itself; no recursion
      // permitted)
      cmd.reset(new DefineFunctionCommand(name, t, e));
    }
    break;
    // (define-fun <symbol> (<sorted_var>*) <sort> <term>)
    case Token::DEFINE_FUN_TOK:
    {
      d_state.checkThatLogicIsSet();
      std::string name = d_tparser.parseSymbol(CHECK_UNDECLARED, SYM_VARIABLE);
      d_state.checkUserSymbol(name);
      std::vector<std::pair<std::string, Sort>> sortedVarNames =
          d_tparser.parseSortedVarList();
      Sort t = d_tparser.parseSort();
      /* add variables to parser state before parsing term */
      Trace("parser") << "define fun: '" << name << "'" << std::endl;
      std::vector<Sort> sorts;
      if (sortedVarNames.size() > 0)
      {
        sorts.reserve(sortedVarNames.size());
        for (const std::pair<std::string, Sort>& i : sortedVarNames)
        {
          sorts.push_back(i.second);
        }
      }
      std::vector<Term> flattenVars;
      t = d_state.mkFlatFunctionType(sorts, t, flattenVars);
      if (t.isFunction())
      {
        t = t.getFunctionCodomainSort();
      }
      if (sortedVarNames.size() > 0)
      {
        d_state.pushScope();
      }
      std::vector<Term> terms = d_state.bindBoundVars(sortedVarNames);
      Term expr = d_tparser.parseTerm();
      if (!flattenVars.empty())
      {
        // if this function has any implicit variables flattenVars,
        // we apply the body of the definition to the flatten vars
        expr = d_state.mkHoApply(expr, flattenVars);
        terms.insert(terms.end(), flattenVars.begin(), flattenVars.end());
      }
      if (sortedVarNames.size() > 0)
      {
        d_state.popScope();
      }
      cmd.reset(new DefineFunctionCommand(name, terms, t, expr));
    }
    break;
    // (define-fun-rec <symbol> (<sorted_var>*) <sort> <term>)
    case Token::DEFINE_FUN_REC_TOK:
    {
      d_state.checkThatLogicIsSet();
      std::string fname = d_tparser.parseSymbol(CHECK_NONE, SYM_VARIABLE);
      d_state.checkUserSymbol(fname);
      std::vector<std::pair<std::string, Sort>> sortedVarNames =
          d_tparser.parseSortedVarList();
      Sort t = d_tparser.parseSort();
      std::vector<Term> flattenVars;
      std::vector<Term> bvs;
      Term func =
          d_state.bindDefineFunRec(fname, sortedVarNames, t, flattenVars);
      d_state.pushDefineFunRecScope(sortedVarNames, func, flattenVars, bvs);
      Term expr = d_tparser.parseTerm();
      d_state.popScope();
      if (!flattenVars.empty())
      {
        expr = d_state.mkHoApply(expr, flattenVars);
      }
      cmd.reset(new DefineFunctionRecCommand(func, bvs, expr));
    }
    break;
    // (define-funs-rec (<function_dec>^{n+1}) (<term>^{n+1}))
    // where
    // <function_dec> := (<symbol> (<sorted_var>*) <sort>)
    case Token::DEFINE_FUNS_REC_TOK:
    {
      d_state.checkThatLogicIsSet();
      d_lex.eatToken(Token::LPAREN_TOK);
      std::vector<Term> funcs;
      std::vector<std::vector<std::pair<std::string, Sort>>> sortedVarNamesList;
      std::vector<std::vector<Term>> flattenVarsList;
      // while the next token is LPAREN, exit if RPAREN
      // parse <function_dec>^{n+1}
      while (d_lex.eatTokenChoice(Token::LPAREN_TOK, Token::RPAREN_TOK))
      {
        std::string fname =
            d_tparser.parseSymbol(CHECK_UNDECLARED, SYM_VARIABLE);
        d_state.checkUserSymbol(fname);
        std::vector<std::pair<std::string, Sort>> sortedVarNames =
            d_tparser.parseSortedVarList();
        Sort t = d_tparser.parseSort();
        std::vector<Term> flattenVars;
        Term func =
            d_state.bindDefineFunRec(fname, sortedVarNames, t, flattenVars);
        funcs.push_back(func);

        // add to lists (need to remember for when parsing the bodies)
        sortedVarNamesList.push_back(sortedVarNames);
        flattenVarsList.push_back(flattenVars);
        d_lex.eatToken(Token::RPAREN_TOK);
      }

      // parse the bodies
      d_lex.eatToken(Token::LPAREN_TOK);
      std::vector<Term> funcDefs;
      std::vector<std::vector<Term>> formals;
      // parse <term>^{n+1}
      for (size_t j = 0, nfuncs = funcs.size(); j < nfuncs; j++)
      {
        std::vector<Term> bvs;
        d_state.pushDefineFunRecScope(
            sortedVarNamesList[j], funcs[j], flattenVarsList[j], bvs);
        Term expr = d_tparser.parseTerm();
        d_state.popScope();
        funcDefs.push_back(expr);
        formals.push_back(bvs);
      }
      d_lex.eatToken(Token::RPAREN_TOK);
      Assert(funcs.size() == funcDefs.size());
      cmd.reset(new DefineFunctionRecCommand(funcs, formals, funcDefs));
    }
    break;
    // (define-sort <symbol> (<symbol>*) <sort>)
    case Token::DEFINE_SORT_TOK:
    {
      d_state.checkThatLogicIsSet();
      std::string name = d_tparser.parseSymbol(CHECK_UNDECLARED, SYM_SORT);
      d_state.checkUserSymbol(name);
      std::vector<std::string> snames =
          d_tparser.parseSymbolList(CHECK_UNDECLARED, SYM_SORT);
      d_state.pushScope();
      std::vector<Sort> sorts;
      for (const std::string& sname : snames)
      {
        sorts.push_back(d_state.mkSort(sname));
      }
      Sort t = d_tparser.parseSort();
      d_state.popScope();
      cmd.reset(new DefineSortCommand(name, sorts, t));
    }
    break;
    // (echo <string>)
    case Token::ECHO_TOK:
    {
      // optional string literal
      tok = d_lex.peekToken();
      if (tok == Token::STRING_LITERAL)
      {
        std::string msg = d_tparser.parseStr(true);
        cmd.reset(new EchoCommand(msg));
      }
      else
      {
        cmd.reset(new EchoCommand());
      }
    }
    break;
    // (exit)
    case Token::EXIT_TOK:
    {
      cmd.reset(new QuitCommand());
    }
    break;
    // (get-abduct <symbol> <term> <grammar>?)
    case Token::GET_ABDUCT_TOK:
    {
      d_state.checkThatLogicIsSet();
      std::string name = d_tparser.parseSymbol(CHECK_UNDECLARED, SYM_VARIABLE);
      Term t = d_tparser.parseTerm();
      // parse optional grammar
      std::vector<Term> emptyVarList;
      Grammar* g = d_tparser.parseGrammarOrNull(emptyVarList, name);
      cmd.reset(new GetAbductCommand(name, t, g));
    }
    break;
    // (get-abduct-next)
    case Token::GET_ABDUCT_NEXT_TOK:
    {
      d_state.checkThatLogicIsSet();
      cmd.reset(new GetAbductNextCommand);
    }
    break;
    // (get-assertions)
    case Token::GET_ASSERTIONS_TOK:
    {
      d_state.checkThatLogicIsSet();
      cmd.reset(new GetAssertionsCommand());
    }
    break;
    // (get-assignment)
    case Token::GET_ASSIGNMENT_TOK:
    {
      d_state.checkThatLogicIsSet();
      cmd.reset(new GetAssignmentCommand());
    }
    break;
    // (get-difficulty)
    case Token::GET_DIFFICULTY_TOK:
    {
      d_state.checkThatLogicIsSet();
      cmd.reset(new GetDifficultyCommand);
    }
    break;
    // (get-info <keyword>)
    case Token::GET_INFO_TOK:
    {
      std::string key = d_tparser.parseKeyword();
      cmd.reset(new GetInfoCommand(key));
    }
    break;
    // (get-interpolant <symbol> <term> <grammar>?)
    case Token::GET_INTERPOL_TOK:
    {
      d_state.checkThatLogicIsSet();
      std::string name = d_tparser.parseSymbol(CHECK_UNDECLARED, SYM_VARIABLE);
      Term t = d_tparser.parseTerm();
      std::vector<Term> emptyVarList;
      Grammar* g = d_tparser.parseGrammarOrNull(emptyVarList, name);
      cmd.reset(new GetInterpolantCommand(name, t, g));
    }
    break;
    // (get-interpolant-next)
    case Token::GET_INTERPOL_NEXT_TOK:
    {
      d_state.checkThatLogicIsSet();
      cmd.reset(new GetInterpolantNextCommand);
    }
    break;
    // (get-learned-literals <keyword>?)
    case Token::GET_LEARNED_LITERALS_TOK:
    {
      // optional keyword
      tok = d_lex.peekToken();
      modes::LearnedLitType llt = modes::LEARNED_LIT_INPUT;
      if (tok == Token::KEYWORD)
      {
        std::string key = d_tparser.parseKeyword();
        llt = d_state.getLearnedLitType(key);
      }
      d_state.checkThatLogicIsSet();
      cmd.reset(new GetLearnedLiteralsCommand(llt));
    }
    break;
    // (get-model)
    case Token::GET_MODEL_TOK:
    {
      d_state.checkThatLogicIsSet();
      cmd.reset(new GetModelCommand());
    }
    break;
    // (get-option <keyword>)
    case Token::GET_OPTION_TOK:
    {
      std::string key = d_tparser.parseKeyword();
      cmd.reset(new GetOptionCommand(key));
    }
    break;
    // (get-proof <keyword>?)
    case Token::GET_PROOF_TOK:
    {
      // optional keyword
      tok = d_lex.peekToken();
      modes::ProofComponent pc = modes::PROOF_COMPONENT_FULL;
      if (tok == Token::KEYWORD)
      {
        std::string key = d_tparser.parseKeyword();
        pc = d_state.getProofComponent(key);
      }
      d_state.checkThatLogicIsSet();
      cmd.reset(new GetProofCommand(pc));
    }
    break;
    // quantifier elimination commands
    // (get-qe <term>)
    // (get-qe-disjunct <term>)
    case Token::GET_QE_TOK:
    case Token::GET_QE_DISJUNCT_TOK:
    {
      d_state.checkThatLogicIsSet();
      Term t = d_tparser.parseTerm();
      bool isFull = (tok == Token::GET_QE_TOK);
      cmd.reset(new GetQuantifierEliminationCommand(t, isFull));
    }
    break;
    // (get-unsat-assumptions)
    case Token::GET_UNSAT_ASSUMPTIONS_TOK:
    {
      d_state.checkThatLogicIsSet();
      cmd.reset(new GetUnsatAssumptionsCommand);
    }
    break;
    // (get-unsat-core)
    case Token::GET_UNSAT_CORE_TOK:
    {
      d_state.checkThatLogicIsSet();
      cmd.reset(new GetUnsatCoreCommand);
    }
    break;
    // (get-value (<term>*))
    case Token::GET_VALUE_TOK:
    {
      d_state.checkThatLogicIsSet();
      // bind all symbols specific to the model, e.g. uninterpreted constant
      // values
      d_state.pushGetValueScope();
      std::vector<Term> terms = d_tparser.parseTermList();
      cmd.reset(new GetValueCommand(terms));
      d_state.popScope();
    }
    break;
    // (inv-constraint <symbol> <symbol> <symbol> <symbol>)
    case Token::INV_CONSTRAINT_TOK:
    {
      std::vector<std::string> names;
      for (size_t i = 0; i < 4; i++)
      {
        std::string name = d_tparser.parseSymbol(CHECK_NONE, SYM_VARIABLE);
        names.push_back(name);
      }
      d_state.checkThatLogicIsSet();
      cmd = d_state.invConstraint(names);
    }
    break;
    // (pop <numeral>?)
    case Token::POP_TOK:
    {
      // optional integer
      tok = d_lex.peekToken();
      if (tok == Token::INTEGER_LITERAL)
      {
        size_t num = d_tparser.parseIntegerNumeral();
        cmd = d_state.handlePop(num);
      }
      else
      {
        cmd = d_state.handlePop(std::nullopt);
      }
    }
    break;
    // (push <numeral>?)
    case Token::PUSH_TOK:
    {
      // optional integer
      tok = d_lex.peekToken();
      if (tok == Token::INTEGER_LITERAL)
      {
        size_t num = d_tparser.parseIntegerNumeral();
        cmd = d_state.handlePush(num);
      }
      else
      {
        cmd = d_state.handlePush(std::nullopt);
      }
    }
    break;
    // (reset)
    case Token::RESET_TOK:
    {
      cmd.reset(new ResetCommand());
      // reset the state of the parser, which is independent of the symbol
      // manager
      d_state.reset();
    }
    break;
    // (reset-assertions)
    case Token::RESET_ASSERTIONS_TOK:
    {
      cmd.reset(new ResetAssertionsCommand());
    }
    break;
    // (set-feature <attribute>)
    case Token::SET_FEATURE_TOK:
    {
      std::string key = d_tparser.parseKeyword();
      Term s = d_tparser.parseSymbolicExpr();
      d_state.checkThatLogicIsSet();
      // ":grammars" is defined in the SyGuS version 2.1 standard and is by
      // default supported, all other features are not.
      if (key != "grammars")
      {
        std::stringstream ss;
        ss << "SyGuS feature " << key << " not currently supported";
        d_state.warning(ss.str());
      }
      cmd.reset(new EmptyCommand());
    }
    break;
    // (set-info <attribute>)
    case Token::SET_INFO_TOK:
    {
      std::string key = d_tparser.parseKeyword();
      Term sexpr = d_tparser.parseSymbolicExpr();
      cmd.reset(new SetInfoCommand(key, sexprToString(sexpr)));
    }
    break;
    // (set-logic <symbol>)
    case Token::SET_LOGIC_TOK:
    {
      std::string name = d_tparser.parseSymbol(CHECK_NONE, SYM_SORT);
      cmd.reset(d_state.setLogic(name));
    }
    break;
    // (set-option <option>)
    case Token::SET_OPTION_TOK:
    {
      std::string key = d_tparser.parseKeyword();
      Term sexpr = d_tparser.parseSymbolicExpr();
      std::string ss = sexprToString(sexpr);
      // special case: for channel settings, we are expected to parse e.g.
      // `"stdin"` which should be treated as `stdin`
      // Note we could consider a more general solution where knowing whether
      // this special case holds can be queried via OptionInfo.
      if (key == "diagnostic-output-channel" || key == "regular-output-channel"
          || key == "in" || key == "out")
      {
        ss = d_state.stripQuotes(ss);
      }
      cmd.reset(new SetOptionCommand(key, ss));
      // Ugly that this changes the state of the parser; but
      // global-declarations affects parsing, so we can't hold off
      // on this until some SolverEngine eventually (if ever) executes it.
      if (key == "global-declarations")
      {
        d_state.getSymbolManager()->setGlobalDeclarations(ss == "true");
      }
    }
    break;
    // (simplify <term>)
    case Token::SIMPLIFY_TOK:
    {
      d_state.checkThatLogicIsSet();
      Term t = d_tparser.parseTerm();
      cmd.reset(new SimplifyCommand(t));
    }
    break;
    // (synth-fun <symbol> (<sorted_var>*) <sort> <grammar>?)
    // (synth-inv <symbol> (<sorted_var>*) <grammar>?)
    case Token::SYNTH_FUN_TOK:
    case Token::SYNTH_INV_TOK:
    {
      d_state.checkThatLogicIsSet();
      std::string name = d_tparser.parseSymbol(CHECK_UNDECLARED, SYM_VARIABLE);
      std::vector<std::pair<std::string, Sort>> sortedVarNames =
          d_tparser.parseSortedVarList();
      Sort range;
      bool isInv = (tok == Token::SYNTH_INV_TOK);
      if (isInv)
      {
        range = d_state.getSolver()->getBooleanSort();
      }
      else
      {
        range = d_tparser.parseSort();
      }
      d_state.pushScope();
      std::vector<cvc5::Term> sygusVars = d_state.bindBoundVars(sortedVarNames);
      Grammar* g = d_tparser.parseGrammarOrNull(sygusVars, name);

      Trace("parser-sygus") << "Define synth fun : " << name << std::endl;
      Solver* slv = d_state.getSolver();
      Term fun =
          isInv ? (g == nullptr ? slv->synthInv(name, sygusVars)
                                : slv->synthInv(name, sygusVars, *g))
                : (g == nullptr ? slv->synthFun(name, sygusVars, range)
                                : slv->synthFun(name, sygusVars, range, *g));

      Trace("parser-sygus") << "...read synth fun " << name << std::endl;
      d_state.popScope();
      cmd.reset(new SynthFunCommand(name, fun, sygusVars, range, isInv, g));
    }
    break;
    case Token::EOF_TOK:
      d_lex.parseError("Expected SMT-LIBv2 command", true);
      break;
    default:
      d_lex.unexpectedTokenError(tok, "Expected SMT-LIBv2 command");
      break;
  }
  d_lex.eatToken(Token::RPAREN_TOK);
  return cmd;
}

}  // namespace parser
}  // namespace cvc5
