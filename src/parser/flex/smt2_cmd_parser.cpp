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
 * Definitions of SMT2 tokens.
 */

#include "parser/flex/smt2_cmd_parser.h"

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

Command* Smt2CmdParser::parseNextCommand()
{
  std::unique_ptr<Command> cmd;
  d_lex.eatToken(Token::LPAREN_TOK);
  Token tok = d_lex.nextToken();
  switch (tok)
  {
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
    case Token::ASSUME_TOK:
    case Token::CONSTRAINT_TOK:
    {
      bool isAssume = (tok == Token::ASSUME_TOK);
      d_state.checkThatLogicIsSet();
      Term t = d_tparser.parseTerm();
      cmd.reset(new SygusConstraintCommand(t, isAssume));
    }
    break;
    case Token::BLOCK_MODEL_TOK:
    {
      const std::string& key = d_tparser.parseKeyword();
      d_state.checkThatLogicIsSet();
      modes::BlockModelsMode mode = d_state.getBlockModelsMode(key);
      cmd.reset(new BlockModelCommand(mode));
    }
    break;
    case Token::BLOCK_MODEL_VALUES_TOK:
    {
      d_state.checkThatLogicIsSet();
      std::vector<Term> terms = d_tparser.parseTermList();
      cmd.reset(new BlockModelValuesCommand(terms));
    }
    break;
    case Token::CHECK_SAT_TOK:
    {
      if (d_state.sygus())
      {
        d_state.parseError("Sygus does not support check-sat command.");
      }
      cmd.reset(new CheckSatCommand());
    }
    break;
    case Token::CHECK_SAT_ASSUMING_TOK:
    {
      d_state.checkThatLogicIsSet();
      std::vector<Term> terms = d_tparser.parseTermList();
      cmd.reset(new CheckSatAssumingCommand(terms));
    }
    break;
    case Token::CHECK_SYNTH_TOK:
    {
      d_state.checkThatLogicIsSet();
      cmd.reset(new CheckSynthCommand());
    }
    break;
    case Token::CHECK_SYNTH_NEXT_TOK:
    {
      d_state.checkThatLogicIsSet();
      cmd.reset(new CheckSynthCommand(true));
    }
    break;
    // single datatype
    case Token::DECLARE_CODATATYPE_TOK:
    case Token::DECLARE_DATATYPE_TOK:
    {
      d_state.checkThatLogicIsSet();
      std::vector<std::string> dnames;
      std::vector<size_t> arities;
      const std::string& name =
          d_tparser.parseSymbol(CHECK_UNDECLARED, SYM_SORT);
      dnames.push_back(name);
      bool isCo = (tok == Token::DECLARE_CODATATYPE_TOK);
      std::vector<DatatypeDecl> dts =
          d_tparser.parseDatatypeDef(isCo, dnames, arities);
      cmd.reset(new DatatypeDeclarationCommand(
          d_state.bindMutualDatatypeTypes(dts, true)));
    }
    break;
    // multiple datatype
    case Token::DECLARE_CODATATYPES_TOK:
    case Token::DECLARE_DATATYPES_TOK:
    {
      d_state.checkThatLogicIsSet();
      d_lex.eatToken(Token::LPAREN_TOK);
      std::vector<std::string> dnames;
      std::vector<size_t> arities;
      // TODO: optional
      while (true)
      {
        d_lex.eatToken(Token::LPAREN_TOK);
        const std::string& name =
            d_tparser.parseSymbol(CHECK_UNDECLARED, SYM_SORT);
        size_t arity = d_tparser.parseIntegerNumeral();
        dnames.push_back(name);
        arities.push_back(arity);

        d_lex.eatToken(Token::RPAREN_TOK);
      }
      d_lex.eatToken(Token::RPAREN_TOK);
      d_lex.eatToken(Token::LPAREN_TOK);

      bool isCo = (tok == Token::DECLARE_CODATATYPE_TOK);
      std::vector<DatatypeDecl> dts =
          d_tparser.parseDatatypeDef(isCo, dnames, arities);
      d_lex.eatToken(Token::RPAREN_TOK);
      cmd.reset(new DatatypeDeclarationCommand(
          d_state.bindMutualDatatypeTypes(dts, true)));
    }
    break;
    // declare-fun and declare-const
    case Token::DECLARE_CONST_TOK:
    case Token::DECLARE_FUN_TOK:
    {
      d_state.checkThatLogicIsSet();
      const std::string& name = d_tparser.parseSymbol(CHECK_NONE, SYM_VARIABLE);
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
        d_state.parseError(
            "declare-fun are not allowed in sygus "
            "version 2.0");
      }
      else
      {
        Term func = d_state.bindVar(name, t, true);
        cmd.reset(new DeclareFunctionCommand(name, func, t));
      }
    }
    break;
    case Token::DECLARE_HEAP:
    {
      d_lex.eatToken(Token::LPAREN_TOK);
      Sort t = d_tparser.parseSort();
      Sort s = d_tparser.parseSort();
      cmd.reset(new DeclareHeapCommand(t, s));
      d_lex.eatToken(Token::RPAREN_TOK);
    }
    break;
    case Token::DECLARE_POOL:
    {
      d_state.checkThatLogicIsSet();
      const std::string& name = d_tparser.parseSymbol(CHECK_NONE, SYM_VARIABLE);
      d_state.checkUserSymbol(name);
      Sort t = d_tparser.parseSort();
      std::vector<Term> terms = d_tparser.parseTermList();
      Trace("parser") << "declare pool: '" << name << "'" << std::endl;
      Term pool = d_state.getSolver()->declarePool(name, t, terms);
      d_state.defineVar(name, pool);
      cmd.reset(new DeclarePoolCommand(name, pool, t, terms));
    }
    break;
    case Token::DECLARE_SORT_TOK:
    {
      d_state.checkThatLogicIsSet();
      d_state.checkLogicAllowsFreeSorts();
      const std::string& name =
          d_tparser.parseSymbol(CHECK_UNDECLARED, SYM_SORT);
      d_state.checkUserSymbol(name);
      size_t arity = d_tparser.parseIntegerNumeral();
      Trace("parser") << "declare sort: '" << name << "' arity=" << arity
                      << std::endl;
      if (arity == 0)
      {
        Sort type = d_state.mkSort(name);
        cmd.reset(new DeclareSortCommand(name, 0, type));
      }
      else
      {
        Sort type = d_state.mkSortConstructor(name, arity);
        cmd.reset(new DeclareSortCommand(name, arity, type));
      }
    }
    break;
    case Token::DECLARE_VAR_TOK:
    {
      d_state.checkThatLogicIsSet();
      const std::string& name =
          d_tparser.parseSymbol(CHECK_UNDECLARED, SYM_VARIABLE);
      d_state.checkUserSymbol(name);
      Sort t = d_tparser.parseSort();
      Term var = d_state.getSolver()->declareSygusVar(name, t);
      d_state.defineVar(name, var);
      cmd.reset(new DeclareSygusVarCommand(name, var, t));
    }
    break;
    case Token::DEFINE_CONST_TOK:
    {
      d_state.checkThatLogicIsSet();
      const std::string& name =
          d_tparser.parseSymbol(CHECK_UNDECLARED, SYM_VARIABLE);
      d_state.checkUserSymbol(name);
      Sort t = d_tparser.parseSort();
      Term e = d_tparser.parseTerm();

      // declare the name down here (while parsing term, signature
      // must not be extended with the name itself; no recursion
      // permitted)
      cmd.reset(new DefineFunctionCommand(name, t, e));
    }
    break;
    case Token::DEFINE_FUN_TOK: break;
    case Token::DEFINE_FUN_REC_TOK: break;
    case Token::DEFINE_FUNS_REC_TOK: break;
    case Token::DEFINE_SORT_TOK: break;
    case Token::ECHO_TOK: break;
    case Token::EXIT_TOK:
    {
      cmd.reset(new QuitCommand());
    }
    break;
    case Token::GET_ABDUCT_TOK:
    {
      d_state.checkThatLogicIsSet();
      const std::string& name =
          d_tparser.parseSymbol(CHECK_UNDECLARED, SYM_VARIABLE);
      Term t = d_tparser.parseTerm();
      // TODO: optional
      std::vector<Term> emptyVarList;
      Grammar* g = d_tparser.parseGrammar(emptyVarList, name);
      cmd.reset(new GetAbductCommand(name, t, g));
    }
    break;
    case Token::GET_ABDUCT_NEXT_TOK:
    {
      d_state.checkThatLogicIsSet();
      cmd.reset(new GetAbductNextCommand);
    }
    break;
    case Token::GET_ASSERTIONS_TOK:
    {
      d_state.checkThatLogicIsSet();
      cmd.reset(new GetAssertionsCommand());
    }
    break;
    case Token::GET_ASSIGNMENT_TOK:
    {
      d_state.checkThatLogicIsSet();
      cmd.reset(new GetAssignmentCommand());
    }
    break;
    case Token::GET_DIFFICULTY_TOK:
    {
      d_state.checkThatLogicIsSet();
      cmd.reset(new GetDifficultyCommand);
    }
    break;
    case Token::GET_INFO_TOK:
    {
      const std::string& key = d_tparser.parseKeyword();
      cmd.reset(new GetInfoCommand(key));
    }
    break;
    case Token::GET_INTERPOL_TOK:
    {
      d_state.checkThatLogicIsSet();
      const std::string& name =
          d_tparser.parseSymbol(CHECK_UNDECLARED, SYM_VARIABLE);
      Term t = d_tparser.parseTerm();
      // TODO: optional
      std::vector<Term> emptyVarList;
      Grammar* g = d_tparser.parseGrammar(emptyVarList, name);
      cmd.reset(new GetInterpolantCommand(name, t, g));
    }
    break;
    case Token::GET_INTERPOL_NEXT_TOK:
    {
      d_state.checkThatLogicIsSet();
      cmd.reset(new GetInterpolantNextCommand);
    }
    break;
    case Token::GET_LEARNED_LITERALS_TOK:
    {
      // TODO: optional
      bool readKeyword = true;
      const std::string& key = d_tparser.parseKeyword();
      d_state.checkThatLogicIsSet();
      modes::LearnedLitType llt = modes::LEARNED_LIT_INPUT;
      if (readKeyword)
      {
        llt = d_state.getLearnedLitType(key);
      }
      cmd.reset(new GetLearnedLiteralsCommand(llt));
    }
    break;
    case Token::GET_MODEL_TOK:
    {
      d_state.checkThatLogicIsSet();
      cmd.reset(new GetModelCommand());
    }
    break;
    case Token::GET_OPTION_TOK:
    {
      const std::string& key = d_tparser.parseKeyword();
      cmd.reset(new GetOptionCommand(key));
    }
    break;
    case Token::GET_PROOF_TOK:
    {
      // TODO: optional
      bool readKeyword = true;
      const std::string& key = d_tparser.parseKeyword();
      d_state.checkThatLogicIsSet();
      modes::ProofComponent pc = modes::PROOF_COMPONENT_FULL;
      if (readKeyword)
      {
        pc = d_state.getProofComponent(key);
      }
      cmd.reset(new GetProofCommand(pc));
    }
    break;
    // quantifier elimination commands
    case Token::GET_QE_TOK:
    case Token::GET_QE_DISJUNCT_TOK:
    {
      d_state.checkThatLogicIsSet();
      Term t = d_tparser.parseTerm();
      bool isFull = (tok == Token::GET_QE_TOK);
      cmd.reset(new GetQuantifierEliminationCommand(t, isFull));
    }
    break;
    case Token::GET_UNSAT_ASSUMPTIONS_TOK:
    {
      d_state.checkThatLogicIsSet();
      cmd.reset(new GetUnsatAssumptionsCommand);
    }
    break;
    case Token::GET_UNSAT_CORE_TOK:
    {
      d_state.checkThatLogicIsSet();
      cmd.reset(new GetUnsatCoreCommand);
    }
    break;
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
    case Token::INV_CONSTRAINT_TOK:
    {
      std::vector<std::string> names;
      for (size_t i = 0; i < 4; i++)
      {
        const std::string& name =
            d_tparser.parseSymbol(CHECK_NONE, SYM_VARIABLE);
        names.push_back(name);
      }
      d_state.checkThatLogicIsSet();
      cmd = d_state.invConstraint(names);
    }
    break;
    case Token::POP_TOK:
    {
      // TODO: optional
      bool readNumeral = true;
      size_t num = d_tparser.parseIntegerNumeral();
      if (readNumeral)
      {
        cmd = d_state.handlePop(num);
      }
      else
      {
        cmd = d_state.handlePop(std::nullopt);
      }
    }
    break;
    case Token::PUSH_TOK:
    {
      // TODO: optional
      bool readNumeral = true;
      size_t num = d_tparser.parseIntegerNumeral();
      if (readNumeral)
      {
        cmd = d_state.handlePush(num);
      }
      else
      {
        cmd = d_state.handlePush(std::nullopt);
      }
    }
    break;
    case Token::RESET_TOK:
    {
      cmd.reset(new ResetCommand());
      // reset the state of the parser, which is independent of the symbol
      // manager
      d_state.reset();
    }
    break;
    case Token::RESET_ASSERTIONS_TOK:
    {
      cmd.reset(new ResetAssertionsCommand());
    }
    break;
    case Token::SET_FEATURE_TOK:
    {
      const std::string& key = d_tparser.parseKeyword();
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
    case Token::SET_INFO_TOK:
    {
      const std::string& key = d_tparser.parseKeyword();
      Term sexpr = d_tparser.parseSymbolicExpr();
      cmd.reset(new SetInfoCommand(key, sexprToString(sexpr)));
    }
    break;
    case Token::SET_LOGIC_TOK:
    {
      const std::string& name = d_tparser.parseSymbol(CHECK_NONE, SYM_SORT);
      cmd.reset(d_state.setLogic(name));
    }
    break;
    case Token::SET_OPTION_TOK:
    {
      const std::string& key = d_tparser.parseKeyword();
      Term sexpr = d_tparser.parseSymbolicExpr();
      std::string ss = sexprToString(sexpr);
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
    case Token::SIMPLIFY_TOK:
    {
      d_state.checkThatLogicIsSet();
      Term t = d_tparser.parseTerm();
      cmd.reset(new SimplifyCommand(t));
    }
    break;
    case Token::SYNTH_FUN_TOK:
    case Token::SYNTH_INV_TOK:
    {
    d_state.checkThatLogicIsSet();
      const std::string& name = d_tparser.parseSymbol(CHECK_UNDECLARED, SYM_VARIABLE);
      std::vector<std::pair<std::string, Sort> > sortedVarNames = d_tparser.parseSortedVarList();
      Sort range;
      bool isInv = (tok ==Token::SYNTH_INV_TOK);
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
      // TODO: optional
      Grammar* g = d_tparser.parseGrammar(sygusVars, name);
    
      Trace("parser-sygus") << "Define synth fun : " << name << std::endl;
      Solver * slv = d_state.getSolver();
      Term fun = isInv ? (g == nullptr
                         ? slv->synthInv(name, sygusVars)
                         : slv->synthInv(name, sygusVars, *g))
                  : (g == nullptr
                         ? slv->synthFun(name, sygusVars, range)
                         : slv->synthFun(name, sygusVars, range, *g));

      Trace("parser-sygus") << "...read synth fun " << name << std::endl;
      d_state.popScope();
      // we do not allow overloading for synth fun
      d_state.defineVar(name, fun);
      cmd.reset(
          new SynthFunCommand(name, fun, sygusVars, range, isInv, g));
    }
    break;
    default:
      // TODO: error
      break;
  }
  d_lex.eatToken(Token::RPAREN_TOK);
  return cmd.release();
}

}  // namespace parser
}  // namespace cvc5
