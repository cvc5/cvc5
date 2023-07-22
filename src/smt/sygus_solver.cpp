/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The solver for SyGuS queries.
 */

#include "smt/sygus_solver.h"

#include <sstream>

#include "base/modal_exception.h"
#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "expr/skolem_manager.h"
#include "options/base_options.h"
#include "options/option_exception.h"
#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "smt/preprocessor.h"
#include "smt/smt_driver.h"
#include "smt/smt_solver.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/sygus/sygus_utils.h"
#include "theory/quantifiers_engine.h"
#include "theory/rewriter.h"
#include "theory/smt_engine_subsolver.h"

using namespace cvc5::internal::theory;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace smt {

SygusSolver::SygusSolver(Env& env, SmtSolver& sms)
    : EnvObj(env),
      d_smtSolver(sms),
      d_sygusVars(userContext()),
      d_sygusConstraints(userContext()),
      d_sygusAssumps(userContext()),
      d_sygusFunSymbols(userContext()),
      d_sygusConjectureStale(userContext(), true),
      d_subsolverCd(userContext(), nullptr)
{
}

SygusSolver::~SygusSolver() {}

void SygusSolver::declareSygusVar(Node var)
{
  Trace("smt") << "SygusSolver::declareSygusVar: " << var << " "
               << var.getType() << "\n";
  d_sygusVars.push_back(var);
  // don't need to set that the conjecture is stale
}

void SygusSolver::declareSynthFun(Node fn,
                                  TypeNode sygusType,
                                  bool isInv,
                                  const std::vector<Node>& vars)
{
  Trace("smt") << "SygusSolver::declareSynthFun: " << fn << "\n";
  NodeManager* nm = NodeManager::currentNM();
  d_sygusFunSymbols.push_back(fn);
  if (!vars.empty())
  {
    Node bvl = nm->mkNode(BOUND_VAR_LIST, vars);
    // use an attribute to mark its bound variable list
    quantifiers::SygusUtils::setSygusArgumentList(fn, bvl);
  }
  // whether sygus type encodes syntax restrictions
  if (!sygusType.isNull() && sygusType.isDatatype()
      && sygusType.getDType().isSygus())
  {
    // use an attribute to mark its grammar
    quantifiers::SygusUtils::setSygusType(fn, sygusType);
    // we must expand definitions for sygus operators in the block
    expandDefinitionsSygusDt(sygusType);
  }

  // sygus conjecture is now stale
  d_sygusConjectureStale = true;
}

void SygusSolver::assertSygusConstraint(Node n, bool isAssume)
{
  Trace("smt") << "SygusSolver::assertSygusConstrant: " << n
               << ", isAssume=" << isAssume << "\n";
  if (isAssume)
  {
    d_sygusAssumps.push_back(n);
  }
  else
  {
    d_sygusConstraints.push_back(n);
  }

  // sygus conjecture is now stale
  d_sygusConjectureStale = true;
}

std::vector<Node> SygusSolver::getSygusConstraints() const
{
  return listToVector(d_sygusConstraints);
}

std::vector<Node> SygusSolver::getSygusAssumptions() const
{
  return listToVector(d_sygusAssumps);
}

void SygusSolver::assertSygusInvConstraint(Node inv,
                                           Node pre,
                                           Node trans,
                                           Node post)
{
  Trace("smt") << "SygusSolver::assertSygusInvConstrant: " << inv << " " << pre
               << " " << trans << " " << post << "\n";
  // build invariant constraint

  // get variables (regular and their respective primed versions)
  std::vector<Node> terms;
  std::vector<Node> vars;
  std::vector<Node> primed_vars;
  terms.push_back(inv);
  terms.push_back(pre);
  terms.push_back(trans);
  terms.push_back(post);
  // variables are built based on the invariant type
  NodeManager* nm = NodeManager::currentNM();
  std::vector<TypeNode> argTypes = inv.getType().getArgTypes();
  for (const TypeNode& tn : argTypes)
  {
    vars.push_back(nm->mkBoundVar(tn));
    d_sygusVars.push_back(vars.back());
    std::stringstream ss;
    ss << vars.back() << "'";
    primed_vars.push_back(nm->mkBoundVar(ss.str(), tn));
    d_sygusVars.push_back(primed_vars.back());
  }

  // make relevant terms; 0 -> Inv, 1 -> Pre, 2 -> Trans, 3 -> Post
  for (unsigned i = 0; i < 4; ++i)
  {
    Node op = terms[i];
    Trace("smt-debug") << "Make inv-constraint term #" << i << " : " << op
                       << " with type " << op.getType() << "...\n";
    std::vector<Node> children;
    children.push_back(op);
    // transition relation applied over both variable lists
    if (i == 2)
    {
      children.insert(children.end(), vars.begin(), vars.end());
      children.insert(children.end(), primed_vars.begin(), primed_vars.end());
    }
    else
    {
      children.insert(children.end(), vars.begin(), vars.end());
    }
    terms[i] = nm->mkNode(APPLY_UF, children);
    // make application of Inv on primed variables
    if (i == 0)
    {
      children.clear();
      children.push_back(op);
      children.insert(children.end(), primed_vars.begin(), primed_vars.end());
      terms.push_back(nm->mkNode(APPLY_UF, children));
    }
  }
  // make constraints
  std::vector<Node> conj;
  conj.push_back(nm->mkNode(IMPLIES, terms[1], terms[0]));
  Node term0_and_2 = nm->mkNode(AND, terms[0], terms[2]);
  conj.push_back(nm->mkNode(IMPLIES, term0_and_2, terms[4]));
  conj.push_back(nm->mkNode(IMPLIES, terms[0], terms[3]));
  Node constraint = nm->mkNode(AND, conj);

  d_sygusConstraints.push_back(constraint);

  // sygus conjecture is now stale
  d_sygusConjectureStale = true;
}

SynthResult SygusSolver::checkSynth(bool isNext)
{
  Trace("smt") << "SygusSolver::checkSynth" << std::endl;
  // if applicable, check if the subsolver is the correct one
  if (!isNext)
  {
    // if we are not using check-synth-next, we always reconstruct the solver.
    d_sygusConjectureStale = true;
  }
  if (usingSygusSubsolver() && d_subsolverCd.get() != d_subsolver.get())
  {
    // this can occur if we backtrack to a place where we were using a different
    // subsolver than the current one. In this case, we should reconstruct
    // the subsolver.
    d_sygusConjectureStale = true;
  }
  if (d_sygusConjectureStale)
  {
    NodeManager* nm = NodeManager::currentNM();
    // build synthesis conjecture from asserted constraints and declared
    // variables/functions
    Trace("smt") << "Sygus : Constructing sygus constraint...\n";
    Node body = nm->mkAnd(listToVector(d_sygusConstraints));
    // note that if there are no constraints, then assumptions are irrelevant
    if (!d_sygusConstraints.empty() && !d_sygusAssumps.empty())
    {
      Node bodyAssump = nm->mkAnd(listToVector(d_sygusAssumps));
      body = nm->mkNode(IMPLIES, bodyAssump, body);
    }
    body = body.notNode();
    Trace("smt") << "...constructed sygus constraint " << body << std::endl;
    if (!d_sygusVars.empty())
    {
      Node boundVars = nm->mkNode(BOUND_VAR_LIST, listToVector(d_sygusVars));
      body = nm->mkNode(EXISTS, boundVars, body);
      Trace("smt") << "...constructed exists " << body << std::endl;
    }
    if (!d_sygusFunSymbols.empty())
    {
      body = quantifiers::SygusUtils::mkSygusConjecture(
          listToVector(d_sygusFunSymbols), body);
    }
    Trace("smt") << "...constructed forall " << body << std::endl;

    Trace("smt") << "Check synthesis conjecture: " << body << std::endl;

    d_sygusConjectureStale = false;

    d_conj = body;

    // if we are using a subsolver, initialize it now
    if (usingSygusSubsolver())
    {
      // we generate a new solver engine to do the SyGuS query
      Assertions& as = d_smtSolver.getAssertions();
      initializeSygusSubsolver(d_subsolver, as);

      // store the pointer (context-dependent)
      d_subsolverCd = d_subsolver.get();

      // also assert the internal SyGuS conjecture
      d_subsolver->assertFormula(d_conj);
    }
  }
  else
  {
    Assert(d_subsolver != nullptr);
  }
  Result r;
  if (usingSygusSubsolver())
  {
    r = d_subsolver->checkSat();
  }
  else
  {
    std::vector<Node> query;
    query.push_back(d_conj);
    // use a single call driver
    SmtDriverSingleCall sdsc(d_env, d_smtSolver);
    r = sdsc.checkSat(query);
  }
  // The result returned by the above call is typically "unknown", which may
  // or may not correspond to a state in which we solved the conjecture
  // successfully. Instead we call getSynthSolutions below. If this returns
  // true, then we were successful. In this case, we set the synthesis result to
  // "solution".
  //
  // This behavior is done for 2 reasons:
  // (1) if we do not negate the synthesis conjecture, the subsolver in some
  // cases cannot answer "sat", e.g. in the presence of recursive function
  // definitions. Instead the SyGuS language standard itself indicates that
  // a correct solution for a conjecture is one where the synthesis conjecture
  // is *T-valid* (in the presence of defined recursive functions). In other
  // words, a SyGuS query asks to prove that the conjecture is valid when
  // witnessed by the given solution.
  // (2) we do not want the solver to explicitly answer "unsat" by giving an
  // unsatisfiable set of formulas to the underlying PropEngine, or otherwise
  // we will not be able to ask for further solutions. This is critical for
  // incremental solving where multiple solutions are returned for the same
  // set of constraints. Thus, the internal SyGuS solver will mark unknown
  // with IncompleteId::QUANTIFIERS_SYGUS_SOLVED. Furthermore, this id may be
  // overwritten by other means of incompleteness, so we cannot rely on this
  // identifier being the final reason for unknown.
  //
  // Thus, we use getSynthSolutions as means of knowing the conjecture was
  // solved.
  SynthResult sr;
  std::map<Node, Node> sol_map;
  if (getSynthSolutions(sol_map))
  {
    // if we have solutions, we return "solution"
    sr = SynthResult(SynthResult::SOLUTION);
    // Check that synthesis solutions satisfy the conjecture
    if (options().smt.checkSynthSol)
    {
      Assertions& as = d_smtSolver.getAssertions();
      checkSynthSolution(as, sol_map);
    }
  }
  else if (r.getStatus() == Result::UNSAT)
  {
    // unsat means no solution
    sr = SynthResult(SynthResult::NO_SOLUTION);
  }
  else
  {
    // otherwise, we return "unknown"
    sr = SynthResult(SynthResult::UNKNOWN, UnknownExplanation::UNKNOWN_REASON);
  }
  return sr;
}

bool SygusSolver::getSynthSolutions(std::map<Node, Node>& solMap)
{
  Trace("smt") << "SygusSolver::getSynthSolutions" << std::endl;
  if (usingSygusSubsolver())
  {
    // use the call to get the synth solutions from the subsolver
    return d_subsolver ? d_subsolver->getSubsolverSynthSolutions(solMap)
                       : false;
  }
  return getSubsolverSynthSolutions(solMap);
}

bool SygusSolver::getSubsolverSynthSolutions(std::map<Node, Node>& solMap)
{
  Trace("smt") << "SygusSolver::getSubsolverSynthSolutions" << std::endl;
  std::map<Node, std::map<Node, Node>> solMapn;
  // fail if the theory engine does not have synthesis solutions
  QuantifiersEngine* qe = d_smtSolver.getQuantifiersEngine();
  if (qe == nullptr || !qe->getSynthSolutions(solMapn))
  {
    return false;
  }
  for (std::pair<const Node, std::map<Node, Node>>& cs : solMapn)
  {
    for (std::pair<const Node, Node>& s : cs.second)
    {
      solMap[s.first] = s.second;
    }
  }
  return true;
}

bool SygusSolver::canTrustSynthesisResult(const Options& opts)
{
  if (opts.quantifiers.cegisSample == options::CegisSampleMode::TRUST)
  {
    return false;
  }
  return true;
}

void SygusSolver::checkSynthSolution(Assertions& as,
                                     const std::map<Node, Node>& sol_map)
{
  if (isVerboseOn(1))
  {
    verbose(1) << "SyGuS::checkSynthSolution: checking synthesis solution"
               << std::endl;
  }
  bool canTrustResult = canTrustSynthesisResult(options());
  if (!canTrustResult)
  {
    warning() << "Running check-synth-sol is not guaranteed to pass with the "
                 "current options."
              << std::endl;
  }
  if (sol_map.empty())
  {
    InternalError() << "SygusSolver::checkSynthSolution(): Got empty solution!";
    return;
  }
  Trace("check-synth-sol") << "Got solution map:\n";
  // the set of synthesis conjectures in our assertions
  std::unordered_set<Node> conjs;
  conjs.insert(d_conj);
  // For each of the above conjectures, the functions-to-synthesis and their
  // solutions. This is used as a substitution below.
  std::vector<Node> fvars;
  std::vector<Node> fsols;
  for (const std::pair<const Node, Node>& pair : sol_map)
  {
    Trace("check-synth-sol")
        << "  " << pair.first << " --> " << pair.second << "\n";
    fvars.push_back(pair.first);
    fsols.push_back(pair.second);
  }

  Trace("check-synth-sol") << "Starting new SMT Engine\n";

  Trace("check-synth-sol") << "Retrieving assertions\n";
  // Build conjecture from original assertions
  // check all conjectures
  for (const Node& conj : conjs)
  {
    // Start new SMT engine to check solutions
    std::unique_ptr<SolverEngine> solChecker;
    initializeSygusSubsolver(solChecker, as);
    solChecker->getOptions().writeSmt().checkSynthSol = false;
    solChecker->getOptions().writeQuantifiers().sygusRecFun = false;
    Assert(conj.getKind() == FORALL);
    Node conjBody = conj[1];
    // we must apply substitutions here, since define-fun may contain the
    // function-to-synthesize, which needs to be substituted.
    conjBody = d_smtSolver.getPreprocessor()->applySubstitutions(conjBody);
    // Apply solution map to conjecture body
    conjBody = conjBody.substitute(
        fvars.begin(), fvars.end(), fsols.begin(), fsols.end());

    if (isVerboseOn(1))
    {
      verbose(1) << "SyGuS::checkSynthSolution: -- body substitutes to "
                 << conjBody << std::endl;
    }
    Trace("check-synth-sol")
        << "Substituted body of assertion to " << conjBody << "\n";
    solChecker->assertFormula(conjBody);
    Result r = solChecker->checkSat();
    if (isVerboseOn(1))
    {
      verbose(1) << "SyGuS::checkSynthSolution: result is " << r << std::endl;
    }
    Trace("check-synth-sol") << "Satsifiability check: " << r << "\n";
    if (r.getStatus() == Result::UNSAT)
    {
      continue;
    }
    std::stringstream ss;
    bool hardFailure = canTrustResult;
    if (r.getStatus() == Result::SAT)
    {
      ss << "SygusSolver::checkSynthSolution(): produced solution leads to "
            "satisfiable negated conjecture.";
    }
    else
    {
      hardFailure = false;
      ss << "SygusSolver::checkSynthSolution(): could not check "
            "solution, result unknown.";
    }
    if (hardFailure)
    {
      InternalError() << ss.str();
    }
    else
    {
      warning() << ss.str() << std::endl;
    }
  }
}

void SygusSolver::initializeSygusSubsolver(std::unique_ptr<SolverEngine>& se,
                                           Assertions& as)
{
  initializeSubsolver(se, d_env);
  std::unordered_set<Node> processed;
  // if we did not spawn a subsolver for the main check, the overall SyGuS
  // conjecture has been added as an assertion. Do not add it here, which
  // is important for check-synth-sol. Adding this also has no impact
  // when spawning a subsolver for the main check.
  processed.insert(d_conj);
  // carry the ordinary define-fun definitions
  const context::CDList<Node>& alistDefs = as.getAssertionListDefinitions();
  for (const Node& def : alistDefs)
  {
    // only consider define-fun, represented as (= f (lambda ...)).
    if (def.getKind() == EQUAL)
    {
      Assert(def[0].isVar());
      std::vector<Node> formals;
      Node dbody = def[1];
      if (def[1].getKind() == LAMBDA)
      {
        formals.insert(formals.end(), def[1][0].begin(), def[1][0].end());
        dbody = dbody[1];
      }
      se->defineFunction(def[0], formals, dbody);
      processed.insert(def);
    }
  }
  // Also assert auxiliary assertions, which typically correspond to
  // quantified formulas for define-fun-rec only.
  const context::CDList<Node>& alist = as.getAssertionList();
  for (size_t i = 0, asize = alist.size(); i < asize; ++i)
  {
    Node a = alist[i];
    // ignore definitions here
    if (processed.find(a) == processed.end())
    {
      se->assertFormula(a);
    }
  }
}

bool SygusSolver::usingSygusSubsolver() const
{
  // use SyGuS subsolver if in incremental mode
  return options().base.incrementalSolving;
}

void SygusSolver::expandDefinitionsSygusDt(TypeNode tn) const
{
  std::unordered_set<TypeNode> processed;
  std::vector<TypeNode> toProcess;
  toProcess.push_back(tn);
  size_t index = 0;
  while (index < toProcess.size())
  {
    TypeNode tnp = toProcess[index];
    index++;
    Assert(tnp.isDatatype());
    Assert(tnp.getDType().isSygus());
    const std::vector<std::shared_ptr<DTypeConstructor>>& cons =
        tnp.getDType().getConstructors();
    for (const std::shared_ptr<DTypeConstructor>& c : cons)
    {
      Node op = c->getSygusOp();
      // Only expand definitions if the operator is not constant, since
      // calling expandDefinitions on them should be a no-op. This check
      // ensures we don't try to expand e.g. bitvector extract operators,
      // whose type is undefined, and thus should not be passed to
      // expandDefinitions.
      Node eop = op.isConst()
                     ? op
                     : d_smtSolver.getPreprocessor()->applySubstitutions(op);
      eop = rewrite(eop);
      datatypes::utils::setExpandedDefinitionForm(op, eop);
      // also must consider the arguments
      for (unsigned j = 0, nargs = c->getNumArgs(); j < nargs; ++j)
      {
        TypeNode tnc = c->getArgType(j);
        if (tnc.isDatatype() && tnc.getDType().isSygus()
            && processed.find(tnc) == processed.end())
        {
          toProcess.push_back(tnc);
          processed.insert(tnc);
        }
      }
    }
  }
}

std::vector<Node> SygusSolver::listToVector(const NodeList& list)
{
  std::vector<Node> vec;
  for (const Node& n : list)
  {
    vec.push_back(n);
  }
  return vec;
}

std::vector<std::pair<Node, TypeNode>> SygusSolver::getSynthFunctions() const
{
  std::vector<std::pair<Node, TypeNode>> funs;
  for (const Node& f : d_sygusFunSymbols)
  {
    TypeNode st = quantifiers::SygusUtils::getSygusType(f);
    funs.emplace_back(f, st);
  }
  return funs;
}

}  // namespace smt
}  // namespace cvc5::internal
