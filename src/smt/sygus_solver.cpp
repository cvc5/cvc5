/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Abdalrhman Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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
#include "smt/smt_solver.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/sygus/sygus_grammar_cons.h"
#include "theory/quantifiers/sygus/sygus_utils.h"
#include "theory/quantifiers_engine.h"
#include "theory/rewriter.h"
#include "theory/smt_engine_subsolver.h"

using namespace cvc5::theory;
using namespace cvc5::kind;

namespace cvc5 {
namespace smt {

SygusSolver::SygusSolver(Env& env, SmtSolver& sms)
    : EnvObj(env), d_smtSolver(sms), d_sygusConjectureStale(userContext(), true)
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
    SygusSynthFunVarListAttribute ssfvla;
    fn.setAttribute(ssfvla, bvl);
  }
  // whether sygus type encodes syntax restrictions
  if (!sygusType.isNull() && sygusType.isDatatype()
      && sygusType.getDType().isSygus())
  {
    Node sym = nm->mkBoundVar("sfproxy", sygusType);
    // use an attribute to mark its grammar
    SygusSynthGrammarAttribute ssfga;
    fn.setAttribute(ssfga, sym);
    // we must expand definitions for sygus operators in the block
    expandDefinitionsSygusDt(sygusType);
  }

  // sygus conjecture is now stale
  setSygusConjectureStale();
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
  setSygusConjectureStale();
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
  setSygusConjectureStale();
}

Result SygusSolver::checkSynth(Assertions& as)
{
  if (options().base.incrementalSolving)
  {
    // TODO (project #7)
    throw ModalException(
        "Cannot make check-synth commands when incremental solving is enabled");
  }
  Trace("smt") << "SygusSolver::checkSynth" << std::endl;
  std::vector<Node> query;
  if (d_sygusConjectureStale)
  {
    NodeManager* nm = NodeManager::currentNM();
    // build synthesis conjecture from asserted constraints and declared
    // variables/functions
    Trace("smt") << "Sygus : Constructing sygus constraint...\n";
    Node body = nm->mkAnd(d_sygusConstraints);
    // note that if there are no constraints, then assumptions are irrelevant
    if (!d_sygusConstraints.empty() && !d_sygusAssumps.empty())
    {
      Node bodyAssump = nm->mkAnd(d_sygusAssumps);
      body = nm->mkNode(IMPLIES, bodyAssump, body);
    }
    body = body.notNode();
    Trace("smt") << "...constructed sygus constraint " << body << std::endl;
    if (!d_sygusVars.empty())
    {
      Node boundVars = nm->mkNode(BOUND_VAR_LIST, d_sygusVars);
      body = nm->mkNode(EXISTS, boundVars, body);
      Trace("smt") << "...constructed exists " << body << std::endl;
    }
    if (!d_sygusFunSymbols.empty())
    {
      body =
          quantifiers::SygusUtils::mkSygusConjecture(d_sygusFunSymbols, body);
    }
    Trace("smt") << "...constructed forall " << body << std::endl;

    Trace("smt") << "Check synthesis conjecture: " << body << std::endl;

    d_sygusConjectureStale = false;

    // TODO (project #7): if incremental, we should push a context and assert
    query.push_back(body);
  }

  Result r = d_smtSolver.checkSatisfiability(as, query, false);

  // Check that synthesis solutions satisfy the conjecture
  if (options().smt.checkSynthSol
      && r.asSatisfiabilityResult().isSat() == Result::UNSAT)
  {
    checkSynthSolution(as);
  }
  return r;
}

bool SygusSolver::getSynthSolutions(std::map<Node, Node>& sol_map)
{
  Trace("smt") << "SygusSolver::getSynthSolutions" << std::endl;
  std::map<Node, std::map<Node, Node>> sol_mapn;
  // fail if the theory engine does not have synthesis solutions
  QuantifiersEngine* qe = d_smtSolver.getQuantifiersEngine();
  if (qe == nullptr || !qe->getSynthSolutions(sol_mapn))
  {
    return false;
  }
  for (std::pair<const Node, std::map<Node, Node>>& cs : sol_mapn)
  {
    for (std::pair<const Node, Node>& s : cs.second)
    {
      sol_map[s.first] = s.second;
    }
  }
  return true;
}

void SygusSolver::checkSynthSolution(Assertions& as)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  if (isVerboseOn(1))
  {
    verbose(1) << "SyGuS::checkSynthSolution: checking synthesis solution"
               << std::endl;
  }
  std::map<Node, std::map<Node, Node>> sol_map;
  // Get solutions and build auxiliary vectors for substituting
  QuantifiersEngine* qe = d_smtSolver.getQuantifiersEngine();
  if (qe == nullptr || !qe->getSynthSolutions(sol_map))
  {
    InternalError()
        << "SygusSolver::checkSynthSolution(): No solution to check!";
    return;
  }
  if (sol_map.empty())
  {
    InternalError() << "SygusSolver::checkSynthSolution(): Got empty solution!";
    return;
  }
  Trace("check-synth-sol") << "Got solution map:\n";
  // the set of synthesis conjectures in our assertions
  std::unordered_set<Node> conjs;
  // For each of the above conjectures, the functions-to-synthesis and their
  // solutions. This is used as a substitution below.
  std::map<Node, std::vector<Node>> fvarMap;
  std::map<Node, std::vector<Node>> fsolMap;
  for (const std::pair<const Node, std::map<Node, Node>>& cmap : sol_map)
  {
    Trace("check-synth-sol") << "For conjecture " << cmap.first << ":\n";
    conjs.insert(cmap.first);
    std::vector<Node>& fvars = fvarMap[cmap.first];
    std::vector<Node>& fsols = fsolMap[cmap.first];
    for (const std::pair<const Node, Node>& pair : cmap.second)
    {
      Trace("check-synth-sol")
          << "  " << pair.first << " --> " << pair.second << "\n";
      fvars.push_back(pair.first);
      fsols.push_back(pair.second);
    }
  }
  Trace("check-synth-sol") << "Starting new SMT Engine\n";

  Trace("check-synth-sol") << "Retrieving assertions\n";
  // Build conjecture from original assertions
  const context::CDList<Node>& alist = as.getAssertionList();
  Assert(options().smt.produceAssertions)
      << "Expected produce assertions to be true when checking synthesis "
         "solution";
  // auxiliary assertions
  std::vector<Node> auxAssertions;
  // expand definitions cache
  std::unordered_map<Node, Node> cache;
  for (const Node& assertion : alist)
  {
    if (isVerboseOn(1))
    {
      verbose(1) << "SyGuS::checkSynthSolution: checking assertion "
                 << assertion << std::endl;
    }
    Trace("check-synth-sol") << "Retrieving assertion " << assertion << "\n";
    // Apply any define-funs from the problem.
    Node n = d_smtSolver.getPreprocessor()->expandDefinitions(assertion, cache);
    if (isVerboseOn(1))
    {
      verbose(1) << "SyGuS::checkSynthSolution: -- expands to " << n
                 << std::endl;
    }
    Trace("check-synth-sol") << "Expanded assertion " << n << "\n";
    if (conjs.find(n) == conjs.end())
    {
      Trace("check-synth-sol") << "It is an auxiliary assertion\n";
      auxAssertions.push_back(n);
    }
    else
    {
      Trace("check-synth-sol") << "It is a synthesis conjecture\n";
    }
  }
  // check all conjectures
  for (Node conj : conjs)
  {
    // Start new SMT engine to check solutions
    std::unique_ptr<SolverEngine> solChecker;
    initializeSubsolver(solChecker, d_env);
    solChecker->getOptions().smt.checkSynthSol = false;
    solChecker->getOptions().quantifiers.sygusRecFun = false;
    // get the solution for this conjecture
    std::vector<Node>& fvars = fvarMap[conj];
    std::vector<Node>& fsols = fsolMap[conj];
    // Apply solution map to conjecture body
    Node conjBody;
    /* Whether property is quantifier free */
    if (conj[1].getKind() != EXISTS)
    {
      conjBody = conj[1].substitute(
          fvars.begin(), fvars.end(), fsols.begin(), fsols.end());
    }
    else
    {
      conjBody = conj[1][1].substitute(
          fvars.begin(), fvars.end(), fsols.begin(), fsols.end());

      /* Skolemize property */
      std::vector<Node> vars, skos;
      for (unsigned j = 0, size = conj[1][0].getNumChildren(); j < size; ++j)
      {
        vars.push_back(conj[1][0][j]);
        std::stringstream ss;
        ss << "sk_" << j;
        skos.push_back(sm->mkDummySkolem(ss.str(), conj[1][0][j].getType()));
        Trace("check-synth-sol") << "\tSkolemizing " << conj[1][0][j] << " to "
                                 << skos.back() << "\n";
      }
      conjBody = conjBody.substitute(
          vars.begin(), vars.end(), skos.begin(), skos.end());
    }

    if (isVerboseOn(1))
    {
      verbose(1) << "SyGuS::checkSynthSolution: -- body substitutes to "
                 << conjBody << std::endl;
    }
    Trace("check-synth-sol")
        << "Substituted body of assertion to " << conjBody << "\n";
    solChecker->assertFormula(conjBody);
    // Assert all auxiliary assertions. This may include recursive function
    // definitions that were added as assertions to the sygus problem.
    for (Node a : auxAssertions)
    {
      // We require rewriting here, e.g. so that define-fun from the original
      // problem are rewritten to true. If this is not the case, then the
      // assertions module of the subsolver will complain about assertions
      // with free variables.
      Node ar = rewrite(a);
      solChecker->assertFormula(ar);
    }
    Result r = solChecker->checkSat();
    if (isVerboseOn(1))
    {
      verbose(1) << "SyGuS::checkSynthSolution: result is " << r << std::endl;
    }
    Trace("check-synth-sol") << "Satsifiability check: " << r << "\n";
    if (r.asSatisfiabilityResult().isUnknown())
    {
      InternalError() << "SygusSolver::checkSynthSolution(): could not check "
                         "solution, result "
                         "unknown.";
    }
    else if (r.asSatisfiabilityResult().isSat())
    {
      InternalError()
          << "SygusSolver::checkSynthSolution(): produced solution leads to "
             "satisfiable negated conjecture.";
    }
  }
}

void SygusSolver::setSygusConjectureStale()
{
  if (d_sygusConjectureStale)
  {
    // already stale
    return;
  }
  d_sygusConjectureStale = true;
  // TODO (project #7): if incremental, we should pop a context
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
                     : d_smtSolver.getPreprocessor()->expandDefinitions(op);
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

}  // namespace smt
}  // namespace cvc5
