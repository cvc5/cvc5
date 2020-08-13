/*********************                                                        */
/*! \file sygus_solver.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The solver for sygus queries
 **/

#include "smt/sygus_solver.h"

#include "options/smt_options.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/theory_engine.h"
#include "options/quantifiers_options.h"
#include "theory/smt_engine_subsolver.h"
#include "smt/smt_solver.h"

using namespace CVC4::theory;
using namespace CVC4::kind;

namespace CVC4 {
namespace smt {

SygusSolver::SygusSolver(SmtEngine& smt, SmtSolver& sms, context::UserContext* u) : d_smt(smt), d_smtSolver(sms),
        d_sygusConjectureStale(u, true) {}

SygusSolver::~SygusSolver() {}

Result SygusSolver::checkSynth(Assertions& as)
{
  if (options::incrementalSolving())
  {
    // TODO (project #7)
    throw ModalException(
        "Cannot make check-synth commands when incremental solving is enabled");
  }
  std::vector<Node> query;
  if (d_sygusConjectureStale)
  {
    NodeManager * nm = NodeManager::currentNM();
    // build synthesis conjecture from asserted constraints and declared
    // variables/functions
    Node sygusVar =
        nm->mkSkolem("sygus", nm->booleanType());
    Node inst_attr = nm->mkNode(INST_ATTRIBUTE, sygusVar);
    Node sygusAttr = nm->mkNode(INST_PATTERN_LIST, inst_attr);
    std::vector<Node> bodyv;
    Trace("smt") << "Sygus : Constructing sygus constraint...\n";
    unsigned n_constraints = d_sygusConstraints.size();
    Node body = n_constraints == 0
                    ? nm->mkConst(true)
                    : (n_constraints == 1
                           ? d_sygusConstraints[0]
                           : nm->mkNode(
                               AND, d_sygusConstraints));
    body = body.notNode();
    Trace("smt") << "...constructed sygus constraint " << body << std::endl;
    if (!d_sygusVars.empty())
    {
      Node boundVars =
          nm->mkNode(BOUND_VAR_LIST, d_sygusVars);
      body = nm->mkNode(EXISTS, boundVars, body);
      Trace("smt") << "...constructed exists " << body << std::endl;
    }
    if (!d_sygusFunSymbols.empty())
    {
      Node boundVars = nm->mkNode(BOUND_VAR_LIST,
                                             d_sygusFunSymbols);
      body = nm->mkNode(FORALL, boundVars, body, sygusAttr);
    }
    Trace("smt") << "...constructed forall " << body << std::endl;

    // set attribute for synthesis conjecture
    TheoryEngine * te = d_smtSolver.getTheoryEngine();
    te->setUserAttribute("sygus", sygusVar, {}, "");

    Trace("smt") << "Check synthesis conjecture: " << body << std::endl;
    Dump("raw-benchmark") << CheckSynthCommand();

    d_sygusConjectureStale = false;

    // TODO (project #7): if incremental, we should push a context and assert
    query.push_back(body);
  }

  Result r = d_smtSolver.checkSatisfiability(as, query, false, false);
    
  // Check that synthesis solutions satisfy the conjecture
  if (options::checkSynthSol()
      && r.asSatisfiabilityResult().isSat() == Result::UNSAT)
  {
    checkSynthSolution(as);
  }
  return r;
}

bool SygusSolver::getSynthSolutions(std::map<Node, Node>& sol_map)
{
  std::map<Node, std::map<Node, Node>> sol_mapn;
  Assert(d_theoryEngine != nullptr);
  // fail if the theory engine does not have synthesis solutions
  TheoryEngine * te = d_smtSolver.getTheoryEngine();
  if (!te->getSynthSolutions(sol_mapn))
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
  Notice() << "SygusSolver::checkSynthSolution(): checking synthesis solution" << std::endl;
  std::map<Node, std::map<Node, Node>> sol_map;
  // Get solutions and build auxiliary vectors for substituting
  TheoryEngine * te = d_smtSolver.getTheoryEngine();
  if (!te->getSynthSolutions(sol_map))
  {
    InternalError() << "SygusSolver::checkSynthSolution(): No solution to check!";
    return;
  }
  if (sol_map.empty())
  {
    InternalError() << "SygusSolver::checkSynthSolution(): Got empty solution!";
    return;
  }
  Trace("check-synth-sol") << "Got solution map:\n";
  // the set of synthesis conjectures in our assertions
  std::unordered_set<Node, NodeHashFunction> conjs;
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
  context::CDList<Node>* alist = as.getAssertionList();
  if (alist == nullptr)
  {
    Trace("check-synth-sol") << "No assertions to check\n";
    return;
  }
  // auxiliary assertions
  std::vector<Node> auxAssertions;
  for (const Node& assertion : *alist)
  {
    Notice() << "SmtEngine::checkSynthSolution(): checking assertion "
             << assertion << std::endl;
    Trace("check-synth-sol") << "Retrieving assertion " << assertion << "\n";
    // Apply any define-funs from the problem.
    Node n = d_smt.expandDefinitions(assertion);
    Notice() << "SmtEngine::checkSynthSolution(): -- expands to " << n << std::endl;
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
  for (const Node& conj : conjs)
  {
    // Start new SMT engine to check solutions
    std::unique_ptr<SmtEngine> solChecker;
    initializeSubsolver(solChecker);
    solChecker->getOptions().set(options::checkSynthSol, false);
    solChecker->getOptions().set(options::sygusRecFun, false);
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
        skos.push_back(nm->mkSkolem(ss.str(), conj[1][0][j].getType()));
        Trace("check-synth-sol") << "\tSkolemizing " << conj[1][0][j] << " to "
                                 << skos.back() << "\n";
      }
      conjBody = conjBody.substitute(
          vars.begin(), vars.end(), skos.begin(), skos.end());
    }
    Notice() << "SmtEngine::checkSynthSolution(): -- body substitutes to "
             << conjBody << std::endl;
    Trace("check-synth-sol") << "Substituted body of assertion to " << conjBody
                             << "\n";
    solChecker->assertFormula(conjBody);
    // Assert all auxiliary assertions. This may include recursive function
    // definitions that were added as assertions to the sygus problem.
    for (const Node& a : auxAssertions)
    {
      solChecker->assertFormula(a);
    }
    Result r = solChecker->checkSat();
    Notice() << "SmtEngine::checkSynthSolution(): result is " << r << std::endl;
    Trace("check-synth-sol") << "Satsifiability check: " << r << "\n";
    if (r.asSatisfiabilityResult().isUnknown())
    {
      InternalError() << "SmtEngine::checkSynthSolution(): could not check "
                         "solution, result "
                         "unknown.";
    }
    else if (r.asSatisfiabilityResult().isSat())
    {
      InternalError()
          << "SmtEngine::checkSynthSolution(): produced solution leads to "
             "satisfiable negated conjecture.";
    }
  }
}

bool SygusSolver::setSygusConjectureStale()
{
  if (d_sygusConjectureStale)
  {
    // already stale
    return false;
  }
  d_sygusConjectureStale = true;
  return true;
}

}  // namespace smt
}  // namespace CVC4
