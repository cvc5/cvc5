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

#include "expr/dtype.h"
#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "smt/preprocessor.h"
#include "smt/smt_solver.h"
#include "theory/smt_engine_subsolver.h"
#include "theory/theory_engine.h"

using namespace CVC4::theory;
using namespace CVC4::kind;

namespace CVC4 {
namespace smt {

SygusSolver::SygusSolver(SmtSolver& sms,
                         Preprocessor& pp,
                         context::UserContext* u)
    : d_smtSolver(sms), d_pp(pp), d_sygusConjectureStale(u, true)
{
}

SygusSolver::~SygusSolver() {}

void SygusSolver::declareSygusVar(const std::string& id,
                                  Node var,
                                  TypeNode type)
{
  Trace("smt") << "SygusSolver::declareSygusVar: " << id << " " << var << " "
               << type << "\n";
  Assert(var.getType() == type);
  d_sygusVars.push_back(var);
  // don't need to set that the conjecture is stale
}

void SygusSolver::declareSynthFun(const std::string& id,
                                  Node fn,
                                  TypeNode sygusType,
                                  bool isInv,
                                  const std::vector<Node>& vars)
{
  Trace("smt") << "SygusSolver::declareSynthFun: " << id << "\n";
  NodeManager* nm = NodeManager::currentNM();
  TheoryEngine* te = d_smtSolver.getTheoryEngine();
  Assert(te != nullptr);
  d_sygusFunSymbols.push_back(fn);
  if (!vars.empty())
  {
    Node bvl = nm->mkNode(BOUND_VAR_LIST, vars);
    std::vector<Node> attr_val_bvl;
    attr_val_bvl.push_back(bvl);
    te->setUserAttribute("sygus-synth-fun-var-list", fn, attr_val_bvl, "");
  }
  // whether sygus type encodes syntax restrictions
  if (sygusType.isDatatype() && sygusType.getDType().isSygus())
  {
    Node sym = nm->mkBoundVar("sfproxy", sygusType);
    std::vector<Node> attr_value;
    attr_value.push_back(sym);
    te->setUserAttribute("sygus-synth-grammar", fn, attr_value, "");
  }

  // sygus conjecture is now stale
  setSygusConjectureStale();
}

void SygusSolver::assertSygusConstraint(Node constraint)
{
  Trace("smt") << "SygusSolver::assertSygusConstrant: " << constraint << "\n";
  d_sygusConstraints.push_back(constraint);

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
  if (options::incrementalSolving())
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
    Node sygusVar = nm->mkSkolem("sygus", nm->booleanType());
    Node inst_attr = nm->mkNode(INST_ATTRIBUTE, sygusVar);
    Node sygusAttr = nm->mkNode(INST_PATTERN_LIST, inst_attr);
    std::vector<Node> bodyv;
    Trace("smt") << "Sygus : Constructing sygus constraint...\n";
    size_t nconstraints = d_sygusConstraints.size();
    Node body = nconstraints == 0
                    ? nm->mkConst(true)
                    : (nconstraints == 1 ? d_sygusConstraints[0]
                                         : nm->mkNode(AND, d_sygusConstraints));
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
      Node boundVars = nm->mkNode(BOUND_VAR_LIST, d_sygusFunSymbols);
      body = nm->mkNode(FORALL, boundVars, body, sygusAttr);
    }
    Trace("smt") << "...constructed forall " << body << std::endl;

    // set attribute for synthesis conjecture
    TheoryEngine* te = d_smtSolver.getTheoryEngine();
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
  Trace("smt") << "SygusSolver::getSynthSolutions" << std::endl;
  std::map<Node, std::map<Node, Node>> sol_mapn;
  // fail if the theory engine does not have synthesis solutions
  TheoryEngine* te = d_smtSolver.getTheoryEngine();
  Assert(te != nullptr);
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
  Notice() << "SygusSolver::checkSynthSolution(): checking synthesis solution"
           << std::endl;
  std::map<Node, std::map<Node, Node>> sol_map;
  // Get solutions and build auxiliary vectors for substituting
  TheoryEngine* te = d_smtSolver.getTheoryEngine();
  if (!te->getSynthSolutions(sol_map))
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
  // expand definitions cache
  std::unordered_map<Node, Node, NodeHashFunction> cache;
  for (Node assertion : *alist)
  {
    Notice() << "SygusSolver::checkSynthSolution(): checking assertion "
             << assertion << std::endl;
    Trace("check-synth-sol") << "Retrieving assertion " << assertion << "\n";
    // Apply any define-funs from the problem.
    Node n = d_pp.expandDefinitions(assertion, cache);
    Notice() << "SygusSolver::checkSynthSolution(): -- expands to " << n
             << std::endl;
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
    Notice() << "SygusSolver::checkSynthSolution(): -- body substitutes to "
             << conjBody << std::endl;
    Trace("check-synth-sol")
        << "Substituted body of assertion to " << conjBody << "\n";
    solChecker->assertFormula(conjBody);
    // Assert all auxiliary assertions. This may include recursive function
    // definitions that were added as assertions to the sygus problem.
    for (Node a : auxAssertions)
    {
      solChecker->assertFormula(a);
    }
    Result r = solChecker->checkSat();
    Notice() << "SygusSolver::checkSynthSolution(): result is " << r
             << std::endl;
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

}  // namespace smt
}  // namespace CVC4
