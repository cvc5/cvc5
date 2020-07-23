/*********************                                                        */
/*! \file nonlinear_extension.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/arith/nl/nonlinear_extension.h"

#include "options/arith_options.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/theory_arith.h"
#include "theory/ext_theory.h"
#include "theory/theory_model.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {

NonlinearExtension::NonlinearExtension(TheoryArith& containing,
                                       eq::EqualityEngine* ee)
    : d_lemmas(containing.getUserContext()),
      d_lemmasPp(containing.getUserContext()),
      d_containing(containing),
      d_ee(ee),
      d_needsLastCall(false),
      d_extTheory(&containing),
      d_model(containing.getSatContext()),
      d_trSlv(d_model),
      d_nlSlv(containing, d_model),
      d_iandSlv(containing, d_model),
      d_builtModel(containing.getSatContext(), false)
{
  d_extTheory.addFunctionKind(kind::NONLINEAR_MULT);
  d_extTheory.addFunctionKind(kind::EXPONENTIAL);
  d_extTheory.addFunctionKind(kind::SINE);
  d_extTheory.addFunctionKind(kind::PI);
  d_extTheory.addFunctionKind(kind::IAND);
  d_true = NodeManager::currentNM()->mkConst(true);
  d_zero = NodeManager::currentNM()->mkConst(Rational(0));
  d_one = NodeManager::currentNM()->mkConst(Rational(1));
  d_neg_one = NodeManager::currentNM()->mkConst(Rational(-1));
}

NonlinearExtension::~NonlinearExtension() {}

void NonlinearExtension::preRegisterTerm(TNode n)
{
  // register terms with extended theory, to find extended terms that can be
  // eliminated by context-depedendent simplification.
  d_extTheory.registerTermRec(n);
}

bool NonlinearExtension::getCurrentSubstitution(
    int effort,
    const std::vector<Node>& vars,
    std::vector<Node>& subs,
    std::map<Node, std::vector<Node>>& exp)
{
  // get the constant equivalence classes
  std::map<Node, std::vector<int>> rep_to_subs_index;

  bool retVal = false;
  for (unsigned i = 0; i < vars.size(); i++)
  {
    Node n = vars[i];
    if (d_ee->hasTerm(n))
    {
      Node nr = d_ee->getRepresentative(n);
      if (nr.isConst())
      {
        subs.push_back(nr);
        Trace("nl-subs") << "Basic substitution : " << n << " -> " << nr
                         << std::endl;
        exp[n].push_back(n.eqNode(nr));
        retVal = true;
      }
      else
      {
        rep_to_subs_index[nr].push_back(i);
        subs.push_back(n);
      }
    }
    else
    {
      subs.push_back(n);
    }
  }

  // return true if the substitution is non-trivial
  return retVal;
}

std::pair<bool, Node> NonlinearExtension::isExtfReduced(
    int effort, Node n, Node on, const std::vector<Node>& exp) const
{
  if (n != d_zero)
  {
    Kind k = n.getKind();
    return std::make_pair(
        k != NONLINEAR_MULT && !isTranscendentalKind(k) && k != IAND,
        Node::null());
  }
  Assert(n == d_zero);
  if (on.getKind() == NONLINEAR_MULT)
  {
    Trace("nl-ext-zero-exp")
        << "Infer zero : " << on << " == " << n << std::endl;
    // minimize explanation if a substitution+rewrite results in zero
    const std::set<Node> vars(on.begin(), on.end());

    for (unsigned i = 0, size = exp.size(); i < size; i++)
    {
      Trace("nl-ext-zero-exp")
          << "  exp[" << i << "] = " << exp[i] << std::endl;
      std::vector<Node> eqs;
      if (exp[i].getKind() == EQUAL)
      {
        eqs.push_back(exp[i]);
      }
      else if (exp[i].getKind() == AND)
      {
        for (const Node& ec : exp[i])
        {
          if (ec.getKind() == EQUAL)
          {
            eqs.push_back(ec);
          }
        }
      }

      for (unsigned j = 0; j < eqs.size(); j++)
      {
        for (unsigned r = 0; r < 2; r++)
        {
          if (eqs[j][r] == d_zero && vars.find(eqs[j][1 - r]) != vars.end())
          {
            Trace("nl-ext-zero-exp")
                << "...single exp : " << eqs[j] << std::endl;
            return std::make_pair(true, eqs[j]);
          }
        }
      }
    }
  }
  return std::make_pair(true, Node::null());
}

void NonlinearExtension::sendLemmas(const std::vector<NlLemma>& out)
{
  for (const NlLemma& nlem : out)
  {
    Node lem = nlem.d_lemma;
    bool preprocess = nlem.d_preprocess;
    Trace("nl-ext-lemma") << "NonlinearExtension::Lemma : " << nlem.d_id
                          << " : " << lem << std::endl;
    d_containing.getOutputChannel().lemma(lem, false, preprocess);
    // process the side effect
    processSideEffect(nlem);
    // add to cache if not preprocess
    if (preprocess)
    {
      d_lemmasPp.insert(lem);
    }
    else
    {
      d_lemmas.insert(lem);
    }
    d_stats.d_inferences << nlem.d_id;
    // also indicate this is a tautology
    d_model.addTautology(lem);
  }
}

void NonlinearExtension::processSideEffect(const NlLemma& se)
{
  d_trSlv.processSideEffect(se);
}

unsigned NonlinearExtension::filterLemma(NlLemma lem, std::vector<NlLemma>& out)
{
  Trace("nl-ext-lemma-debug")
      << "NonlinearExtension::Lemma pre-rewrite : " << lem.d_lemma << std::endl;
  lem.d_lemma = Rewriter::rewrite(lem.d_lemma);
  // get the proper cache
  NodeSet& lcache = lem.d_preprocess ? d_lemmasPp : d_lemmas;
  if (lcache.find(lem.d_lemma) != lcache.end())
  {
    Trace("nl-ext-lemma-debug")
        << "NonlinearExtension::Lemma duplicate : " << lem.d_lemma << std::endl;
    return 0;
  }
  out.emplace_back(lem);
  return 1;
}

unsigned NonlinearExtension::filterLemmas(std::vector<NlLemma>& lemmas,
                                          std::vector<NlLemma>& out)
{
  if (options::nlExtEntailConflicts())
  {
    // check if any are entailed to be false
    for (const NlLemma& lem : lemmas)
    {
      Node ch_lemma = lem.d_lemma.negate();
      ch_lemma = Rewriter::rewrite(ch_lemma);
      Trace("nl-ext-et-debug")
          << "Check entailment of " << ch_lemma << "..." << std::endl;
      std::pair<bool, Node> et = d_containing.getValuation().entailmentCheck(
          options::TheoryOfMode::THEORY_OF_TYPE_BASED, ch_lemma);
      Trace("nl-ext-et-debug") << "entailment test result : " << et.first << " "
                               << et.second << std::endl;
      if (et.first)
      {
        Trace("nl-ext-et") << "*** Lemma entailed to be in conflict : "
                           << lem.d_lemma << std::endl;
        // return just this lemma
        if (filterLemma(lem, out) > 0)
        {
          lemmas.clear();
          return 1;
        }
      }
    }
  }

  unsigned sum = 0;
  for (const NlLemma& lem : lemmas)
  {
    sum += filterLemma(lem, out);
  }
  lemmas.clear();
  return sum;
}

void NonlinearExtension::getAssertions(std::vector<Node>& assertions)
{
  Trace("nl-ext") << "Getting assertions..." << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  // get the assertions
  std::map<Node, Rational> init_bounds[2];
  std::map<Node, Node> init_bounds_lit[2];
  unsigned nassertions = 0;
  std::unordered_set<Node, NodeHashFunction> init_assertions;
  for (Theory::assertions_iterator it = d_containing.facts_begin();
       it != d_containing.facts_end();
       ++it)
  {
    nassertions++;
    const Assertion& assertion = *it;
    Node lit = assertion.d_assertion;
    init_assertions.insert(lit);
    // check for concrete bounds
    bool pol = lit.getKind() != NOT;
    Node atom_orig = lit.getKind() == NOT ? lit[0] : lit;

    std::vector<Node> atoms;
    if (atom_orig.getKind() == EQUAL)
    {
      if (pol)
      {
        // t = s  is ( t >= s ^ t <= s )
        for (unsigned i = 0; i < 2; i++)
        {
          Node atom_new = nm->mkNode(GEQ, atom_orig[i], atom_orig[1 - i]);
          atom_new = Rewriter::rewrite(atom_new);
          atoms.push_back(atom_new);
        }
      }
    }
    else
    {
      atoms.push_back(atom_orig);
    }

    for (const Node& atom : atoms)
    {
      // non-strict bounds only
      if (atom.getKind() == GEQ || (!pol && atom.getKind() == GT))
      {
        Node p = atom[0];
        Assert(atom[1].isConst());
        Rational bound = atom[1].getConst<Rational>();
        if (!pol)
        {
          if (atom[0].getType().isInteger())
          {
            // ~( p >= c ) ---> ( p <= c-1 )
            bound = bound - Rational(1);
          }
        }
        unsigned bindex = pol ? 0 : 1;
        bool setBound = true;
        std::map<Node, Rational>::iterator itb = init_bounds[bindex].find(p);
        if (itb != init_bounds[bindex].end())
        {
          if (itb->second == bound)
          {
            setBound = atom_orig.getKind() == EQUAL;
          }
          else
          {
            setBound = pol ? itb->second < bound : itb->second > bound;
          }
          if (setBound)
          {
            // the bound is subsumed
            init_assertions.erase(init_bounds_lit[bindex][p]);
          }
        }
        if (setBound)
        {
          Trace("nl-ext-init") << (pol ? "Lower" : "Upper") << " bound for "
                               << p << " : " << bound << std::endl;
          init_bounds[bindex][p] = bound;
          init_bounds_lit[bindex][p] = lit;
        }
      }
    }
  }
  // for each bound that is the same, ensure we've inferred the equality
  for (std::pair<const Node, Rational>& ib : init_bounds[0])
  {
    Node p = ib.first;
    Node lit1 = init_bounds_lit[0][p];
    if (lit1.getKind() != EQUAL)
    {
      std::map<Node, Rational>::iterator itb = init_bounds[1].find(p);
      if (itb != init_bounds[1].end())
      {
        if (ib.second == itb->second)
        {
          Node eq = p.eqNode(nm->mkConst(ib.second));
          eq = Rewriter::rewrite(eq);
          Node lit2 = init_bounds_lit[1][p];
          Assert(lit2.getKind() != EQUAL);
          // use the equality instead, thus these are redundant
          init_assertions.erase(lit1);
          init_assertions.erase(lit2);
          init_assertions.insert(eq);
        }
      }
    }
  }

  for (const Node& a : init_assertions)
  {
    assertions.push_back(a);
  }
  Trace("nl-ext") << "...keep " << assertions.size() << " / " << nassertions
                  << " assertions." << std::endl;
}

std::vector<Node> NonlinearExtension::checkModelEval(
    const std::vector<Node>& assertions)
{
  std::vector<Node> false_asserts;
  for (size_t i = 0; i < assertions.size(); ++i)
  {
    Node lit = assertions[i];
    Node atom = lit.getKind() == NOT ? lit[0] : lit;
    Node litv = d_model.computeConcreteModelValue(lit);
    Trace("nl-ext-mv-assert") << "M[[ " << lit << " ]] -> " << litv;
    if (litv != d_true)
    {
      Trace("nl-ext-mv-assert") << " [model-false]" << std::endl;
      false_asserts.push_back(lit);
    }
    else
    {
      Trace("nl-ext-mv-assert") << std::endl;
    }
  }
  return false_asserts;
}

bool NonlinearExtension::checkModel(const std::vector<Node>& assertions,
                                    const std::vector<Node>& false_asserts,
                                    std::vector<NlLemma>& lemmas,
                                    std::vector<Node>& gs)
{
  Trace("nl-ext-cm") << "--- check-model ---" << std::endl;

  // get the presubstitution
  Trace("nl-ext-cm-debug") << "  apply pre-substitution..." << std::endl;
  std::vector<Node> passertions = assertions;
  if (options::nlExt())
  {
    // preprocess the assertions with the trancendental solver
    if (!d_trSlv.preprocessAssertionsCheckModel(passertions))
    {
      return false;
    }
  }

  Trace("nl-ext-cm") << "-----" << std::endl;
  unsigned tdegree = d_trSlv.getTaylorDegree();
  bool ret = d_model.checkModel(passertions, tdegree, lemmas, gs);
  return ret;
}

int NonlinearExtension::checkLastCall(const std::vector<Node>& assertions,
                                      const std::vector<Node>& false_asserts,
                                      const std::vector<Node>& xts,
                                      std::vector<NlLemma>& lems,
                                      std::vector<NlLemma>& wlems)
{
  std::vector<NlLemma> lemmas;

  ++(d_stats.d_checkRuns);

  if (options::nlExt())
  {
    // initialize the non-linear solver
    d_nlSlv.initLastCall(assertions, false_asserts, xts);
    // initialize the trancendental function solver
    d_trSlv.initLastCall(assertions, false_asserts, xts, lemmas);
    // process lemmas that may have been generated by the transcendental solver
    filterLemmas(lemmas, lems);
  }
  
  // init last call with IAND
  d_iandSlv.initLastCall(assertions, false_asserts, xts);
  
  if (!lems.empty())
  {
    Trace("nl-ext") << "  ...finished with " << lems.size()
                    << " new lemmas during registration." << std::endl;
    return lems.size();
  }

  //----------------------------------- possibly split on zero
  if (options::nlExt() && options::nlExtSplitZero())
  {
    Trace("nl-ext") << "Get zero split lemmas..." << std::endl;
    lemmas = d_nlSlv.checkSplitZero();
    filterLemmas(lemmas, lems);
    if (!lems.empty())
    {
      Trace("nl-ext") << "  ...finished with " << lems.size() << " new lemmas."
                      << std::endl;
      return lems.size();
    }
  }

  //-----------------------------------initial lemmas for transcendental
  if (options::nlExt())
  {
    // functions
    lemmas = d_trSlv.checkTranscendentalInitialRefine();
    filterLemmas(lemmas, lems);
    if (!lems.empty())
    {
      Trace("nl-ext") << "  ...finished with " << lems.size() << " new lemmas."
                      << std::endl;
      return lems.size();
    }
  }
  //-----------------------------------initial lemmas for iand
  lemmas = d_iandSlv.checkInitialRefine();
  filterLemmas(lemmas, lems);
  if (!lems.empty())
  {
    Trace("nl-ext") << "  ...finished with " << lems.size() << " new lemmas."
                    << std::endl;
    return lems.size();
  }
  
  // main calls to nlExt
  if (options::nlExt())
  {
    //---------------------------------lemmas based on sign (comparison to zero)
    lemmas = d_nlSlv.checkMonomialSign();
    filterLemmas(lemmas, lems);
    if (!lems.empty())
    {
      Trace("nl-ext") << "  ...finished with " << lems.size() << " new lemmas."
                      << std::endl;
      return lems.size();
    }

    //-----------------------------------monotonicity of transdental functions
    lemmas = d_trSlv.checkTranscendentalMonotonic();
    filterLemmas(lemmas, lems);
    if (!lems.empty())
    {
      Trace("nl-ext") << "  ...finished with " << lems.size() << " new lemmas."
                      << std::endl;
      return lems.size();
    }

    //------------------------lemmas based on magnitude of non-zero monomials
    for (unsigned c = 0; c < 3; c++)
    {
      // c is effort level
      lemmas = d_nlSlv.checkMonomialMagnitude(c);
      unsigned nlem = lemmas.size();
      filterLemmas(lemmas, lems);
      if (!lems.empty())
      {
        Trace("nl-ext") << "  ...finished with " << lems.size()
                        << " new lemmas (out of possible " << nlem << ")."
                        << std::endl;
        return lems.size();
      }
    }

    //-----------------------------------inferred bounds lemmas
    //  e.g. x >= t => y*x >= y*t
    std::vector<NlLemma> nt_lemmas;
    lemmas =
        d_nlSlv.checkMonomialInferBounds(nt_lemmas, assertions, false_asserts);
    // Trace("nl-ext") << "Bound lemmas : " << lemmas.size() << ", " <<
    // nt_lemmas.size() << std::endl;  prioritize lemmas that do not
    // introduce new monomials
    filterLemmas(lemmas, lems);

    if (options::nlExtTangentPlanes()
        && options::nlExtTangentPlanesInterleave())
    {
      lemmas = d_nlSlv.checkTangentPlanes();
      filterLemmas(lemmas, lems);
    }

    if (!lems.empty())
    {
      Trace("nl-ext") << "  ...finished with " << lems.size() << " new lemmas."
                      << std::endl;
      return lems.size();
    }

    // from inferred bound inferences : now do ones that introduce new terms
    filterLemmas(nt_lemmas, lems);
    if (!lems.empty())
    {
      Trace("nl-ext") << "  ...finished with " << lems.size()
                      << " new (monomial-introducing) lemmas." << std::endl;
      return lems.size();
    }

    //------------------------------------factoring lemmas
    //   x*y + x*z >= t => exists k. k = y + z ^ x*k >= t
    if (options::nlExtFactor())
    {
      lemmas = d_nlSlv.checkFactoring(assertions, false_asserts);
      filterLemmas(lemmas, lems);
      if (!lems.empty())
      {
        Trace("nl-ext") << "  ...finished with " << lems.size()
                        << " new lemmas." << std::endl;
        return lems.size();
      }
    }

    //------------------------------------resolution bound inferences
    //  e.g. ( y>=0 ^ s <= x*z ^ x*y <= t ) => y*s <= z*t
    if (options::nlExtResBound())
    {
      lemmas = d_nlSlv.checkMonomialInferResBounds();
      filterLemmas(lemmas, lems);
      if (!lems.empty())
      {
        Trace("nl-ext") << "  ...finished with " << lems.size()
                        << " new lemmas." << std::endl;
        return lems.size();
      }
    }

    //------------------------------------tangent planes
    if (options::nlExtTangentPlanes()
        && !options::nlExtTangentPlanesInterleave())
    {
      lemmas = d_nlSlv.checkTangentPlanes();
      filterLemmas(lemmas, wlems);
    }
    if (options::nlExtTfTangentPlanes())
    {
      lemmas = d_trSlv.checkTranscendentalTangentPlanes();
      filterLemmas(lemmas, wlems);
    }
  }
  // run the full refinement in the IAND solver
  lemmas = d_iandSlv.checkFullRefine();
  filterLemmas(lemmas, wlems);

  Trace("nl-ext") << "  ...finished with " << wlems.size() << " waiting lemmas."
                  << std::endl;

  return 0;
}

void NonlinearExtension::check(Theory::Effort e)
{
  Trace("nl-ext") << std::endl;
  Trace("nl-ext") << "NonlinearExtension::check, effort = " << e
                  << ", built model = " << d_builtModel.get() << std::endl;
  if (e == Theory::EFFORT_FULL)
  {
    d_extTheory.clearCache();
    d_needsLastCall = true;
    if (options::nlExtRewrites())
    {
      std::vector<Node> nred;
      if (!d_extTheory.doInferences(0, nred))
      {
        Trace("nl-ext") << "...sent no lemmas, # extf to reduce = "
                        << nred.size() << std::endl;
        if (nred.empty())
        {
          d_needsLastCall = false;
        }
      }
      else
      {
        Trace("nl-ext") << "...sent lemmas." << std::endl;
      }
    }
  }
  else
  {
    // If we computed lemmas during collectModelInfo, send them now.
    if (!d_cmiLemmas.empty())
    {
      sendLemmas(d_cmiLemmas);
      return;
    }
    // Otherwise, we will answer SAT. The values that we approximated are
    // recorded as approximations here.
    TheoryModel* tm = d_containing.getValuation().getModel();
    for (std::pair<const Node, std::pair<Node, Node>>& a : d_approximations)
    {
      if (a.second.second.isNull())
      {
        tm->recordApproximation(a.first, a.second.first);
      }
      else
      {
        tm->recordApproximation(a.first, a.second.first, a.second.second);
      }
    }
    for (const auto& vw : d_witnesses)
    {
      tm->recordApproximation(vw.first, vw.second);
    }
  }
}

bool NonlinearExtension::modelBasedRefinement(std::vector<NlLemma>& mlems)
{
  ++(d_stats.d_mbrRuns);

  // get the assertions
  std::vector<Node> assertions;
  getAssertions(assertions);

  Trace("nl-ext-mv-assert")
      << "Getting model values... check for [model-false]" << std::endl;
  // get the assertions that are false in the model
  const std::vector<Node> false_asserts = checkModelEval(assertions);
  Trace("nl-ext") << "# false asserts = " << false_asserts.size() << std::endl;

  // get the extended terms belonging to this theory
  std::vector<Node> xts;
  d_extTheory.getTerms(xts);

  if (Trace.isOn("nl-ext-debug"))
  {
    Trace("nl-ext-debug") << "  processing NonlinearExtension::check : "
                          << std::endl;
    Trace("nl-ext-debug") << "     " << false_asserts.size()
                          << " false assertions" << std::endl;
    Trace("nl-ext-debug") << "     " << xts.size()
                          << " extended terms: " << std::endl;
    Trace("nl-ext-debug") << "       ";
    for (unsigned j = 0; j < xts.size(); j++)
    {
      Trace("nl-ext-debug") << xts[j] << " ";
    }
    Trace("nl-ext-debug") << std::endl;
  }

  // compute whether shared terms have correct values
  unsigned num_shared_wrong_value = 0;
  std::vector<Node> shared_term_value_splits;
  // must ensure that shared terms are equal to their concrete value
  Trace("nl-ext-mv") << "Shared terms : " << std::endl;
  for (context::CDList<TNode>::const_iterator its =
           d_containing.shared_terms_begin();
       its != d_containing.shared_terms_end();
       ++its)
  {
    TNode shared_term = *its;
    // compute its value in the model, and its evaluation in the model
    Node stv0 = d_model.computeConcreteModelValue(shared_term);
    Node stv1 = d_model.computeAbstractModelValue(shared_term);
    d_model.printModelValue("nl-ext-mv", shared_term);
    if (stv0 != stv1)
    {
      num_shared_wrong_value++;
      Trace("nl-ext-mv") << "Bad shared term value : " << shared_term
                         << std::endl;
      if (shared_term != stv0)
      {
        // split on the value, this is non-terminating in general, TODO :
        // improve this
        Node eq = shared_term.eqNode(stv0);
        shared_term_value_splits.push_back(eq);
      }
      else
      {
        // this can happen for transcendental functions
        // the problem is that we cannot evaluate transcendental functions
        // (they don't have a rewriter that returns constants)
        // thus, the actual value in their model can be themselves, hence we
        // have no reference point to rule out the current model.  In this
        // case, we may set incomplete below.
      }
    }
  }
  Trace("nl-ext-debug") << "     " << num_shared_wrong_value
                        << " shared terms with wrong model value." << std::endl;
  bool needsRecheck;
  do
  {
    d_model.resetCheck();
    needsRecheck = false;
    // complete_status:
    //   1 : we may answer SAT, -1 : we may not answer SAT, 0 : unknown
    int complete_status = 1;
    // lemmas that should be sent later
    std::vector<NlLemma> wlems;
    // We require a check either if an assertion is false or a shared term has
    // a wrong value
    if (!false_asserts.empty() || num_shared_wrong_value > 0)
    {
      complete_status = num_shared_wrong_value > 0 ? -1 : 0;
      checkLastCall(assertions, false_asserts, xts, mlems, wlems);
      if (!mlems.empty())
      {
        return true;
      }
    }
    Trace("nl-ext") << "Finished check with status : " << complete_status
                    << std::endl;

    // if we did not add a lemma during check and there is a chance for SAT
    if (complete_status == 0)
    {
      Trace("nl-ext")
          << "Check model based on bounds for irrational-valued functions..."
          << std::endl;
      // check the model based on simple solving of equalities and using
      // error bounds on the Taylor approximation of transcendental functions.
      std::vector<NlLemma> lemmas;
      std::vector<Node> gs;
      if (checkModel(assertions, false_asserts, lemmas, gs))
      {
        complete_status = 1;
      }
      for (const Node& mg : gs)
      {
        Node mgr = Rewriter::rewrite(mg);
        mgr = d_containing.getValuation().ensureLiteral(mgr);
        d_containing.getOutputChannel().requirePhase(mgr, true);
        d_builtModel = true;
      }
      filterLemmas(lemmas, mlems);
      if (!mlems.empty())
      {
        return true;
      }
    }

    // if we have not concluded SAT
    if (complete_status != 1)
    {
      // flush the waiting lemmas
      if (!wlems.empty())
      {
        mlems.insert(mlems.end(), wlems.begin(), wlems.end());
        Trace("nl-ext") << "...added " << wlems.size() << " waiting lemmas."
                        << std::endl;
        return true;
      }
      // resort to splitting on shared terms with their model value
      // if we did not add any lemmas
      if (num_shared_wrong_value > 0)
      {
        complete_status = -1;
        if (!shared_term_value_splits.empty())
        {
          std::vector<NlLemma> stvLemmas;
          for (const Node& eq : shared_term_value_splits)
          {
            Node req = Rewriter::rewrite(eq);
            Node literal = d_containing.getValuation().ensureLiteral(req);
            d_containing.getOutputChannel().requirePhase(literal, true);
            Trace("nl-ext-debug") << "Split on : " << literal << std::endl;
            Node split = literal.orNode(literal.negate());
            NlLemma nsplit(split, Inference::SHARED_TERM_VALUE_SPLIT);
            filterLemma(nsplit, stvLemmas);
          }
          if (!stvLemmas.empty())
          {
            mlems.insert(mlems.end(), stvLemmas.begin(), stvLemmas.end());
            Trace("nl-ext") << "...added " << stvLemmas.size()
                            << " shared term value split lemmas." << std::endl;
            return true;
          }
        }
        else
        {
          // this can happen if we are trying to do theory combination with
          // trancendental functions
          // since their model value cannot even be computed exactly
        }
      }

      // we are incomplete
      if (options::nlExt() && options::nlExtIncPrecision()
          && d_model.usedApproximate())
      {
        d_trSlv.incrementTaylorDegree();
        needsRecheck = true;
        // increase precision for PI?
        // Difficult since Taylor series is very slow to converge
        Trace("nl-ext") << "...increment Taylor degree to "
                        << d_trSlv.getTaylorDegree() << std::endl;
      }
      else
      {
        Trace("nl-ext") << "...failed to send lemma in "
                           "NonLinearExtension, set incomplete"
                        << std::endl;
        d_containing.getOutputChannel().setIncomplete();
      }
    }
  } while (needsRecheck);

  // did not add lemmas
  return false;
}

void NonlinearExtension::interceptModel(std::map<Node, Node>& arithModel)
{
  if (!needsCheckLastEffort())
  {
    // no non-linear constraints, we are done
    return;
  }
  Trace("nl-ext") << "NonlinearExtension::interceptModel begin" << std::endl;
  d_model.reset(d_containing.getValuation().getModel(), arithModel);
  // run a last call effort check
  d_cmiLemmas.clear();
  if (!d_builtModel.get())
  {
    Trace("nl-ext") << "interceptModel: do model-based refinement" << std::endl;
    modelBasedRefinement(d_cmiLemmas);
  }
  if (d_builtModel.get())
  {
    Trace("nl-ext") << "interceptModel: do model repair" << std::endl;
    d_approximations.clear();
    d_witnesses.clear();
    // modify the model values
    d_model.getModelValueRepair(arithModel, d_approximations, d_witnesses);
  }
}

void NonlinearExtension::presolve()
{
  Trace("nl-ext") << "NonlinearExtension::presolve" << std::endl;
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4
