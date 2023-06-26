/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of candidate_rewrite_database.
 */

#include "theory/quantifiers/candidate_rewrite_database.h"

#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "printer/printer.h"
#include "smt/set_defaults.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"
#include "theory/rewriter.h"

using namespace std;
using namespace cvc5::internal::kind;
using namespace cvc5::context;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

CandidateRewriteDatabase::CandidateRewriteDatabase(
    Env& env, bool doCheck, bool rewAccel, bool filterPairs, bool rec)
    : ExprMiner(env),
      d_tds(nullptr),
      d_useExtRewriter(false),
      d_doCheck(doCheck),
      d_rewAccel(rewAccel),
      d_filterPairs(filterPairs),
      d_using_sygus(false),
      d_rec(rec),
      d_crewrite_filter(env)
{
  // determine the options to use for the verification subsolvers we spawn
  // we start with the provided options
  d_subOptions.copyValues(options());
  // disable checking
  smt::SetDefaults::disableChecking(d_subOptions);
}
void CandidateRewriteDatabase::initialize(const std::vector<Node>& vars,
                                          SygusSampler* ss)
{
  Assert(ss != nullptr);
  d_candidate = Node::null();
  d_using_sygus = false;
  d_tds = nullptr;
  d_useExtRewriter = false;
  if (d_filterPairs)
  {
    d_crewrite_filter.initialize(ss, nullptr, false);
  }
  ExprMiner::initialize(vars, ss);
}

void CandidateRewriteDatabase::initializeSygus(const std::vector<Node>& vars,
                                               TermDbSygus* tds,
                                               Node f,
                                               SygusSampler* ss)
{
  Assert(ss != nullptr);
  d_candidate = f;
  d_using_sygus = true;
  d_tds = tds;
  d_useExtRewriter = false;
  if (d_filterPairs)
  {
    d_crewrite_filter.initialize(ss, d_tds, d_using_sygus);
  }
  ExprMiner::initialize(vars, ss);
}

bool CandidateRewriteDatabase::wasVerified(const Node& rewrite) const
{
  return d_verified.find(rewrite) != d_verified.end();
}

Node CandidateRewriteDatabase::addOrGetTerm(Node sol,
                                            std::vector<Node>& rewrites)
{
  // have we added this term before?
  std::unordered_map<Node, Node>::iterator itac = d_add_term_cache.find(sol);
  if (itac != d_add_term_cache.end())
  {
    return itac->second;
  }

  if (d_rec)
  {
    // if recursive, we first add all subterms
    for (const Node& solc : sol)
    {
      // whether a candidate rewrite is printed for any subterm is irrelevant
      addTerm(solc, rewrites);
    }
  }
  // register the term
  bool is_unique_term = true;
  Node eq_sol = d_sampler->registerTerm(sol);
  Trace("rr-check-r") << sol << " returns " << eq_sol << std::endl;
  // eq_sol is a candidate solution that is equivalent to sol
  if (eq_sol != sol)
  {
    is_unique_term = false;
    // should we filter the pair?
    if (!d_filterPairs || !d_crewrite_filter.filterPair(sol, eq_sol))
    {
      // get the actual term
      Node solb = sol;
      Node eq_solb = eq_sol;
      if (d_using_sygus)
      {
        Assert(d_tds != nullptr);
        solb = d_tds->sygusToBuiltin(sol);
        eq_solb = d_tds->sygusToBuiltin(eq_sol);
      }
      // get the rewritten form
      Node solbr;
      Node eq_solr;
      if (d_useExtRewriter)
      {
        solbr = extendedRewrite(solb);
        eq_solr = extendedRewrite(eq_solb);
      }
      else
      {
        solbr = rewrite(solb);
        eq_solr = rewrite(eq_solb);
      }
      bool verified = false;
      Trace("rr-check") << "Check candidate rewrite..." << std::endl;
      // verify it if applicable
      if (d_doCheck)
      {
        Node crr = solbr.eqNode(eq_solr).negate();
        Trace("rr-check") << "Check candidate rewrite : " << crr << std::endl;

        // Notice we don't set produce-models. rrChecker takes the same
        // options as the SolverEngine we belong to, where we ensure that
        // produce-models is set.
        SubsolverSetupInfo ssi(d_env, d_subOptions);
        std::unique_ptr<SolverEngine> rrChecker;
        initializeChecker(rrChecker, crr, ssi);
        Result r = rrChecker->checkSat();
        Trace("rr-check") << "...result : " << r << std::endl;
        if (r.getStatus() == Result::SAT)
        {
          Trace("rr-check") << "...rewrite does not hold for: " << std::endl;
          NodeManager* nm = NodeManager::currentNM();
          is_unique_term = true;
          std::vector<Node> vars;
          d_sampler->getVariables(vars);
          std::vector<Node> pt;
          for (const Node& v : vars)
          {
            Node val;
            Node refv = v;
            // if a bound variable, map to the skolem we introduce before
            // looking up the model value
            if (v.getKind() == BOUND_VARIABLE)
            {
              std::map<Node, Node>::iterator itf = d_fv_to_skolem.find(v);
              if (itf == d_fv_to_skolem.end())
              {
                // not in conjecture, can use arbitrary value
                val = nm->mkGroundTerm(v.getType());
              }
              else
              {
                // get the model value of its skolem
                refv = itf->second;
              }
            }
            if (val.isNull())
            {
              Assert(!refv.isNull() && refv.getKind() != BOUND_VARIABLE);
              val = rrChecker->getValue(refv);
            }
            Trace("rr-check") << "  " << v << " -> " << val << std::endl;
            pt.push_back(val);
          }
          d_sampler->addSamplePoint(pt);
          // add the solution again
          // by construction of the above point, we should be unique now
          eq_sol = d_sampler->registerTerm(sol);
          Assert(eq_sol == sol) << "Model failed to distinguish terms "
                                << eq_sol << " and " << sol;
        }
        else
        {
          verified = !r.isUnknown();
        }
      }
      else
      {
        // just insist that constants are not relevant pairs
        if (solb.isConst() && eq_solb.isConst())
        {
          is_unique_term = true;
          eq_sol = sol;
        }
      }
      if (!is_unique_term)
      {
        // register this as a relevant pair (helps filtering)
        if (d_filterPairs)
        {
          d_crewrite_filter.registerRelevantPair(sol, eq_sol);
        }
        // The analog of terms sol and eq_sol are equivalent under
        // sample points but do not rewrite to the same term. Hence,
        // this indicates a candidate rewrite.
        Node eq = solb.eqNode(eq_sol);
        rewrites.push_back(eq);
        if (verified)
        {
          d_verified.insert(eq);
        }
        // debugging information
        if (TraceIsOn("sygus-rr-debug"))
        {
          Trace("sygus-rr-debug") << "; candidate #1 ext-rewrites to: " << solbr
                                  << std::endl;
          Trace("sygus-rr-debug")
              << "; candidate #2 ext-rewrites to: " << eq_solr << std::endl;
        }
        if (d_rewAccel && d_using_sygus)
        {
          Assert(d_tds != nullptr);
          // Add a symmetry breaking clause that excludes the larger
          // of sol and eq_sol. This effectively states that we no longer
          // wish to enumerate any term that contains sol (resp. eq_sol)
          // as a subterm.
          Node exc_sol = sol;
          unsigned sz = datatypes::utils::getSygusTermSize(sol);
          unsigned eqsz = datatypes::utils::getSygusTermSize(eq_sol);
          if (eqsz > sz)
          {
            sz = eqsz;
            exc_sol = eq_sol;
          }
          TypeNode ptn = d_candidate.getType();
          Node x = d_tds->getFreeVar(ptn, 0);
          Node lem = d_tds->getExplain()->getExplanationForEquality(x, exc_sol);
          lem = lem.negate();
          Trace("sygus-rr-sb") << "Symmetry breaking lemma : " << lem
                               << std::endl;
          d_tds->registerSymBreakLemma(d_candidate, lem, ptn, sz);
        }
      }
      // If we failed to verify, then we return the original term. This is done
      // so that the user of this method is not told of a rewrite rule that
      // may not hold. Furthermore, note that the term is not added to the lazy
      // trie in the sygus sampler. This means that the set of rewrites is not
      // complete, as we are discarding the current solution. Ideally, we would
      // store a list of terms (that are pairwise unknown to be equal) at each
      // leaf of the lazy trie.
      if (!verified)
      {
        eq_sol = sol;
      }
    }
    // We count this as a rewrite if we did not explicitly rule it out.
    // The value of is_unique_term is false iff this call resulted in a rewrite.
    // Notice that when --sygus-rr-synth-check is enabled,
    // statistics on number of candidate rewrite rules is
    // an accurate count of (#enumerated_terms-#unique_terms) only if
    // the option sygus-rr-synth-filter-order is disabled. The reason
    // is that the sygus sampler may reason that a candidate rewrite
    // rule is not useful since its variables are unordered, whereby
    // it discards it as a redundant candidate rewrite rule before
    // checking its correctness.
  }
  d_add_term_cache[sol] = eq_sol;
  return eq_sol;
}

bool CandidateRewriteDatabase::addTerm(Node sol, std::vector<Node>& rewrites)
{
  Node rsol = addOrGetTerm(sol, rewrites);
  return sol == rsol;
}

void CandidateRewriteDatabase::enableExtendedRewriter()
{
  d_useExtRewriter = true;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
