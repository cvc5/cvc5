/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of candidate_rewrite_database.
 */

#include "theory/quantifiers/candidate_rewrite_database.h"

#include "options/base_options.h"
#include "printer/printer.h"
#include "smt/smt_statistics_registry.h"
#include "smt/solver_engine.h"
#include "smt/solver_engine_scope.h"
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
    Env& env, bool doCheck, bool rewAccel, bool silent, bool filterPairs)
    : ExprMiner(env),
      d_tds(nullptr),
      d_useExtRewriter(false),
      d_doCheck(doCheck),
      d_rewAccel(rewAccel),
      d_silent(silent),
      d_filterPairs(filterPairs),
      d_using_sygus(false),
      d_crewrite_filter(env)
{
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

Node CandidateRewriteDatabase::addTerm(Node sol,
                                       bool rec,
                                       std::ostream& out,
                                       bool& rew_print)
{
  // have we added this term before?
  std::unordered_map<Node, Node>::iterator itac = d_add_term_cache.find(sol);
  if (itac != d_add_term_cache.end())
  {
    return itac->second;
  }

  if (rec)
  {
    // if recursive, we first add all subterms
    for (const Node& solc : sol)
    {
      // whether a candidate rewrite is printed for any subterm is irrelevant
      bool rew_printc = false;
      addTerm(solc, rec, out, rew_printc);
    }
  }
  // register the term
  bool is_unique_term = true;
  Node eq_sol = d_sampler->registerTerm(sol);
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
        std::unique_ptr<SolverEngine> rrChecker;
        initializeChecker(rrChecker, crr);
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
          Assert(eq_sol == sol);
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
        if (!d_silent)
        {
          out << "(" << (verified ? "" : "candidate-") << "rewrite ";
          if (d_using_sygus)
          {
            TermDbSygus::toStreamSygus(out, sol);
            out << " ";
            TermDbSygus::toStreamSygus(out, eq_sol);
          }
          else
          {
            out << sol << " " << eq_sol;
          }
          out << ")" << std::endl;
        }
        // we count this as printed, despite not literally printing it
        rew_print = true;
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

Node CandidateRewriteDatabase::addTerm(Node sol, bool rec, std::ostream& out)
{
  bool rew_print = false;
  return addTerm(sol, rec, out, rew_print);
}
bool CandidateRewriteDatabase::addTerm(Node sol, std::ostream& out)
{
  Node rsol = addTerm(sol, false, out);
  return sol == rsol;
}

void CandidateRewriteDatabase::setSilent(bool flag) { d_silent = flag; }

void CandidateRewriteDatabase::enableExtendedRewriter()
{
  d_useExtRewriter = true;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
