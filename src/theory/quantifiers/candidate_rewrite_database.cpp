/*********************                                                        */
/*! \file candidate_rewrite_database.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of candidate_rewrite_database
 **/

#include "theory/quantifiers/candidate_rewrite_database.h"

#include "api/cvc4cpp.h"
#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "printer/printer.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "smt/smt_statistics_registry.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers_engine.h"

using namespace std;
using namespace CVC4::kind;
using namespace CVC4::context;

namespace CVC4 {
namespace theory {
namespace quantifiers {

CandidateRewriteDatabase::CandidateRewriteDatabase()
    : d_qe(nullptr),
      d_tds(nullptr),
      d_ext_rewrite(nullptr),
      d_using_sygus(false),
      d_silent(false)
{
}
void CandidateRewriteDatabase::initialize(const std::vector<Node>& vars,
                                          SygusSampler* ss)
{
  Assert(ss != nullptr);
  d_candidate = Node::null();
  d_using_sygus = false;
  d_qe = nullptr;
  d_tds = nullptr;
  d_ext_rewrite = nullptr;
  d_crewrite_filter.initialize(ss, nullptr, false);
  ExprMiner::initialize(vars, ss);
}

void CandidateRewriteDatabase::initializeSygus(const std::vector<Node>& vars,
                                               QuantifiersEngine* qe,
                                               Node f,
                                               SygusSampler* ss)
{
  Assert(ss != nullptr);
  d_candidate = f;
  d_using_sygus = true;
  d_qe = qe;
  d_tds = d_qe->getTermDatabaseSygus();
  d_ext_rewrite = nullptr;
  d_crewrite_filter.initialize(ss, d_tds, d_using_sygus);
  ExprMiner::initialize(vars, ss);
}

bool CandidateRewriteDatabase::addTerm(Node sol,
                                       bool rec,
                                       std::ostream& out,
                                       bool& rew_print)
{
  // have we added this term before?
  std::unordered_map<Node, bool, NodeHashFunction>::iterator itac =
      d_add_term_cache.find(sol);
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
    if (!d_crewrite_filter.filterPair(sol, eq_sol))
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
      if (d_ext_rewrite != nullptr)
      {
        solbr = d_ext_rewrite->extendedRewrite(solb);
        eq_solr = d_ext_rewrite->extendedRewrite(eq_solb);
      }
      else
      {
        solbr = Rewriter::rewrite(solb);
        eq_solr = Rewriter::rewrite(eq_solb);
      }
      bool verified = false;
      Trace("rr-check") << "Check candidate rewrite..." << std::endl;
      // verify it if applicable
      if (options::sygusRewSynthCheck())
      {
        Node crr = solbr.eqNode(eq_solr).negate();
        Trace("rr-check") << "Check candidate rewrite : " << crr << std::endl;

        // Notice we don't set produce-models. rrChecker takes the same
        // options as the SmtEngine we belong to, where we ensure that
        // produce-models is set.
        std::unique_ptr<SmtEngine> rrChecker;
        initializeChecker(rrChecker, crr);
        Result r = rrChecker->checkSat();
        Trace("rr-check") << "...result : " << r << std::endl;
        if (r.asSatisfiabilityResult().isSat() == Result::SAT)
        {
          Trace("rr-check") << "...rewrite does not hold for: " << std::endl;
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
                val = v.getType().mkGroundTerm();
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
              val = Node::fromExpr(rrChecker->getValue(refv.toExpr()));
            }
            Trace("rr-check") << "  " << v << " -> " << val << std::endl;
            pt.push_back(val);
          }
          d_sampler->addSamplePoint(pt);
          // add the solution again
          // by construction of the above point, we should be unique now
          Node eq_sol_new = d_sampler->registerTerm(sol);
          Assert(eq_sol_new == sol);
        }
        else
        {
          verified = !r.asSatisfiabilityResult().isUnknown();
        }
      }
      else
      {
        // just insist that constants are not relevant pairs
        is_unique_term = solb.isConst() && eq_solb.isConst();
      }
      if (!is_unique_term)
      {
        // register this as a relevant pair (helps filtering)
        d_crewrite_filter.registerRelevantPair(sol, eq_sol);
        // The analog of terms sol and eq_sol are equivalent under
        // sample points but do not rewrite to the same term. Hence,
        // this indicates a candidate rewrite.
        if (!d_silent)
        {
          out << "(" << (verified ? "" : "candidate-") << "rewrite ";
          if (d_using_sygus)
          {
            Printer* p = Printer::getPrinter(options::outputLanguage());
            p->toStreamSygus(out, sol);
            out << " ";
            p->toStreamSygus(out, eq_sol);
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
        if (Trace.isOn("sygus-rr-debug"))
        {
          Trace("sygus-rr-debug") << "; candidate #1 ext-rewrites to: " << solbr
                                  << std::endl;
          Trace("sygus-rr-debug")
              << "; candidate #2 ext-rewrites to: " << eq_solr << std::endl;
        }
        if (options::sygusRewSynthAccel() && d_using_sygus)
        {
          Assert(d_tds != nullptr);
          // Add a symmetry breaking clause that excludes the larger
          // of sol and eq_sol. This effectively states that we no longer
          // wish to enumerate any term that contains sol (resp. eq_sol)
          // as a subterm.
          Node exc_sol = sol;
          unsigned sz = d_tds->getSygusTermSize(sol);
          unsigned eqsz = d_tds->getSygusTermSize(eq_sol);
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
  d_add_term_cache[sol] = is_unique_term;
  return is_unique_term;
}

bool CandidateRewriteDatabase::addTerm(Node sol, bool rec, std::ostream& out)
{
  bool rew_print = false;
  return addTerm(sol, rec, out, rew_print);
}
bool CandidateRewriteDatabase::addTerm(Node sol, std::ostream& out)
{
  return addTerm(sol, false, out);
}

void CandidateRewriteDatabase::setSilent(bool flag) { d_silent = flag; }

void CandidateRewriteDatabase::setExtendedRewriter(ExtendedRewriter* er)
{
  d_ext_rewrite = er;
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
