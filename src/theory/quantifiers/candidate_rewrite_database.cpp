/*********************                                                        */
/*! \file candidate_rewrite_database.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of candidate_rewrite_database
 **/

#include "theory/quantifiers/candidate_rewrite_database.h"

#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "printer/printer.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "smt/smt_statistics_registry.h"
#include "theory/quantifiers/sygus/ce_guided_instantiation.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"

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
      d_using_sygus(false)
{
}
void CandidateRewriteDatabase::initialize(ExtendedRewriter* er,
                                          TypeNode tn,
                                          std::vector<Node>& vars,
                                          unsigned nsamples,
                                          bool unique_type_ids)
{
  d_candidate = Node::null();
  d_type = tn;
  d_using_sygus = false;
  d_qe = nullptr;
  d_tds = nullptr;
  d_ext_rewrite = er;
  d_sampler.initialize(tn, vars, nsamples, unique_type_ids);
  d_crewrite_filter.initialize(&d_sampler, nullptr, false);
}

void CandidateRewriteDatabase::initializeSygus(QuantifiersEngine* qe,
                                               Node f,
                                               unsigned nsamples,
                                               bool useSygusType)
{
  d_candidate = f;
  d_type = f.getType();
  Assert(d_type.isDatatype());
  Assert(static_cast<DatatypeType>(d_type.toType()).getDatatype().isSygus());
  d_using_sygus = true;
  d_qe = qe;
  d_tds = d_qe->getTermDatabaseSygus();
  d_ext_rewrite = d_tds->getExtRewriter();
  d_sampler.initializeSygus(d_tds, f, nsamples, useSygusType);
  d_crewrite_filter.initialize(&d_sampler, d_tds, true);
}

bool CandidateRewriteDatabase::addTerm(Node sol,
                                       std::ostream& out,
                                       bool& rew_print)
{
  bool is_unique_term = true;
  Node eq_sol = d_sampler.registerTerm(sol);
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
        NodeManager* nm = NodeManager::currentNM();

        Node crr = solbr.eqNode(eq_solr).negate();
        Trace("rr-check") << "Check candidate rewrite : " << crr << std::endl;
        // quantify over the free variables in crr
        std::vector<Node> fvs;
        TermUtil::computeVarContains(crr, fvs);
        std::map<Node, unsigned> fv_index;
        std::vector<Node> sks;
        if (!fvs.empty())
        {
          // map to skolems
          for (unsigned i = 0, size = fvs.size(); i < size; i++)
          {
            Node v = fvs[i];
            fv_index[v] = i;
            std::map<Node, Node>::iterator itf = d_fv_to_skolem.find(v);
            if (itf == d_fv_to_skolem.end())
            {
              Node sk = nm->mkSkolem("rrck", v.getType());
              d_fv_to_skolem[v] = sk;
              sks.push_back(sk);
            }
            else
            {
              sks.push_back(itf->second);
            }
          }
          crr = crr.substitute(fvs.begin(), fvs.end(), sks.begin(), sks.end());
        }

        // Notice we don't set produce-models. rrChecker takes the same
        // options as the SmtEngine we belong to, where we ensure that
        // produce-models is set.
        bool needExport = true;
        ExprManagerMapCollection varMap;
        ExprManager em(nm->getOptions());
        std::unique_ptr<SmtEngine> rrChecker;
        Result r;
        if (options::sygusRewSynthCheckTimeout.wasSetByUser())
        {
          // To support a separate timeout for the subsolver, we need to create
          // a separate ExprManager with its own options. This requires that
          // the expressions sent to the subsolver can be exported from on
          // ExprManager to another. If the export fails, we throw an
          // OptionException.
          try
          {
            rrChecker.reset(new SmtEngine(&em));
            rrChecker->setTimeLimit(options::sygusRewSynthCheckTimeout(), true);
            rrChecker->setLogic(smt::currentSmtEngine()->getLogicInfo());
            Expr eccr = crr.toExpr().exportTo(&em, varMap);
            rrChecker->assertFormula(eccr);
            r = rrChecker->checkSat();
          }
          catch (const CVC4::ExportUnsupportedException& e)
          {
            std::stringstream msg;
            msg << "Unable to export " << crr
                << " but exporting expressions is required for "
                   "--sygus-rr-synth-check-timeout.";
            throw OptionException(msg.str());
          }
        }
        else
        {
          needExport = false;
          rrChecker.reset(new SmtEngine(nm->toExprManager()));
          rrChecker->assertFormula(crr.toExpr());
          r = rrChecker->checkSat();
        }

        Trace("rr-check") << "...result : " << r << std::endl;
        if (r.asSatisfiabilityResult().isSat() == Result::SAT)
        {
          Trace("rr-check") << "...rewrite does not hold for: " << std::endl;
          is_unique_term = true;
          std::vector<Node> vars;
          d_sampler.getVariables(vars);
          std::vector<Node> pt;
          for (const Node& v : vars)
          {
            Node val;
            Node refv = v;
            // if a bound variable, map to the skolem we introduce before
            // looking up the model value
            if (v.getKind() == BOUND_VARIABLE)
            {
              std::map<Node, unsigned>::iterator itf = fv_index.find(v);
              if (itf == fv_index.end())
              {
                // not in conjecture, can use arbitrary value
                val = v.getType().mkGroundTerm();
              }
              else
              {
                // get the model value of its skolem
                refv = sks[itf->second];
              }
            }
            if (val.isNull())
            {
              Assert(!refv.isNull() && refv.getKind() != BOUND_VARIABLE);
              if (needExport)
              {
                Expr erefv = refv.toExpr().exportTo(&em, varMap);
                val = Node::fromExpr(rrChecker->getValue(erefv).exportTo(
                    nm->toExprManager(), varMap));
              }
              else
              {
                val = Node::fromExpr(rrChecker->getValue(refv.toExpr()));
              }
            }
            Trace("rr-check") << "  " << v << " -> " << val << std::endl;
            pt.push_back(val);
          }
          d_sampler.addSamplePoint(pt);
          // add the solution again
          // by construction of the above point, we should be unique now
          Node eq_sol_new = d_sampler.registerTerm(sol);
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
  return is_unique_term;
}

bool CandidateRewriteDatabase::addTerm(Node sol, std::ostream& out)
{
  bool rew_print = false;
  return addTerm(sol, out, rew_print);
}

CandidateRewriteDatabaseGen::CandidateRewriteDatabaseGen(
    std::vector<Node>& vars, unsigned nsamples)
    : d_vars(vars.begin(), vars.end()), d_nsamples(nsamples)
{
}

bool CandidateRewriteDatabaseGen::addTerm(Node n, std::ostream& out)
{
  ExtendedRewriter* er = nullptr;
  if (options::synthRrPrepExtRew())
  {
    er = &d_ext_rewrite;
  }
  Node nr;
  if (er == nullptr)
  {
    nr = Rewriter::rewrite(n);
  }
  else
  {
    nr = er->extendedRewrite(n);
  }
  TypeNode tn = nr.getType();
  std::map<TypeNode, CandidateRewriteDatabase>::iterator itc = d_cdbs.find(tn);
  if (itc == d_cdbs.end())
  {
    Trace("synth-rr-dbg") << "Initialize database for " << tn << std::endl;
    // initialize with the extended rewriter owned by this class
    d_cdbs[tn].initialize(er, tn, d_vars, d_nsamples, true);
    itc = d_cdbs.find(tn);
    Trace("synth-rr-dbg") << "...finish." << std::endl;
  }
  Trace("synth-rr-dbg") << "Add term " << nr << " for " << tn << std::endl;
  return itc->second.addTerm(nr, out);
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
