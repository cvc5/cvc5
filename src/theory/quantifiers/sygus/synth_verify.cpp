/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Abdalrhman Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Class for verifying queries for synthesis solutions
 */

#include "theory/quantifiers/sygus/synth_verify.h"

#include "expr/node_algorithm.h"
#include "options/arith_options.h"
#include "options/base_options.h"
#include "options/datatypes_options.h"
#include "options/quantifiers_options.h"
#include "smt/set_defaults.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/rewriter.h"
#include "theory/smt_engine_subsolver.h"

using namespace cvc5::internal::kind;
using namespace std;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

SynthVerify::SynthVerify(Env& env, TermDbSygus* tds)
    : EnvObj(env), d_tds(tds), d_subLogicInfo(logicInfo())
{
  // determine the options to use for the verification subsolvers we spawn
  // we start with the provided options
  d_subOptions.copyValues(options());
  // limit the number of instantiation rounds on subcalls
  d_subOptions.writeQuantifiers().instMaxRounds =
      d_subOptions.quantifiers.sygusVerifyInstMaxRounds;
  // Disable sygus on the subsolver. This is particularly important since it
  // ensures that recursive function definitions have the standard ownership
  // instead of being claimed by sygus in the subsolver.
  d_subOptions.writeBase().inputLanguage = Language::LANG_SMTLIB_V2_6;
  d_subOptions.writeQuantifiers().sygus = false;
  // use tangent planes by default, since we want to put effort into
  // the verification step for sygus queries with non-linear arithmetic
  if (!d_subOptions.arith.nlExtTangentPlanesWasSetByUser)
  {
    d_subOptions.writeArith().nlExtTangentPlanes = true;
  }
  // we must use the same setting for datatype selectors, since shared selectors
  // can appear in solutions
  d_subOptions.writeDatatypes().dtSharedSelectors =
      options().datatypes.dtSharedSelectors;
  d_subOptions.writeDatatypes().dtSharedSelectorsWasSetByUser = true;
  // disable checking
  smt::SetDefaults::disableChecking(d_subOptions);
}

SynthVerify::~SynthVerify() {}

Result SynthVerify::verify(Node query,
                           const std::vector<Node>& vars,
                           std::vector<Node>& mvs)
{
  Node queryp = preprocessQueryInternal(query);
  bool finished;
  Result r;
  do
  {
    Trace("sygus-engine") << "  *** Verify with subcall..." << std::endl;
    if (queryp.isConst())
    {
      if (!queryp.getConst<bool>())
      {
        return Result(Result::UNSAT);
      }
      else if (vars.empty())
      {
        return Result(Result::SAT);
      }
      // sat, but we need to get arbtirary model values below
    }
    SubsolverSetupInfo ssi(d_subOptions,
                           d_subLogicInfo,
                           d_env.getSepLocType(),
                           d_env.getSepDataType());
    r = checkWithSubsolver(queryp,
                           vars,
                           mvs,
                           ssi,
                           options().quantifiers.sygusVerifyTimeout != 0,
                           options().quantifiers.sygusVerifyTimeout);
    finished = true;
    Trace("sygus-engine") << "  ...got " << r << std::endl;
    // we try to learn models for "sat" and "unknown" here
    if (r.getStatus() != Result::UNSAT)
    {
      if (TraceIsOn("sygus-engine"))
      {
        Trace("sygus-engine") << "  * Verification lemma failed for:\n   ";
        for (unsigned i = 0, size = vars.size(); i < size; i++)
        {
          Trace("sygus-engine") << vars[i] << " -> " << mvs[i] << " ";
        }
        Trace("sygus-engine") << std::endl;
      }
      // check whether the query is satisfied by the model
      if (options().quantifiers.oracles || Configuration::isAssertionBuild())
      {
        Assert(vars.size() == mvs.size());
        // the values for the query should be a complete model
        Node squery =
            query.substitute(vars.begin(), vars.end(), mvs.begin(), mvs.end());
        Trace("cegqi-debug") << "...squery : " << squery << std::endl;
        // Rewrite the node. Notice that if squery contains oracle function
        // symbols, then this may trigger new calls to oracles.
        squery = d_tds->rewriteNode(squery);
        Trace("cegqi-debug") << "...rewrites to : " << squery << std::endl;
        if (!squery.isConst() || !squery.getConst<bool>())
        {
          // If the query did not simplify to true, then it may be that the
          // value for an oracle function was not what we expected.
          if (options().quantifiers.oracles)
          {
            // In this case, we reconstruct the query, which may include more
            // information about oracles than we had previously, due to the
            // call to rewriteNode above. We rerun the satisfiability check
            // above, which now may conjoin more I/O pairs to the preprocessed
            // query.
            Node nextQueryp = preprocessQueryInternal(query);
            if (nextQueryp != queryp)
            {
              queryp = nextQueryp;
              finished = false;
            }
          }
          else if (squery.isConst())
          {
            // simplified to false, the result should have been unknown, or
            // else this indicates a check-model failure. We check this only
            // if oracles are disabled.
            Assert(r.getStatus() == Result::UNKNOWN)
                << "Expected model from verification step to satisfy query";
          }
        }
      }
    }
  } while (!finished);
  return r;
}

Result SynthVerify::verify(Node query)
{
  std::vector<Node> vars;
  std::vector<Node> mvs;
  return verify(query, vars, mvs);
}

Node SynthVerify::preprocessQueryInternal(Node query)
{
  NodeManager* nm = NodeManager::currentNM();
  Trace("cegqi-debug") << "pre-rewritten query : " << query << std::endl;
  // simplify the lemma based on the term database sygus utility
  query = d_tds->rewriteNode(query);
  // eagerly unfold applications of evaluation function
  Trace("cegqi-debug") << "post-rewritten query : " << query << std::endl;
  if (!query.isConst())
  {
    // if non-constant, we may need to add recursive function definitions
    FunDefEvaluator* feval = d_tds->getFunDefEvaluator();
    OracleChecker* ochecker = d_tds->getOracleChecker();
    const std::vector<Node>& fdefs = feval->getDefinitions();
    if (!fdefs.empty() || (ochecker != nullptr && ochecker->hasOracles()))
    {
      // Get the relevant definitions based on the symbols in the query.
      // Notice in some cases, this may have the effect of making the subcall
      // involve no recursive function definitions at all, in which case the
      // subcall to verification may be decidable, in which case the call
      // below is guaranteed to generate a new counterexample point.
      std::unordered_set<Node> syms;
      expr::getSymbols(query, syms);
      std::vector<Node> qconj;
      qconj.push_back(query);
      for (const Node& f : syms)
      {
        // get the function definition
        Node q = feval->getDefinitionFor(f);
        if (!q.isNull())
        {
          qconj.push_back(q);
        }
        // Get the relevant cached oracle calls.
        // In contrast to the presentation in Polgreen et al VMCAI 2022,
        // we do not use SMTO as a subsolver for SyMO here. Instead, we
        // conjoin the set of I/O pairs known about each oracle function
        // to the query.
        if (ochecker != nullptr && ochecker->hasOracleCalls(f))
        {
          const std::map<Node, std::vector<Node>>& ocalls =
              ochecker->getOracleCalls(f);
          for (const std::pair<const Node, std::vector<Node>>& oc : ocalls)
          {
            // we ignore calls that had a size other than one
            if (oc.second.size() == 1)
            {
              qconj.push_back(oc.first.eqNode(oc.second[0]));
            }
          }
        }
      }
      query = nm->mkAnd(qconj);
      Trace("cegqi-debug")
          << "after function definitions + oracle calls, query is " << query
          << std::endl;
    }
  }
  return query;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
