/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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
#include "smt/smt_statistics_registry.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/rewriter.h"
#include "theory/smt_engine_subsolver.h"

using namespace cvc5::kind;
using namespace std;

namespace cvc5 {
namespace theory {
namespace quantifiers {

SynthVerify::SynthVerify(Env& env, TermDbSygus* tds)
    : EnvObj(env), d_tds(tds), d_subLogicInfo(logicInfo())
{
  // determine the options to use for the verification subsolvers we spawn
  // we start with the provided options
  d_subOptions.copyValues(options());
  // limit the number of instantiation rounds on subcalls
  d_subOptions.quantifiers.instMaxRounds =
      d_subOptions.quantifiers.sygusVerifyInstMaxRounds;
  // Disable sygus on the subsolver. This is particularly important since it
  // ensures that recursive function definitions have the standard ownership
  // instead of being claimed by sygus in the subsolver.
  d_subOptions.base.inputLanguage = Language::LANG_SMTLIB_V2_6;
  d_subOptions.quantifiers.sygus = false;
  // use tangent planes by default, since we want to put effort into
  // the verification step for sygus queries with non-linear arithmetic
  if (!d_subOptions.arith.nlExtTangentPlanesWasSetByUser)
  {
    d_subOptions.arith.nlExtTangentPlanes = true;
  }
  // we must use the same setting for datatype selectors, since shared selectors
  // can appear in solutions
  d_subOptions.datatypes.dtSharedSelectors =
      options().datatypes.dtSharedSelectors;
  d_subOptions.datatypes.dtSharedSelectorsWasSetByUser = true;
}

SynthVerify::~SynthVerify() {}

Result SynthVerify::verify(Node query,
                           const std::vector<Node>& vars,
                           std::vector<Node>& mvs)
{
  NodeManager* nm = NodeManager::currentNM();
  // simplify the lemma based on the term database sygus utility
  query = d_tds->rewriteNode(query);
  // eagerly unfold applications of evaluation function
  Trace("cegqi-debug") << "pre-unfold counterexample : " << query << std::endl;

  if (query.isConst())
  {
    if (!query.getConst<bool>())
    {
      return Result(Result::UNSAT);
    }
    // sat, but we need to get arbtirary model values below
  }
  else
  {
    // if non-constant, we may need to add recursive function definitions
    FunDefEvaluator* feval = d_tds->getFunDefEvaluator();
    const std::vector<Node>& fdefs = feval->getDefinitions();
    if (!fdefs.empty())
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
        Node q = feval->getDefinitionFor(f);
        if (!q.isNull())
        {
          qconj.push_back(q);
        }
      }
      query = nm->mkAnd(qconj);
      Trace("cegqi-debug") << "query is " << query << std::endl;
    }
  }
  Trace("sygus-engine") << "  *** Verify with subcall..." << std::endl;
  query = rewrite(query);
  Result r = checkWithSubsolver(query, vars, mvs, d_subOptions, d_subLogicInfo);
  Trace("sygus-engine") << "  ...got " << r << std::endl;
  if (r.asSatisfiabilityResult().isSat() == Result::SAT)
  {
    if (Trace.isOn("sygus-engine"))
    {
      Trace("sygus-engine") << "  * Verification lemma failed for:\n   ";
      for (unsigned i = 0, size = vars.size(); i < size; i++)
      {
        Trace("sygus-engine") << vars[i] << " -> " << mvs[i] << " ";
      }
      Trace("sygus-engine") << std::endl;
    }
    if (Configuration::isAssertionBuild())
    {
      // the values for the query should be a complete model
      Node squery =
          query.substitute(vars.begin(), vars.end(), mvs.begin(), mvs.end());
      Trace("cegqi-debug") << "...squery : " << squery << std::endl;
      squery = rewrite(squery);
      Trace("cegqi-debug") << "...rewrites to : " << squery << std::endl;
      Assert(options().quantifiers.sygusRecFun
             || (squery.isConst() && squery.getConst<bool>()));
    }
  }
  return r;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
