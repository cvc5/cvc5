/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility for verifying models.
 */

#include "smt/model_verifier.h"

#include "expr/node_algorithm.h"
#include "smt/env.h"
#include "smt/expand_definitions.h"
#include "theory/theory_model.h"
#include "theory/trust_substitutions.h"

using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace smt {

ModelVerifier::ModelVerifier(Env& e) : EnvObj(e) {}

bool ModelVerifier::verify(TheoryModel* m, const context::CDList<Node>& al)
{
  Trace("model-verify") << "ModelVerifier: verify model" << std::endl;
  Node sepHeap, sepNeq;
  if (m->getHeapModel(sepHeap, sepNeq))
  {
    // we do not verify models involving a separation logic heap
    Trace("model-verify") << "...fail: separation logic heap" << std::endl;
    return false;
  }
  // expand definitions module and substitutions
  ExpandDefs expDef(d_env);
  std::unordered_map<Node, Node> cache;
  SubstitutionMap& sm = d_env.getTopLevelSubstitutions().get();
  for (const Node& assertion : al)
  {
    Trace("model-verify") << "check assertion " << assertion << std::endl;
    // Apply the top-level substitutions, which includes the definitions
    // introduced by define-fun, as well as the substitutions learned during
    // preprocessing. Note that the model values we use below are computed
    // modulo these substitutions as well.
    Node n = sm.apply(assertion);
    // Expand definitions, which is required for being accurate for operators
    // that expand involving skolems during preprocessing.
    n = expDef.expandDefinitions(n, cache);
    n = rewrite(n);
    if (n.isConst() && n.getConst<bool>())
    {
      // trivially satisfied
      continue;
    }
    // get the model values of the symbols of n
    if (!addModelValues(m, n))
    {
      return false;
    }
    // The assertion is satisfied if replacing its symbols by their model
    // values results in a formula that rewrites to true.
    Node nv = rewrite(d_mvs.apply(n));
    if (!nv.isConst() || !nv.getConst<bool>())
    {
      Trace("model-verify") << "...fail: assertion " << assertion
                            << " evaluates to " << nv << std::endl;
      return false;
    }
  }
  Trace("model-verify") << "...success" << std::endl;
  return true;
}

bool ModelVerifier::addModelValues(TheoryModel* m, const Node& n)
{
  std::unordered_set<Node> syms;
  expr::getSymbols(n, syms);
  for (const Node& s : syms)
  {
    if (!d_processed.insert(s).second)
    {
      // already computed the model value of this symbol
      continue;
    }
    Node v = m->getValue(s);
    // The value must be a model value, e.g. a constant or a lambda. Otherwise
    // we do not know how to interpret the symbol.
    if (v.isNull() || !m->isValue(v))
    {
      Trace("model-verify")
          << "...fail: no model value for " << s << ", got " << v << std::endl;
      return false;
    }
    // It furthermore must be closed, so that the substitution below is
    // guaranteed to eliminate all symbols, and so that the value does not
    // depend on the context it is substituted into.
    std::unordered_set<Node> vsyms;
    expr::getSymbols(v, vsyms);
    if (!vsyms.empty() || expr::hasFreeVar(v))
    {
      Trace("model-verify") << "...fail: model value " << v << " for " << s
                            << " is not closed" << std::endl;
      return false;
    }
    d_mvs.add(s, v);
  }
  return true;
}

}  // namespace smt
}  // namespace cvc5::internal
