/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A cache to remember what is justified
 */

#include "decision/justify_cache.h"

#include "expr/node_algorithm.h"

using namespace cvc5::internal::kind;
using namespace cvc5::internal::prop;

namespace cvc5::internal {
namespace decision {

JustifyCache::JustifyCache(context::Context* c,
                           prop::CDCLTSatSolver* ss,
                           prop::CnfStream* cs)
    : d_justified(c), d_satSolver(ss), d_cnfStream(cs)
{
}

prop::SatValue JustifyCache::lookupValue(TNode n)
{
  bool pol = n.getKind() != NOT;
  TNode atom = pol ? n : n[0];
  Assert(atom.getKind() != NOT);
  // check if we have already determined the value
  // notice that d_justified may contain nodes that are not assigned SAT values,
  // since this class infers when the value of nodes can be determined.
  auto jit = d_justified.find(atom);
  if (jit != d_justified.end())
  {
    return pol ? jit->second : invertValue(jit->second);
  }
  // Notice that looking up values for non-theory atoms may lead to
  // an incomplete strategy where a formula is asserted but not justified
  // via its theory literal subterms. This is the case because the justification
  // heuristic is not the only source of decisions, as the theory may request
  // them.
  if (expr::isTheoryAtom(atom))
  {
    SatLiteral nsl = d_cnfStream->getLiteral(atom);
    prop::SatValue val = d_satSolver->value(nsl);
    if (val != SAT_VALUE_UNKNOWN)
    {
      // this is the moment where we realize a skolem definition is relevant,
      // add now.
      // NOTE: if we enable skolems when they are justified, we could call
      // a method notifyJustified(atom) here
      d_justified.insert(atom, val);
      return pol ? val : invertValue(val);
    }
  }
  return SAT_VALUE_UNKNOWN;
}

bool JustifyCache::hasValue(TNode n) const
{
  return d_justified.find(n) != d_justified.end();
}

void JustifyCache::setValue(const Node& n, prop::SatValue value)
{
  d_justified.insert(n, value);
}

}  // namespace decision
}  // namespace cvc5::internal
