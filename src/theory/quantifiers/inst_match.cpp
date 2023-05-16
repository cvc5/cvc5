/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of inst match class.
 */

#include "theory/quantifiers/inst_match.h"

#include "options/quantifiers_options.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_registry.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

InstMatch::InstMatch(Env& env, QuantifiersState& qs, TermRegistry& tr, TNode q)
    : EnvObj(env), d_qs(qs), d_tr(tr), d_quant(q), d_ieval(nullptr)
{
  d_vals.resize(q[0].getNumChildren());
  Assert(!d_vals.empty());
  // resize must initialize with null nodes
  Assert(d_vals[0].isNull());
}

void InstMatch::setEvaluatorMode(ieval::TermEvaluatorMode tev)
{
  // should only do this if we are empty
  Assert(empty());
  // get the instantiation evaluator and reset it
  d_ieval = d_tr.getEvaluator(d_quant, tev);
  if (d_ieval != nullptr)
  {
    d_ieval->resetAll();
  }
}

void InstMatch::debugPrint( const char* c ){
  for (unsigned i = 0, size = d_vals.size(); i < size; i++)
  {
    if( !d_vals[i].isNull() ){
      Trace( c ) << "   " << i << " -> " << d_vals[i] << std::endl;
    }
  }
}

void InstMatch::toStream(std::ostream& out) const
{
  out << "INST_MATCH( ";
  bool printed = false;
  for (size_t i = 0, size = d_vals.size(); i < size; i++)
  {
    if (!d_vals[i].isNull())
    {
      if (printed)
      {
        out << ", ";
      }
      out << i << " -> " << d_vals[i];
      printed = true;
    }
  }
  out << " )";
}

bool InstMatch::isComplete() const
{
  for (const Node& v : d_vals)
  {
    if (v.isNull())
    {
      return false;
    }
  }
  return true;
}

bool InstMatch::empty() const
{
  for (const Node& v : d_vals)
  {
    if (!v.isNull())
    {
      return false;
    }
  }
  return true;
}

void InstMatch::resetAll()
{
  for (size_t i = 0, nvals = d_vals.size(); i < nvals; i++)
  {
    d_vals[i] = Node::null();
  }
  // clear information from the evaluator
  if (d_ieval != nullptr)
  {
    d_ieval->resetAll();
  }
}

Node InstMatch::get(size_t i) const
{
  Assert(i < d_vals.size());
  return d_vals[i];
}

bool InstMatch::set(size_t i, TNode n)
{
  Assert(i < d_vals.size());
  if (!d_vals[i].isNull())
  {
    // if they are equal, we do nothing
    return d_qs.areEqual(d_vals[i], n);
  }
  if (d_ieval != nullptr)
  {
    // if applicable, check if the instantiation evaluator is ok
    if (!d_ieval->push(d_quant[0][i], n))
    {
      return false;
    }
  }
  // otherwise, we update the value
  d_vals[i] = n;
  return true;
}

void InstMatch::reset(size_t i)
{
  Assert(!d_vals[i].isNull());
  if (d_ieval != nullptr)
  {
    d_ieval->pop();
  }
  d_vals[i] = Node::null();
}

const std::vector<Node>& InstMatch::get() const { return d_vals; }

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
