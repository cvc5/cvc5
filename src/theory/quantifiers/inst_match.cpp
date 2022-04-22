/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of inst match class.
 */

#include "theory/quantifiers/inst_match.h"

#include "theory/quantifiers/quantifiers_state.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

InstMatch::InstMatch(TNode q) : d_quant(q)
{
  d_vals.resize(q[0].getNumChildren());
  Assert(!d_vals.empty());
  // resize must initialize with null nodes
  Assert(d_vals[0].isNull());
}

InstMatch::InstMatch(InstMatch* m) : d_quant(m->d_quant)
{
  d_vals.insert( d_vals.end(), m->d_vals.begin(), m->d_vals.end() );
}

void InstMatch::add(InstMatch& m)
{
  for (unsigned i = 0, size = d_vals.size(); i < size; i++)
  {
    if( d_vals[i].isNull() ){
      d_vals[i] = m.d_vals[i];
    }
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

void InstMatch::clear() {
  for( unsigned i=0; i<d_vals.size(); i++ ){
    d_vals[i] = Node::null();
  }
}

Node InstMatch::get(size_t i) const
{
  Assert(i < d_vals.size());
  return d_vals[i];
}

void InstMatch::setValue(size_t i, TNode n)
{
  Assert(i < d_vals.size());
  d_vals[i] = n;
}

bool InstMatch::set(QuantifiersState& qs, size_t i, TNode n)
{
  Assert(i < d_vals.size());
  if (!d_vals[i].isNull())
  {
    // if they are equal, we do nothing
    return qs.areEqual(d_vals[i], n);
  }
  // TODO: check if we have already learned this failure?
  // TODO: if applicable, check if the instantiation evaluator is ok
  // TODO: if not, learn the failure?

  // otherwise, we update the value
  d_vals[i] = n;
  return true;
}

void InstMatch::reset(size_t i) 
{ 
  Assert (!d_vals[i].isNull());
  d_vals[i] = Node::null();
}

std::vector<Node>& InstMatch::get() { return d_vals; }

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
