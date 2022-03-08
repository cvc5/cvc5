/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Francois Bobot
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of inst match class.
 */

#include "theory/quantifiers/inst_match.h"

#include "theory/quantifiers/quantifiers_state.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

InstMatch::InstMatch(TNode q)
{
  d_vals.resize(q[0].getNumChildren());
  Assert(!d_vals.empty());
  // resize must initialize with null nodes
  Assert(d_vals[0].isNull());
}

InstMatch::InstMatch( InstMatch* m ) {
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
      Debug( c ) << "   " << i << " -> " << d_vals[i] << std::endl;
    }
  }
}

bool InstMatch::isComplete() {
  for (Node& v : d_vals)
  {
    if (v.isNull())
    {
      return false;
    }
  }
  return true;
}

bool InstMatch::empty() {
  for (Node& v : d_vals)
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
  if( !d_vals[i].isNull() ){
    return qs.areEqual(d_vals[i], n);
  }
  d_vals[i] = n;
  return true;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
