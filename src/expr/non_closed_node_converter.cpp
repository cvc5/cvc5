/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of non-closed node conversion
 */

#include "expr/non_closed_node_converter.h"

#include "expr/array_store_all.h"
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "options/arrays_options.h"
#include "smt/env.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/uf/function_const.h"

namespace cvc5::internal {

NonClosedNodeConverter::NonClosedNodeConverter(Env& env)
    : EnvObj(env), NodeConverter(nodeManager())
{
  getNonClosedKinds(env, d_nonClosedKinds);
}

NonClosedNodeConverter::~NonClosedNodeConverter() {}

Node NonClosedNodeConverter::postConvert(Node n)
{
  Trace("non-closed-debug") << "postConvert: " << n << std::endl;
  Kind k = n.getKind();
  bool purify = false;
  if (d_nonClosedKinds.find(k) != d_nonClosedKinds.end())
  {
    purify = true;
  }
  else if (k == Kind::STORE_ALL)
  {
    // Store all hides its element. if this is not closed, then this entire
    // term must be purified.
    Node nval = n.getConst<ArrayStoreAll>().getValue();
    Node nvalc = convert(nval);
    if (nvalc != nval)
    {
      purify = true;
    }
  }
  else
  {
    // node that can "hide" constants, we must convert these to their expanded
    // form and see if they convert
    Node nc;
    if (k == Kind::CONST_SEQUENCE)
    {
      nc = theory::strings::utils::mkConcatForConstSequence(n);
    }
    else if (k == Kind::FUNCTION_ARRAY_CONST)
    {
      nc = theory::uf::FunctionConst::toLambda(n);
    }
    if (!nc.isNull() && nc!=n)
    {
      Node nnc = convert(nc);
      if (nnc != nc)
      {
        return nnc;
      }
    }
  }
  if (purify)
  {
    Node sk = SkolemManager::mkPurifySkolem(n);
    d_purifySkolems.push_back(sk);
    return sk;
  }
  return n;
}

bool NonClosedNodeConverter::isClosed(Env& env, const Node& n)
{
  std::unordered_set<Kind, kind::KindHashFunction> ncks;
  getNonClosedKinds(env, ncks);
  // additional kinds that *might* be non-closed
  ncks.insert(Kind::STORE_ALL);
  ncks.insert(Kind::CONST_SEQUENCE);
  ncks.insert(Kind::FUNCTION_ARRAY_CONST);
  // most of the time, this will return true
  if (!expr::hasSubtermKinds(ncks, n))
  {
    return true;
  }
  // otherwise see if it converts, if it doesn't then it is closed
  NonClosedNodeConverter ncnc(env);
  Node nc = ncnc.convert(n);
  return nc == n;
}

void NonClosedNodeConverter::getNonClosedKinds(
    const Env& env, std::unordered_set<Kind, kind::KindHashFunction>& ncks)
{
  // some kinds may appear in model values that cannot be asserted
  if (!env.getOptions().arrays.arraysExp)
  {
    ncks.insert(Kind::STORE_ALL);
  }
  ncks.insert(Kind::CODATATYPE_BOUND_VARIABLE);
  ncks.insert(Kind::UNINTERPRETED_SORT_VALUE);
  // may appear in certain models e.g. strings of excessive length
  ncks.insert(Kind::WITNESS);
  ncks.insert(Kind::REAL_ALGEBRAIC_NUMBER);
}

const std::vector<Node>& NonClosedNodeConverter::getSkolems() const
{
  return d_purifySkolems;
}

}  // namespace cvc5::internal
