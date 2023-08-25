/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of representative set utilities.
 */

#include "theory/rep_set_iterator.h"

#include <unordered_set>

#include "theory/type_enumerator.h"

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {

RepSetIterator::RepSetIterator(const RepSet* rs, RepBoundExt* rext)
    : d_rs(rs), d_rext(rext), d_incomplete(false)
{
}

size_t RepSetIterator::domainSize(size_t i) const
{
  size_t v = d_var_order[i];
  return d_domain_elements[v].size();
}

TypeNode RepSetIterator::getTypeOf(size_t i) const { return d_types[i]; }

bool RepSetIterator::setQuantifier(Node q)
{
  Trace("rsi") << "Make rsi for quantified formula " << q << std::endl;
  Assert(d_types.empty());
  // store indicies
  for (const Node& v : q[0])
  {
    d_types.push_back(v.getType());
  }
  d_owner = q;
  return initialize();
}

bool RepSetIterator::setFunctionDomain(Node op)
{
  Trace("rsi") << "Make rsi for function " << op << std::endl;
  Assert(d_types.empty());
  TypeNode tn = op.getType();
  for (size_t i = 0; i < tn.getNumChildren() - 1; i++)
  {
    d_types.push_back(tn[i]);
  }
  d_owner = op;
  return initialize();
}

bool RepSetIterator::initialize()
{
  Trace("rsi") << "Initialize rep set iterator..." << std::endl;
  size_t ntypes = d_types.size();
  d_var_order.resize(ntypes);
  for (size_t v = 0; v < ntypes; v++)
  {
    d_index.push_back(0);
    // store default index order
    d_index_order.push_back(v);
    d_var_order[v] = v;
    // store default domain
    // d_domain.push_back( RepDomain() );
    d_domain_elements.push_back(std::vector<Node>());
    TypeNode tn = d_types[v];
    Trace("rsi") << "Var #" << v << " is type " << tn << "..." << std::endl;
    bool inc = true;
    bool setEnum = false;
    // check if it is externally bound
    if (d_rext)
    {
      inc = !d_rext->initializeRepresentativesForType(tn);
      RsiEnumType rsiet = d_rext->setBound(d_owner, v, d_domain_elements[v]);
      if (rsiet != ENUM_INVALID)
      {
        d_enum_type.push_back(rsiet);
        inc = false;
        setEnum = true;
      }
    }
    if (inc)
    {
      Trace("fmf-incomplete")
          << "Incomplete because of quantification of type " << tn << std::endl;
      d_incomplete = true;
    }

    // if we have yet to determine the type of enumeration
    if (!setEnum)
    {
      if (d_rs->hasType(tn))
      {
        d_enum_type.push_back(ENUM_DEFAULT);
        if (const auto* type_reps = d_rs->getTypeRepsOrNull(tn))
        {
          std::vector<Node>& v_domain_elements = d_domain_elements[v];
          v_domain_elements.insert(
              v_domain_elements.end(), type_reps->begin(), type_reps->end());
        }
      }
      else
      {
        Assert(d_incomplete);
        return false;
      }
    }
  }

  if (d_rext)
  {
    std::vector<size_t> varOrder;
    if (d_rext->getVariableOrder(d_owner, varOrder))
    {
      if (TraceIsOn("bound-int-rsi"))
      {
        Trace("bound-int-rsi") << "Variable order : ";
        for (size_t v : varOrder)
        {
          Trace("bound-int-rsi") << v << " ";
        }
        Trace("bound-int-rsi") << std::endl;
      }
      size_t nvars = varOrder.size();
      std::vector<size_t> indexOrder;
      indexOrder.resize(nvars);
      for (size_t i = 0; i < nvars; i++)
      {
        Assert(varOrder[i] < indexOrder.size());
        indexOrder[varOrder[i]] = i;
      }
      if (TraceIsOn("bound-int-rsi"))
      {
        Trace("bound-int-rsi") << "Will use index order : ";
        for (size_t i = 0, isize = indexOrder.size(); i < isize; i++)
        {
          Trace("bound-int-rsi") << indexOrder[i] << " ";
        }
        Trace("bound-int-rsi") << std::endl;
      }
      setIndexOrder(indexOrder);
    }
  }
  // now reset the indices
  doResetIncrement(-1, true);
  return true;
}

void RepSetIterator::setIndexOrder(std::vector<size_t>& indexOrder)
{
  d_index_order.clear();
  d_index_order.insert(
      d_index_order.begin(), indexOrder.begin(), indexOrder.end());
  // make the d_var_order mapping
  for (size_t i = 0, isize = d_index_order.size(); i < isize; i++)
  {
    d_var_order[d_index_order[i]] = i;
  }
}

int RepSetIterator::resetIndex(size_t i, bool initial)
{
  d_index[i] = 0;
  size_t v = d_var_order[i];
  Trace("bound-int-rsi") << "Reset " << i << ", var order = " << v
                         << ", initial = " << initial << std::endl;
  if (d_rext)
  {
    if (!d_rext->resetIndex(this, d_owner, v, initial, d_domain_elements[v]))
    {
      return -1;
    }
  }
  return d_domain_elements[v].empty() ? 0 : 1;
}

int RepSetIterator::incrementAtIndex(int i)
{
  Assert(!isFinished());
  Trace("rsi-debug") << "RepSetIterator::incrementAtIndex: " << i << std::endl;
  // increment d_index
  if (i >= 0)
  {
    Trace("rsi-debug") << "domain size of " << i << " is " << domainSize(i)
                       << std::endl;
  }
  while (i >= 0 && d_index[i] >= (int)(domainSize(i) - 1))
  {
    i--;
    if (i >= 0)
    {
      Trace("rsi-debug") << "domain size of " << i << " is " << domainSize(i)
                         << std::endl;
    }
  }
  if (i == -1)
  {
    Trace("rsi-debug") << "increment failed" << std::endl;
    d_index.clear();
    return -1;
  }
  else
  {
    Trace("rsi-debug") << "increment " << i << std::endl;
    d_index[i]++;
    return doResetIncrement(i);
  }
}

int RepSetIterator::doResetIncrement(int i, bool initial)
{
  Trace("rsi-debug") << "RepSetIterator::doResetIncrement: " << i
                     << ", initial=" << initial << std::endl;
  for (size_t ii = (i + 1); ii < d_index.size(); ii++)
  {
    bool emptyDomain = false;
    int ri_res = resetIndex(ii, initial);
    if (ri_res == -1)
    {
      // failed
      d_index.clear();
      Trace("fmf-incomplete")
          << "Incomplete because of reset index " << ii << std::endl;
      d_incomplete = true;
      break;
    }
    else if (ri_res == 0)
    {
      emptyDomain = true;
    }
    // force next iteration if currently an empty domain
    if (emptyDomain)
    {
      Trace("rsi-debug") << "This is an empty domain (index " << ii << ")."
                         << std::endl;
      if (ii > 0)
      {
        // increment at the previous index
        return incrementAtIndex(ii - 1);
      }
      else
      {
        // this is the first index, we are done
        d_index.clear();
        return -1;
      }
    }
  }
  Trace("rsi-debug") << "Finished, return " << i << std::endl;
  return i;
}

int RepSetIterator::increment()
{
  if (!isFinished())
  {
    return incrementAtIndex(d_index.size() - 1);
  }
  else
  {
    return -1;
  }
}

bool RepSetIterator::isFinished() const { return d_index.empty(); }

Node RepSetIterator::getCurrentTerm(size_t i, bool valTerm) const
{
  size_t ii = d_index_order[i];
  size_t curr = d_index[ii];
  Trace("rsi-debug") << "rsi : get term " << i
                     << ", index order = " << d_index_order[i] << std::endl;
  Trace("rsi-debug") << "rsi : curr = " << curr << " / "
                     << d_domain_elements[i].size() << std::endl;
  Assert(0 <= curr && curr < d_domain_elements[i].size());
  Node t = d_domain_elements[i][curr];
  Trace("rsi-debug") << "rsi : term = " << t << std::endl;
  if (valTerm)
  {
    Node tt = d_rs->getTermForRepresentative(t);
    if (!tt.isNull())
    {
      Trace("rsi-debug") << "rsi : return rep term = " << tt << std::endl;
      return tt;
    }
  }
  Trace("rsi-debug") << "rsi : return" << std::endl;
  return t;
}

void RepSetIterator::getCurrentTerms(std::vector<Node>& terms) const
{
  for (size_t i = 0, size = d_index_order.size(); i < size; i++)
  {
    terms.push_back(getCurrentTerm(i));
  }
}

void RepSetIterator::debugPrint(const char* c)
{
  for (size_t v = 0, isize = d_index.size(); v < isize; v++)
  {
    Trace(c) << v << " : " << getCurrentTerm(v) << std::endl;
  }
}

void RepSetIterator::debugPrintSmall(const char* c)
{
  Trace(c) << "RI: ";
  for (size_t v = 0, isize = d_index.size(); v < isize; v++)
  {
    Trace(c) << v << ": " << getCurrentTerm(v) << " ";
  }
  Trace(c) << std::endl;
}

}  // namespace theory
}  // namespace cvc5::internal
