/*********************                                                        */
/*! \file term_canonize.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of term canonize.
 **/

#include "expr/term_canonize.h"

// TODO #1216: move the code in this include
#include "theory/quantifiers/term_util.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace expr {

TermCanonize::TermCanonize() : d_op_id_count(0), d_typ_id_count(0) {}

int TermCanonize::getIdForOperator(Node op)
{
  std::map<Node, int>::iterator it = d_op_id.find(op);
  if (it == d_op_id.end())
  {
    d_op_id[op] = d_op_id_count;
    d_op_id_count++;
    return d_op_id[op];
  }
  return it->second;
}

int TermCanonize::getIdForType(TypeNode t)
{
  std::map<TypeNode, int>::iterator it = d_typ_id.find(t);
  if (it == d_typ_id.end())
  {
    d_typ_id[t] = d_typ_id_count;
    d_typ_id_count++;
    return d_typ_id[t];
  }
  return it->second;
}

bool TermCanonize::getTermOrder(Node a, Node b)
{
  if (a.getKind() == BOUND_VARIABLE)
  {
    if (b.getKind() == BOUND_VARIABLE)
    {
      return getIndexForFreeVariable(a) < getIndexForFreeVariable(b);
    }
    return true;
  }
  if (b.getKind() != BOUND_VARIABLE)
  {
    Node aop = a.hasOperator() ? a.getOperator() : a;
    Node bop = b.hasOperator() ? b.getOperator() : b;
    Trace("aeq-debug2") << a << "...op..." << aop << std::endl;
    Trace("aeq-debug2") << b << "...op..." << bop << std::endl;
    if (aop == bop)
    {
      if (a.getNumChildren() == b.getNumChildren())
      {
        for (unsigned i = 0, size = a.getNumChildren(); i < size; i++)
        {
          if (a[i] != b[i])
          {
            // first distinct child determines the ordering
            return getTermOrder(a[i], b[i]);
          }
        }
      }
      else
      {
        return aop.getNumChildren() < bop.getNumChildren();
      }
    }
    else
    {
      return getIdForOperator(aop) < getIdForOperator(bop);
    }
  }
  return false;
}

Node TermCanonize::getCanonicalFreeVar(TypeNode tn, unsigned i)
{
  Assert(!tn.isNull());
  NodeManager* nm = NodeManager::currentNM();
  while (d_cn_free_var[tn].size() <= i)
  {
    std::stringstream oss;
    oss << tn;
    std::string typ_name = oss.str();
    while (typ_name[0] == '(')
    {
      typ_name.erase(typ_name.begin());
    }
    std::stringstream os;
    os << typ_name[0] << i;
    Node x = nm->mkBoundVar(os.str().c_str(), tn);
    d_fvIndex[x] = d_cn_free_var[tn].size();
    d_cn_free_var[tn].push_back(x);
  }
  return d_cn_free_var[tn][i];
}

size_t TermCanonize::getIndexForFreeVariable(Node v) const
{
  std::map<Node, size_t>::const_iterator it = d_fvIndex.find(v);
  if (it == d_fvIndex.end())
  {
    return 0;
  }
  return it->second;
}

struct sortTermOrder
{
  TermCanonize* d_tu;
  bool operator()(Node i, Node j) { return d_tu->getTermOrder(i, j); }
};

Node TermCanonize::getCanonicalTerm(TNode n,
                                    bool apply_torder,
                                    bool doHoVar,
                                    std::map<TypeNode, unsigned>& var_count,
                                    std::map<TNode, Node>& visited)
{
  std::map<TNode, Node>::iterator it = visited.find(n);
  if (it != visited.end())
  {
    return it->second;
  }

  Trace("canon-term-debug") << "Get canonical term for " << n << std::endl;
  if (n.getKind() == BOUND_VARIABLE)
  {
    TypeNode tn = n.getType();
    // allocate variable
    unsigned vn = var_count[tn];
    var_count[tn]++;
    Node fv = getCanonicalFreeVar(tn, vn);
    visited[n] = fv;
    Trace("canon-term-debug") << "...allocate variable." << std::endl;
    return fv;
  }
  else if (n.getNumChildren() > 0)
  {
    // collect children
    Trace("canon-term-debug") << "Collect children" << std::endl;
    std::vector<Node> cchildren;
    for (const Node& cn : n)
    {
      cchildren.push_back(cn);
    }
    // if applicable, first sort by term order
    if (apply_torder && theory::quantifiers::TermUtil::isComm(n.getKind()))
    {
      Trace("canon-term-debug")
          << "Sort based on commutative operator " << n.getKind() << std::endl;
      sortTermOrder sto;
      sto.d_tu = this;
      std::sort(cchildren.begin(), cchildren.end(), sto);
    }
    // now make canonical
    Trace("canon-term-debug") << "Make canonical children" << std::endl;
    for (unsigned i = 0, size = cchildren.size(); i < size; i++)
    {
      cchildren[i] = getCanonicalTerm(
          cchildren[i], apply_torder, doHoVar, var_count, visited);
    }
    if (n.getMetaKind() == metakind::PARAMETERIZED)
    {
      Node op = n.getOperator();
      if (doHoVar)
      {
        op = getCanonicalTerm(op, apply_torder, doHoVar, var_count, visited);
      }
      Trace("canon-term-debug") << "Insert operator " << op << std::endl;
      cchildren.insert(cchildren.begin(), op);
    }
    Trace("canon-term-debug")
        << "...constructing for " << n << "." << std::endl;
    Node ret = NodeManager::currentNM()->mkNode(n.getKind(), cchildren);
    Trace("canon-term-debug")
        << "...constructed " << ret << " for " << n << "." << std::endl;
    visited[n] = ret;
    return ret;
  }
  Trace("canon-term-debug") << "...return 0-child term." << std::endl;
  return n;
}

Node TermCanonize::getCanonicalTerm(TNode n, bool apply_torder, bool doHoVar)
{
  std::map<TypeNode, unsigned> var_count;
  std::map<TNode, Node> visited;
  return getCanonicalTerm(n, apply_torder, doHoVar, var_count, visited);
}

}  // namespace expr
}  // namespace CVC4
