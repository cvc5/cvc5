/*********************                                                        */
/*! \file sygus_grammar_red.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of sygus_grammar_red
 **/

#include "theory/quantifiers/sygus/sygus_grammar_red.h"

#include "expr/dtype.h"
#include "expr/sygus_datatype.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers_engine.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

void SygusRedundantCons::initialize(QuantifiersEngine* qe, TypeNode tn)
{
  Assert(qe != nullptr);
  Trace("sygus-red") << "Compute redundant cons for " << tn << std::endl;
  d_type = tn;
  Assert(tn.isDatatype());
  TermDbSygus* tds = qe->getTermDatabaseSygus();
  tds->registerSygusType(tn);
  const DType& dt = tn.getDType();
  Assert(dt.isSygus());
  TypeNode btn = dt.getSygusType();
  for (unsigned i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
  {
    Trace("sygus-red") << "  Is " << dt[i].getName() << " a redundant operator?"
                       << std::endl;
    Node sop = dt[i].getSygusOp();
    if (sop.getAttribute(SygusAnyConstAttribute()))
    {
      // the any constant constructor is never redundant
      d_sygus_red_status.push_back(0);
      continue;
    }
    std::map<int, Node> pre;
    // We do not do beta reduction, since we want the arguments to match the
    // the types of the datatype.
    Node g = tds->mkGeneric(dt, i, pre, false);
    Trace("sygus-red-debug") << "  ...pre-rewrite : " << g << std::endl;
    d_gen_terms[i] = g;
    // is the operator a lambda of the form (lambda x1...xn. f(x1...xn))?
    bool lamInOrder = false;
    if (sop.getKind() == LAMBDA && sop[0].getNumChildren() == sop[1].getNumChildren())
    {
      Assert(g.getNumChildren()==sop[0].getNumChildren());
      lamInOrder = true;
      for (size_t j = 0, nchild = sop[1].getNumChildren(); j < nchild; j++)
      {
        if (sop[0][j] != sop[1][j])
        {
          // arguments not in order
          lamInOrder = false;
          break;
        }
      }
    }
    // a list of variants of the generic term (see getGenericList).
    std::vector<Node> glist;
    if (lamInOrder)
    {
      // If it is a lambda whose arguments are one-to-one with the datatype
      // arguments, then we can add variants of this operator by permuting
      // the argument list (see getGenericList).
      Assert(g.getNumChildren()==dt[i].getNumArgs());
      for (unsigned j = 0, nargs = dt[i].getNumArgs(); j < nargs; j++)
      {
        pre[j] = g[j];
      }
      getGenericList(tds, dt, i, 0, pre, glist);
    }
    else
    {
      // It is a builtin (possibly) ground term. Its children do not correspond
      // one-to-one with the arugments of the constructor. Hence, we consider
      // only g itself as a variant.
      glist.push_back(g);
    }
    // call the extended rewriter
    bool red = false;
    for (const Node& gr : glist)
    {
      Trace("sygus-red-debug") << "  ...variant : " << gr << std::endl;
      std::map<Node, unsigned>::iterator itg = d_gen_cons.find(gr);
      if (itg != d_gen_cons.end() && itg->second != i)
      {
        red = true;
        Trace("sygus-red") << "  ......redundant, since a variant of " << g
                           << " and " << d_gen_terms[itg->second]
                           << " both rewrite to " << gr << std::endl;
        break;
      }
      else
      {
        d_gen_cons[gr] = i;
        Trace("sygus-red") << "  ......not redundant." << std::endl;
      }
    }
    d_sygus_red_status.push_back(red ? 1 : 0);
  }
  Trace("sygus-red") << "Compute redundant cons for " << tn << " finished"
                     << std::endl;
}

void SygusRedundantCons::getRedundant(std::vector<unsigned>& indices)
{
  const DType& dt = d_type.getDType();
  for (unsigned i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
  {
    if (isRedundant(i))
    {
      indices.push_back(i);
    }
  }
}

bool SygusRedundantCons::isRedundant(unsigned i)
{
  Assert(i < d_sygus_red_status.size());
  return d_sygus_red_status[i] == 1;
}

void SygusRedundantCons::getGenericList(TermDbSygus* tds,
                                        const DType& dt,
                                        unsigned c,
                                        unsigned index,
                                        std::map<int, Node>& pre,
                                        std::vector<Node>& terms)
{
  if (index == dt[c].getNumArgs())
  {
    Node gt = tds->mkGeneric(dt, c, pre);
    gt = tds->getExtRewriter()->extendedRewrite(gt);
    terms.push_back(gt);
    return;
  }
  // with no swap
  getGenericList(tds, dt, c, index + 1, pre, terms);
  // swapping is exponential, only use for operators with small # args.
  if (dt[c].getNumArgs() <= 5)
  {
    TypeNode atype = tds->getArgType(dt[c], index);
    for (unsigned s = index + 1, nargs = dt[c].getNumArgs(); s < nargs; s++)
    {
      if (tds->getArgType(dt[c], s) == atype)
      {
        // swap s and index
        Node tmp = pre[s];
        pre[s] = pre[index];
        pre[index] = tmp;
        getGenericList(tds, dt, c, index + 1, pre, terms);
        // revert
        tmp = pre[s];
        pre[s] = pre[index];
        pre[index] = tmp;
      }
    }
  }
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
