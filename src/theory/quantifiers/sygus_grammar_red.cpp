/*********************                                                        */
/*! \file sygus_grammar_red.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of sygus_grammar_red
 **/

#include "theory/quantifiers/sygus_grammar_red.h"

#include "options/quantifiers_options.h"
#include "theory/quantifiers/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"

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
  const Datatype& dt = static_cast<DatatypeType>(tn.toType()).getDatatype();
  Assert(dt.isSygus());
  TypeNode btn = TypeNode::fromType(dt.getSygusType());
  for (unsigned i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
  {
    Trace("sygus-red") << "  Is " << dt[i].getName() << " a redundant operator?"
                       << std::endl;
    std::map<int, Node> pre;
    Node g = tds->mkGeneric(dt, i, pre);
    Trace("sygus-red-debug") << "  ...pre-rewrite : " << g << std::endl;
    Assert(g.getNumChildren() == dt[i].getNumArgs());
    d_gen_terms[i] = g;
    for (unsigned j = 0, nargs = dt[i].getNumArgs(); j < nargs; j++)
    {
      pre[j] = g[j];
    }
    std::vector<Node> glist;
    getGenericList(tds, dt, i, 0, pre, glist);
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
}

void SygusRedundantCons::getRedundant(std::vector<unsigned>& indices)
{
  const Datatype& dt = static_cast<DatatypeType>(d_type.toType()).getDatatype();
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
                                        const Datatype& dt,
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
