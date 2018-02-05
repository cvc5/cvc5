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

class ReconstructTrie
{
 public:
  std::map<Node, ReconstructTrie> d_children;
  std::vector<Node> d_reconstruct;
  void add(std::vector<Node>& cons, Node r, unsigned index = 0)
  {
    if (index == cons.size())
    {
      d_reconstruct.push_back(r);
    }
    else
    {
      d_children[cons[index]].add(cons, r, index + 1);
    }
  }
  Node getReconstruct(std::map<Node, int>& rcons, unsigned depth)
  {
    if (!d_reconstruct.empty())
    {
      for (unsigned i = 0, size = d_reconstruct.size(); i < size; i++)
      {
        Node r = d_reconstruct[i];
        if (rcons[r] == 0)
        {
          Trace("sygus-static-enum")
              << "...eliminate constructor " << r << std::endl;
          rcons[r] = 1;
          return r;
        }
      }
    }
    if (depth > 0)
    {
      for (unsigned w = 0; w < 2; w++)
      {
        for (std::map<Node, ReconstructTrie>::iterator it = d_children.begin();
             it != d_children.end();
             ++it)
        {
          Node n = it->first;
          if ((w == 0 && rcons[n] != 0) || (w == 1 && rcons[n] == 0))
          {
            Node r = it->second.getReconstruct(rcons, depth - w);
            if (!r.isNull())
            {
              if (w == 1)
              {
                Trace("sygus-static-enum")
                    << "...use " << n << " to eliminate constructor " << r
                    << std::endl;
                rcons[n] = -1;
              }
              return r;
            }
          }
        }
      }
    }
    return Node::null();
  }
};

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
  // run an enumerator for this type
  if (options::sygusMinGrammarAgg())
  {
    TermUtil* tutil = qe->getTermUtil();
    TypeEnumerator te(tn);
    unsigned count = 0;
    std::map<Node, std::vector<Node> > builtin_to_orig;
    Trace("sygus-static-enum")
        << "Static enumerate " << dt.getName() << "..." << std::endl;
    while (!te.isFinished() && count < 1000)
    {
      Node n = *te;
      Node bn = tds->sygusToBuiltin(n, tn);
      Trace("sygus-static-enum") << "  " << bn;
      Node bnr = Rewriter::rewrite(bn);
      Trace("sygus-static-enum") << "  ..." << bnr << std::endl;
      builtin_to_orig[bnr].push_back(n);
      ++te;
      count++;
    }
    std::map<Node, bool> reserved;
    for (unsigned i = 0; i <= 2; i++)
    {
      Node rsv =
          i == 2 ? tutil->getTypeMaxValue(btn) : tutil->getTypeValue(btn, i);
      if (!rsv.isNull())
      {
        reserved[rsv] = true;
      }
    }
    Trace("sygus-static-enum")
        << "...make the reconstruct index data structure..." << std::endl;
    ReconstructTrie rt;
    std::map<Node, int> rcons;
    unsigned max_depth = 0;
    for (std::map<Node, std::vector<Node> >::iterator itb =
             builtin_to_orig.begin();
         itb != builtin_to_orig.end();
         ++itb)
    {
      if (itb->second.size() > 0)
      {
        std::map<Node, std::vector<Node> > clist;
        Node single_cons;
        for (unsigned j = 0; j < itb->second.size(); j++)
        {
          Node e = itb->second[j];
          tds->getSygusConstructors(e, clist[e]);
          if (clist[e].size() > max_depth)
          {
            max_depth = clist[e].size();
          }
          for (unsigned k = 0; k < clist[e].size(); k++)
          {
            rcons[clist[e][k]] = 0;
          }
          if (clist[e].size() == 1)
          {
            Trace("sygus-static-enum")
                << "...single constructor term : " << e << ", builtin is "
                << itb->first << ", cons is " << clist[e][0] << std::endl;
            if (single_cons.isNull())
            {
              single_cons = clist[e][0];
            }
            else
            {
              Trace("sygus-static-enum")
                  << "*** already can eliminate constructor " << clist[e][0]
                  << std::endl;
              unsigned cindex = Datatype::indexOf(clist[e][0].toExpr());
              d_sygus_red_status[cindex] = 1;
            }
          }
        }
        // do not eliminate 0, 1, or max
        if (!single_cons.isNull()
            && reserved.find(itb->first) == reserved.end())
        {
          Trace("sygus-static-enum")
              << "...possibly elim " << single_cons << std::endl;
          for (std::map<Node, std::vector<Node> >::iterator itc = clist.begin();
               itc != clist.end();
               ++itc)
          {
            if (std::find(itc->second.begin(), itc->second.end(), single_cons)
                == itc->second.end())
            {
              rt.add(itc->second, single_cons);
            }
          }
        }
      }
    }
    Trace("sygus-static-enum") << "...compute reconstructions..." << std::endl;
    Node next_rcons;
    do
    {
      unsigned depth = 0;
      do
      {
        next_rcons = rt.getReconstruct(rcons, depth);
        depth++;
      } while (next_rcons.isNull() && depth <= max_depth);
      // if we found a constructor to eliminate
      if (!next_rcons.isNull())
      {
        Trace("sygus-static-enum")
            << "*** eliminate constructor " << next_rcons << std::endl;
        unsigned cindex = Datatype::indexOf(next_rcons.toExpr());
        d_sygus_red_status[cindex] = 2;
      }
    } while (!next_rcons.isNull());
    Trace("sygus-static-enum") << "...finished..." << std::endl;
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
  if (options::sygusMinGrammarAgg())
  {
    return d_sygus_red_status[i] != 0;
  }
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
  if( dt[c].getNumArgs()<=5 )
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
