/*********************                                                        */
/*! \file rewrite_db.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Rewrite database
 **/

#include "theory/rewrite_db.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {

RewriteDb::RewriteDb() : d_idCounter(0)
{
  NodeManager* nm = NodeManager::currentNM();
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
}

unsigned RewriteDb::addRule(Node a, Node b, Node cond, const std::string& name)
{
  NodeManager* nm = NodeManager::currentNM();
  Node eq = a.eqNode(b);
  // we canonize left-to-right, hence we should traverse in the opposite
  // order, since we index based on conclusion
  Node tmp = nm->mkNode(IMPLIES, eq, cond);
  // convert to internal
  Node tmpi = d_rdtp.toInternal(tmp);

  // must canonize
  Trace("rewrite-db") << "Add rule " << name << ": " << cond << " => " << a
                      << " == " << b << std::endl;
  Node cr = d_canon.getCanonicalTerm(tmpi, false, false);

  Node condC = cr[1];
  std::vector<Node> conds;
  if (condC.getKind() == AND)
  {
    for (const Node& c : condC)
    {
      // should flatten in proof inference listing
      Assert(c.getKind() != AND);
      conds.push_back(c);
    }
  }
  else if (!condC.isConst())
  {
    conds.push_back(condC);
  }
  else if (!condC.getConst<bool>())
  {
    // skip those with false condition
    return 0;
  }
  // make as expected matching: top symbol of all conditions is equality
  // this means (not p) becomes (= p false), p becomes (= p true)
  for (unsigned i = 0, nconds = conds.size(); i < nconds; i++)
  {
    if (conds[i].getKind() == NOT)
    {
      conds[i] = conds[i][0].eqNode(d_false);
    }
    else if (conds[i].getKind() != EQUAL)
    {
      conds[i] = conds[i].eqNode(d_true);
    }
  }
  /*
  // register with side condition utility
  for (const Node& c : conds)
  {
    if (d_sceval.registerSideCondition(c))
    {
      d_hasSc.insert(c);
    }
  }
  */

  Node eqC = cr[0];
  Assert(eqC.getKind() == EQUAL);

  // add to discrimination tree
  Trace("proof-db-debug") << "Add (canonical) rule " << eqC << std::endl;
  d_mt.addTerm(eqC);

  // initialize rule
  d_idCounter++;
  d_rewDbRule[d_idCounter].init(name, conds, eqC);
  return d_idCounter;
}

void RewriteDb::getMatches(Node a, Node b, expr::NotifyMatch* ntm)
{
  Node eq = a.eqNode(b);
  d_mt.getMatches(eq, ntm);
}

}  // namespace theory
}  // namespace CVC4
