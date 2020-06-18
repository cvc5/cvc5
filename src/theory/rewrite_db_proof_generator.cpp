/*********************                                                        */
/*! \file rewrite_db_proof_generator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Rewrite database proof generator
 **/

#include "theory/rewrite_db_proof_generator.h"

#include "theory/rewrite_db_term_process.h"

namespace CVC4 {
namespace theory {

RewriteDbProofCons::RewriteDbProofCons(RewriteDb& db) : d_notify(*this), d_db(db), d_eval()
{
  NodeManager* nm = NodeManager::currentNM();
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
}

bool RewriteDbProofCons::prove(Node a, Node b, unsigned recLimit)
{
  Node eq = a.eqNode(b);
  Node eqi = RewriteDbTermProcess::toInternal(eq);
  d_currRecLimit = recLimit+1;
  unsigned id = proveInternal(eqi);
  return id!=0;
}

std::string RewriteDbProofCons::identify() const
{
  return "RewriteDbProofCons";
}

unsigned RewriteDbProofCons::proveInternal(Node eqi)
{
  Assert (d_currRecLimit>0);
  Assert (eqi.getKind()==EQUAL);
  std::unordered_map<Node, unsigned, NodeHashFunction>::iterator it =
      d_pcache.find(eqi);
  if (it != d_pcache.end())
  {
    if (it->second != 0)
    {
      // proof exists, return
      return it->second;
    }
    Assert (d_pcacheFailMaxDepth.find(eqi)!=d_pcacheFailMaxDepth.end());
    if (d_currRecLimit<=d_pcacheFailMaxDepth[eqi])
    {
      return 0;
    }
  }
  // use base methods to see if eqi holds
  unsigned idb = proveInternalBase(eqi);
  if (idb!=0)
  {
    d_pcache[eqi] = idb;
    return idb;
  }
  // Otherwise, call the get matches routine. This will call notifyMatch below
  // for each matching rewrite rule conclusion in the database
  // decrease the recursion depth
  d_currRecLimit--;
  d_db.getMatches(eqi, &d_notify);
  d_currRecLimit++;
  it = d_pcache.find(eqi);
  if (it != d_pcache.end())
  {
    return it->second;
  }
  // store failure, and its maximum depth
  d_pcache[eqi] = 0;
  d_pcacheFailMaxDepth[eqi] = d_currRecLimit;
  return 0;
}

bool RewriteDbProofCons::notifyMatch(Node s,
              Node n,
              std::vector<Node>& vars,
              std::vector<Node>& subs)
{
  // get the rule identifiers for the conclusion
  const std::vector<unsigned>& ids = d_db.getRuleIdsForConclusion(n);
  Assert (!ids.empty());
  // check each rule instance
  bool retVal = true;
  bool recurse = d_currRecLimit>0;
  for (unsigned id : ids)
  {
    const RewritePfRule& rpr = d_db.getRule(id);

    // do its conditions hold?
    bool condSuccess = true;
    Trace("rew-db") << "Check rule " << rpr.d_name << std::endl;
    for (const Node& cond : rpr.d_cond)
    {
      // check whether condition holds? Only do so if we are allowed to recurse
      condSuccess = false;
      if (recurse)
      {
        // substitute
        Node sc =
            cond.substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
        Trace("rew-db-infer-sc") << "Check condition: " << sc << std::endl;
        Assert(sc.getType().isBoolean());
        // recursively check if the condition holds
        condSuccess = proveInternal(sc);
        if (Trace.isOn("rew-db"))
        {
          if (!condSuccess)
          {
            Trace("rew-db")
                << "required: " << sc << " for " << rpr.d_name << std::endl;
          }
        }
      }
      if (!condSuccess)
      {
        break;
      }
    }
    if (condSuccess)
    {
      // successfully found instance of rule
      if (Trace.isOn("rew-db-infer"))
      {
        Node se = RewriteDbTermProcess::toExternal(s);
        Trace("rew-db-infer")
            << "INFER " << se << " by " << rpr.d_name << std::endl;
      }
      d_pcache[s] = id;
      // don't need to notify any further matches
      return false;
    }
  }
  // want to keep getting notify calls
  return true;
}

unsigned RewriteDbProofCons::proveInternalBase(Node eqi)
{
  return 0;
}

}  // namespace theory
}  // namespace CVC4
