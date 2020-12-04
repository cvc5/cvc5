/*********************                                                        */
/*! \file sygus_reconstruct.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief utility for reconstruct
 **
 **/

#include "theory/quantifiers/sygus/sygus_reconstruct.h"

#include "expr/match_trie.h"
#include "expr/node_algorithm.h"
#include "smt/command.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/sygus/sygus_enumerator.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

SygusReconstruct::SygusReconstruct(TermDbSygus* tds, SygusStatistics& s)
    : d_tds(tds), d_stats(s)
{
}

/*
void SygusReconstruct::init(TypeNode stn,
                            std::map<TypeNode, std::vector<Node>>& pool)
{
  SygusTypeInfo stnInfo;
  stnInfo.initialize(d_tds, stn);

  std::vector<TypeNode> sfTypes;
  stnInfo.getSubfieldTypes(sfTypes);

  for (TypeNode type : sfTypes)
  {
    for (std::shared_ptr<DTypeConstructor> cons :
         type.getDType().getConstructors())
    {
      std::vector<Node> sygusVars;
      NodeManager* nm = NodeManager::currentNM();
      Trace("sygus-rcons") << "cons: " << *cons << std::endl;
      std::vector<Node> sygusChildren;
      sygusChildren.push_back(cons->getConstructor());

      for (size_t i = 0, n = cons->getNumArgs(); i < n; ++i)
      {
        Node ct = d_tds->getFreeVarInc(cons->getArgType(i), d_varCount);
        // Trace("sygus-rcons")
        //     << "ct: " << ct << ": " << ct.getType() << std::endl;

        sygusChildren.push_back(ct);
        sygusVars.push_back(ct);
        d_builtinToSygus.emplace(datatypes::utils::sygusToBuiltin(ct), ct);
      }
      Node cx = nm->mkNode(kind::APPLY_CONSTRUCTOR, sygusChildren);
      pool[type].push_back(cx);
    }
  }
}
*/

bool SygusReconstruct::notify(Node s,
                              Node n,
                              std::vector<Node>& vars,
                              std::vector<Node>& subs)
{
  for (size_t i = 0; i < vars.size(); ++i)
  {
    if (d_subs.find(vars[i]) != d_subs.cend() && vars[i] != subs[i])
    {
      return true;
    }
  }

  return false;
}

Node SygusReconstruct::nextEnum(TypeNode stn)
{
  if (!d_enumerators[stn]->increment())
  {
    // TODO: remove enumerator
    Trace("sygus-rcons") << "enum: " << stn << ": no increment" << std::endl;
    return Node::null();
  }

  Node sz = d_enumerators[stn]->getCurrent();

  if (sz == Node::null())
  {
    Trace("sygus-rcons") << "enum: " << stn << ": null" << std::endl;
  }
  else
  {
    Trace("sygus-rcons") << "enum: " << stn << ": "
                         << datatypes::utils::sygusToBuiltin(sz) << std::endl;
  }

  if (sz != Node::null())
  {
    Node builtin = Rewriter::rewrite(datatypes::utils::sygusToBuiltin(sz));
    // if there are no matches (no call to notify)...
    if (d_poolTrie.getMatches(builtin, this))
    {
      // then, this is a new term and we should add it to pool
      d_poolTrie.addTerm(builtin);
    }
    else
    {
      // otherwise, return a null
      sz = Node::null();
    }
  }

  return sz;
}

void SygusReconstruct::cleanup()
{
  d_sol.clear();
  d_watchSet.clear();
  d_enumerators.clear();
  d_poolTrie.clear();
  d_obs.clear();
  d_obDb.clear();
  d_obInfos.clear();
  d_children.clear();
}

Node SygusReconstruct::reconstructSolution(Node sol,
                                           TypeNode stn,
                                           int& reconstructed,
                                           int enumLimit)
{
  Trace("sygus-rcons") << "SygusReconstruct::reconstructSolution: " << sol
                       << std::endl;
  Trace("sygus-rcons") << "- target sygus type is " << stn << std::endl;
  Trace("sygus-rcons") << "- enumeration limit is " << enumLimit << std::endl;
  cleanup();

  SygusTypeInfo stnInfo;
  stnInfo.initialize(d_tds, stn);

  // find the non-terminals of the grammar
  std::vector<TypeNode> sfTypes;
  stnInfo.getSubfieldTypes(sfTypes);

  NodeManager* nm = NodeManager::currentNM();

  // initialize the enumerators
  for (TypeNode tn : sfTypes)
  {
    d_enumerators.emplace(tn,
                          new SygusEnumerator(d_tds, nullptr, d_stats, true));
    d_enumerators[tn]->initialize(nm->mkSkolem("sygus_rcons", tn));
    // skip first enumerated term which is a free var that matches with anything
  }

  // find redundant subs
  for (Node sv : stn.getDType().getSygusVarList())
  {
    d_subs.emplace(sv, sv);
  }

  // will there ever be a case where an obligation is satisfied by enumeration
  // before any of its candidate solutions becomes constant?
  // d_activeObs[newStn].emplace(sol);
  d_obs[stn].emplace(sol);
  d_obDb[stn].emplace(sol);

  Obligation mainOb = Obligation(sol, stn);
  d_obInfos.emplace(mainOb, nm->mkSkolem("sygus_rcons", stn));

  std::map<TypeNode, std::vector<Node>> pool;

  int count = 0;

  // algorithm
  while (!d_obInfos[mainOb].isSatisfied() && count < enumLimit)
  {
    // enumeration phase
    std::map<TypeNode, std::set<Node>> obsPrime;
    Trace("sygus-rcons") << "count: " << count << std::endl;

    for (const std::pair<const TypeNode, std::set<Node>>& pair : d_obs)
    {
      if (!pair.second.empty())
      {
        Node sz = nextEnum(pair.first);

        if (sz != Node::null())
        {
          pool[pair.first].push_back(sz);
          for (Node builtin : pair.second)
          {
            if (!d_obInfos[Obligation(builtin, pair.first)].isSatisfied())
            {
              std::map<TypeNode, std::set<Node>> temp =
                  matchNewObs(Obligation(builtin, pair.first), sz);
              for (std::pair<TypeNode, std::set<Node>> tempPair : temp)
              {
                obsPrime[tempPair.first].insert(tempPair.second.cbegin(),
                                                tempPair.second.cend());
              }
            }
          }
        }
      }
    }
    // match phase
    while (!obsPrime.empty())
    {
      std::map<TypeNode, std::set<Node>> obsDPrime;

      for (const std::pair<TypeNode, std::set<Node>>& pair : obsPrime)
      {
        for (Node builtin : pair.second)
        {
          d_obs[pair.first].emplace(builtin);

          for (Node sz : pool[pair.first])
          {
            Trace("sygus-rcons") << "ct: " << sz << std::endl;
            Trace("sygus-rcons")
                << "t: "
                << Rewriter::rewrite(datatypes::utils::sygusToBuiltin(sz))
                << std::endl;
            auto temp = matchNewObs(Obligation(builtin, pair.first), sz);
            for (std::pair<TypeNode, std::set<Node>> tempPair : temp)
            {
              obsDPrime[tempPair.first].insert(tempPair.second.cbegin(),
                                               tempPair.second.cend());
            }
          }
        }
      }
      obsPrime = obsDPrime;
    }
    count++;
  }

  printEqClasses();
  printPool(pool);

  if (d_obInfos[mainOb].isSatisfied())
  {
    reconstructed = 1;
    return d_obInfos[mainOb].sol();
  }

  // we ran out of elements, return null
  reconstructed = -1;
  Warning() << CommandFailure(
      "Cannot get synth function: reconstruction to syntax failed.");
  // could return sol here, however, we choose to fail by returning null, since
  // it indicates a failure.
  return Node::null();
}

void SygusReconstruct::printEqClasses()
{
  Trace("sygus-rcons") << "\nEq classes: \n[";

  for (const std::pair<TypeNode, std::set<Node>>&& pair : d_obDb)
  {
    for (Node builtin : pair.second)
    {
      Obligation i(builtin, pair.first);
      Trace("sygus-rcons") << std::endl
                           << datatypes::utils::sygusToBuiltin(
                                  d_obInfos[i].var())
                           << " " << i << ":\n [";

      for (Node j : d_obInfos[i].eqClass())
      {
        Trace("sygus-rcons") << datatypes::utils::sygusToBuiltin(j) << " ";
      }
      Trace("sygus-rcons") << "]" << std::endl;
    }
  }

  Trace("sygus-rcons") << "]" << std::endl;
}

void SygusReconstruct::printPool(std::map<TypeNode, std::vector<Node>> pool)
{
  Trace("sygus-rcons") << "\nPool: \n[";

  for (const std::pair<TypeNode, std::vector<Node>>&& pair : pool)
  {
    Trace("sygus-rcons") << std::endl << pair.first << ":\n[" << std::endl;

    for (Node sygusTerm : pair.second)
    {
      Trace("sygus-rcons") << "  "
                           << Rewriter::rewrite(
                                  datatypes::utils::sygusToBuiltin(sygusTerm))
                                  .toString()
                           << std::endl;
    }

    Trace("sygus-rcons") << "]" << std::endl;
  }

  Trace("sygus-rcons") << "]" << std::endl;
}

std::map<TypeNode, std::set<Node>> SygusReconstruct::matchNewObs(Obligation ob,
                                                                 Node sz)
{
  NodeManager* nm = NodeManager::currentNM();
  std::map<TypeNode, std::set<Node>> obsPrime;

  Trace("sygus-rcons") << "ob: " << ob << std::endl;

  std::unordered_map<Node, Node, NodeHashFunction> candObs;
  candObs.insert(d_subs.cbegin(), d_subs.cend());
  std::vector<std::pair<Node, Node>> subs;

  if (expr::match(Rewriter::rewrite(datatypes::utils::sygusToBuiltin(sz)),
                  ob.builtinTerm(),
                  candObs))
  {
    Trace("sygus-rcons") << "-- ct: " << sz << std::endl;
    for (std::pair<Node, Node> pair : d_subs)
    {
      candObs.erase(pair.first);
    }
    std::vector<Obligation> szChildren;
    // for each candidate obligation
    for (NodePair candOb : candObs)
    {
      // did we come across this obligation before?
      TypeNode stn =
          datatypes::utils::builtinVarToSygus(candOb.first).getType();
      auto obsIt = d_obDb[stn].find(candOb.second);
      if (obsIt != d_obDb[stn].cend())
      {
        // if so, replace this candidate obligation with the old one
        Obligation oldOb(candOb.second, stn);
        if (d_obInfos[oldOb].isSatisfied())
        {
          subs.emplace_back(datatypes::utils::builtinVarToSygus(candOb.first),
                            d_obInfos[oldOb].sol());
        }
        else
        {
          subs.emplace_back(datatypes::utils::builtinVarToSygus(candOb.first),
                            d_obInfos[oldOb].var());
          szChildren.emplace_back(candOb.second, stn);
        }
      }
      else
      {
        // otherwise, add this candidate obligation to this list of
        // obligations
        Node newVar = nm->mkSkolem("sygus_rcons", stn);
        obsPrime[stn].emplace(candOb.second);
        d_obDb[stn].emplace(candOb.second);
        d_obInfos.emplace(Obligation(candOb.second, stn),
                          ObligationInfo(newVar));
        subs.emplace_back(datatypes::utils::builtinVarToSygus(candOb.first),
                          newVar);
        szChildren.emplace_back(candOb.second, stn);
      }
    }

    // replace original free vars in sz with new ones to avoid clashes
    if (!subs.empty())
    {
      sz = sz.substitute(subs.cbegin(), subs.cend());
    }

    if (!szChildren.empty())
    {
      d_children[sz] = szChildren;
      d_watchSet[*szChildren.cbegin()].emplace(sz);
    }

    // add sz as a possible solution to ob
    d_obInfos[ob].addToEqClass(sz);

    // if sz (solution to ob) does not have children, substitute it for all
    // instances of ob.
    auto it = d_children.find(sz);
    if (it == d_children.cend())
    {
      markSolved(ob, sz);
    }
  }

  return obsPrime;
}

void SygusReconstruct::markSolved(Obligation ob, Node sol)
{
  Trace("sygus-rcons") << "sol: " << sol << std::endl;
  Trace("sygus-rcons") << "builtin sol: "
                       << datatypes::utils::sygusToBuiltin(sol) << std::endl;

  Assert(Rewriter::rewrite(datatypes::utils::sygusToBuiltin(sol))
         == ob.builtinTerm());

  // FIXME: some free terms in the reconstructed solution get eliminated by the
  // rewriter. For example, rewite((ite true 0 z)) = 0. We should replace those
  // with random values.
  if (!sol.isConst())
  {
    Trace("sygus-rcons") << datatypes::utils::sygusToBuiltin(sol) << std::endl;
  }
  Assert(sol.isConst());

  // TODO: remove redundant sol
  // First, mark `ob` as solved
  d_obInfos[ob].setSol(sol);
  d_sol.emplace(d_obInfos[ob].var(), sol);
  // d_obs[ob.sygusType()].erase(ob.builtinTerm());

  std::vector<Obligation> stack;
  stack.push_back(ob);

  while (!stack.empty())
  {
    Obligation curr = stack.back();
    stack.pop_back();

    // find partial solutions that depend on the now solved obligation `curr`
    auto it = d_watchSet.find(curr);
    if (it != d_watchSet.cend())
    {
      // for each partial solution/parent
      for (Node parent : it->second)
      {
        // remove `curr` and (possibly) other solved obligations from its list
        // of children
        while (!d_children[parent].empty()
               && d_obInfos[d_children[parent].back()].isSatisfied())
        {
          d_children[parent].pop_back();
        }

        // if the partial solution does not have any more children...
        if (d_children[parent].empty())
        {
          // then it is completely solved and can be used as a solution of its
          // corresponding obligation
          Node parentSol = parent.substitute(d_sol.cbegin(), d_sol.cend());
          Obligation parentOb(
              Rewriter::rewrite(datatypes::utils::sygusToBuiltin(parentSol)),
              parentSol.getType());
          // proceed only if parent obligation is not already solved
          if (!d_obInfos[parentOb].isSatisfied())
          {
            // TODO: remove redundant sol
            d_obInfos[parentOb].setSol(parentSol);
            d_obInfos[parentOb].addToEqClass(parentSol);
            d_sol.emplace(d_obInfos[parentOb].var(), parentSol);
            // repeat the same process for the parent obligation
            stack.push_back(parentOb);
            // d_obs[parentOb.sygusType()].erase(parentOb.builtinTerm());
          }
        }
        else
        {
          // if it does have remaining children, add it to the watch list of one
          // of them (picked arbitrarily)
          Obligation newChild = d_children[parent].back();
          d_watchSet[newChild].emplace(parent);
        }
      }
      d_watchSet.erase(it);
    }
  }
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
