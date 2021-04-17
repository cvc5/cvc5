/******************************************************************************
 * Top contributors (to current version):
 *   Abdalrhman Mohamed, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation for reconstruct.
 */

#include "theory/quantifiers/sygus/sygus_reconstruct.h"

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "smt/command.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/rewriter.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace quantifiers {

SygusReconstruct::SygusReconstruct(TermDbSygus* tds, SygusStatistics& s)
    : d_tds(tds), d_stats(s)
{
}

Node SygusReconstruct::reconstructSolution(Node sol,
                                           TypeNode stn,
                                           int8_t& reconstructed,
                                           uint64_t enumLimit)
{
  Trace("sygus-rcons") << "SygusReconstruct::reconstructSolution: " << sol
                       << std::endl;
  Trace("sygus-rcons") << "- target sygus type is " << stn << std::endl;
  Trace("sygus-rcons") << "- enumeration limit is " << enumLimit << std::endl;

  // this method may get called multiple times with the same object. We need to
  // reset the state to avoid conflicts
  clear();

  initialize(stn);

  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();

  /** a set of obligations that are not yet satisfied for each sygus datatype */
  TypeObligationSetMap unsolvedObs;

  // paramaters sol and stn constitute the main obligation to satisfy
  Node mainOb = sm->mkDummySkolem("sygus_rcons", stn);

  // add the main obligation to the set of obligations that are not yet
  // satisfied
  unsolvedObs[stn].emplace(mainOb);
  d_obInfo.emplace(mainOb, RConsObligationInfo(sol));
  d_stnInfo[stn].setBuiltinToOb(sol, mainOb);

  // We need to add the main obligation to the crd in case it cannot be broken
  // down by matching. By doing so, we can solve the obligation using
  // enumeration and crd (if it is in the grammar)
  d_stnInfo[stn].addTerm(sol);

  // the set of unique (up to rewriting) patterns/shapes in the grammar used by
  // matching
  std::unordered_map<TypeNode, std::vector<Node>, TypeNodeHashFunction> pool;

  uint64_t count = 0;

  // algorithm
  while (d_sol[mainOb].isNull() && count < enumLimit)
  {
    // enumeration phase
    // a temporary set of new obligations cached for processing in the match
    // phase
    TypeObligationSetMap obsPrime;
    for (const std::pair<const TypeNode, ObligationSet>& pair : unsolvedObs)
    {
      // enumerate a new term
      Trace("sygus-rcons") << "enum: " << stn << ": ";
      Node sz = d_stnInfo[pair.first].nextEnum();
      if (sz.isNull())
      {
        continue;
      }
      Node builtin = Rewriter::rewrite(datatypes::utils::sygusToBuiltin(sz));
      // if enumerated term does not contain free variables, then its
      // corresponding obligation can be solved immediately
      if (sz.isConst())
      {
        Node rep = d_stnInfo[pair.first].addTerm(builtin);
        Node k = d_stnInfo[pair.first].builtinToOb(rep);
        // check if the enumerated term solves an obligation
        if (k.isNull())
        {
          // if not, create an "artifical" obligation whose solution would be
          // the enumerated term
          k = sm->mkDummySkolem("sygus_rcons", pair.first);
          d_obInfo.emplace(k, RConsObligationInfo(builtin));
          d_stnInfo[pair.first].setBuiltinToOb(builtin, k);
        }
        // mark the obligation as solved
        markSolved(k, sz);
        // Since we added the term to the candidate rewrite database, there is
        // no point in adding it to the pool too
        continue;
      }
      // if there are no matches (all calls to notify return true)...
      if (d_poolTrie.getMatches(builtin, this))
      {
        // then, this is a new term and we should add it to pool
        d_poolTrie.addTerm(builtin);
        pool[pair.first].push_back(sz);
        for (Node k : pair.second)
        {
          if (d_sol[k].isNull())
          {
            Trace("sygus-rcons")
                << "ob: " << RConsObligationInfo::obToString(k, d_obInfo[k])
                << std::endl;
            // try to match obligation k with the enumerated term sz
            TypeObligationSetMap temp = matchNewObs(k, sz);
            // cache the new obligations for processing in the match phase
            for (const std::pair<const TypeNode, ObligationSet>& tempPair :
                 temp)
            {
              obsPrime[tempPair.first].insert(tempPair.second.cbegin(),
                                              tempPair.second.cend());
            }
          }
        }
      }
    }
    // match phase
    while (!obsPrime.empty())
    {
      // a temporary set of new obligations cached for later processing
      TypeObligationSetMap obsDPrime;
      for (const std::pair<const TypeNode, ObligationSet>& pair : obsPrime)
      {
        for (const Node& k : pair.second)
        {
          unsolvedObs[pair.first].emplace(k);
          if (d_sol[k].isNull())
          {
            Trace("sygus-rcons")
                << "ob: " << RConsObligationInfo::obToString(k, d_obInfo[k])
                << std::endl;
            for (Node sz : pool[pair.first])
            {
              // try to match each newly generated and cached obligation
              // with patterns in pool
              TypeObligationSetMap temp = matchNewObs(k, sz);
              // cache the new obligations for later processing
              for (const std::pair<const TypeNode, ObligationSet>& tempPair :
                   temp)
              {
                obsDPrime[tempPair.first].insert(tempPair.second.cbegin(),
                                                 tempPair.second.cend());
              }
            }
          }
        }
      }
      obsPrime = std::move(obsDPrime);
    }
    // remove solved obligations from unsolvedObs
    removeSolvedObs(unsolvedObs);
    ++count;
  }

  if (Trace("sygus-rcons").isConnected())
  {
    RConsObligationInfo::printCandSols(mainOb, d_obInfo);
    printPool(pool);
  }

  // if the main obligation is solved, return the solution
  if (!d_sol[mainOb].isNull())
  {
    reconstructed = 1;
    // The algorithm mostly works with rewritten terms and may not notice that
    // the original terms contain variables eliminated by the rewriter. For
    // example, rewrite((ite true 0 z)) = 0. In such cases, we replace those
    // variables with ground values.
    return d_sol[mainOb].isConst() ? Node(d_sol[mainOb])
                                   : mkGround(d_sol[mainOb]);
  }

  // we ran out of elements, return null
  reconstructed = -1;
  Warning() << CommandFailure(
      "Cannot get synth function: reconstruction to syntax failed.");
  return d_sol[mainOb];
}

TypeObligationSetMap SygusReconstruct::matchNewObs(Node k, Node sz)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  TypeObligationSetMap obsPrime;

  // obligations generated by match. Note that we might have already seen (and
  // even solved) those obligations, hence the name "candidate obligations"
  std::unordered_map<Node, Node, NodeHashFunction> candObs;
  // the builtin terms corresponding to sygus variables in the grammar are bound
  // variables. However, we want the `match` method to treat them as ground
  // terms. So, we add redundant substitutions
  candObs.insert(d_sygusVars.cbegin(), d_sygusVars.cend());

  // try to match the obligation's builtin terms with the pattern sz
  for (Node builtin : d_obInfo[k].getBuiltins())
  {
    if (expr::match(Rewriter::rewrite(datatypes::utils::sygusToBuiltin(sz)),
                    builtin,
                    candObs))
    {
      // the bound variables z generated by the enumerators are reused across
      // enumerated terms, so we need to replace them with our own skolems
      std::vector<std::pair<Node, Node>> subs;
      Trace("sygus-rcons") << "-- ct: " << sz << std::endl;
      // remove redundant substitutions
      for (const std::pair<const Node, Node>& pair : d_sygusVars)
      {
        candObs.erase(pair.first);
      }
      // for each candidate obligation
      for (const std::pair<const Node, Node>& candOb : candObs)
      {
        TypeNode stn =
            datatypes::utils::builtinVarToSygus(candOb.first).getType();
        Node newVar;
        // did we come across an equivalent obligation before?
        Node rep = d_stnInfo[stn].addTerm(candOb.second);
        Node repOb = d_stnInfo[stn].builtinToOb(rep);
        if (!repOb.isNull())
        {
          // if so, use the original obligation
          newVar = repOb;
          // while `candOb.second` is equivalent to `rep`, it may be easier to
          // reconstruct than `rep`. For example:
          //
          // Grammar: S -> p | q | (not S) | (and S S) | (or S S)
          // rep = (= p q)
          // candOb.second = (or (and p q) (and (not p) (not q)))
          //
          // In this case, `candOb.second` is easy to reconstruct by matching
          // because it only uses operators that are already in the grammar.
          // `rep`, on the other hand, is cannot be reconstructed by matching
          // and can only be solved by enumeration (currently).
          //
          // At this point, we do not know which one is easier to reconstruct by
          // matching, so we add `candOb.second` to the set of equivalent
          // builtin terms corresponding to `k` and match against both terms.
          d_obInfo[repOb].addBuiltin(candOb.second);
          d_stnInfo[stn].setBuiltinToOb(candOb.second, repOb);
        }
        else
        {
          // otherwise, create a new obligation of the corresponding sygus type
          newVar = sm->mkDummySkolem("sygus_rcons", stn);
          d_obInfo.emplace(newVar, candOb.second);
          d_stnInfo[stn].setBuiltinToOb(candOb.second, newVar);
          // if the candidate obligation is a constant and the grammar allows
          // random constants
          if (candOb.second.isConst()
              && k.getType().getDType().getSygusAllowConst())
          {
            // then immediately solve the obligation
            markSolved(newVar, d_tds->getProxyVariable(stn, candOb.second));
          }
          else
          {
            // otherwise, add this candidate obligation to this list of
            // obligations
            obsPrime[stn].emplace(newVar);
          }
        }
        subs.emplace_back(datatypes::utils::builtinVarToSygus(candOb.first),
                          newVar);
      }
      // replace original free vars in sz with new ones
      if (!subs.empty())
      {
        sz = sz.substitute(subs.cbegin(), subs.cend());
      }
      // sz is solved if it has no sub-obligations or if all of them are solved
      bool isSolved = true;
      for (const std::pair<Node, Node>& sub : subs)
      {
        if (d_sol[sub.second].isNull())
        {
          isSolved = false;
          d_subObs[sz].push_back(sub.second);
        }
      }

      if (isSolved)
      {
        // As it traverses sz, substitute populates its input cache with TNodes
        // that are not preserved by this module and maybe destroyed after the
        // method call. To avoid referencing those unsafe TNodes throughout this
        // module, we pass a iterators of d_sol instead.
        Node s = sz.substitute(d_sol.cbegin(), d_sol.cend());
        markSolved(k, s);
      }
      else
      {
        // add sz as a possible solution to obligation k
        d_obInfo[k].addCandidateSolution(sz);
        d_parentOb[sz] = k;
        d_obInfo[d_subObs[sz].back()].addCandidateSolutionToWatchSet(sz);
      }
    }
  }

  return obsPrime;
}

void SygusReconstruct::markSolved(Node k, Node s)
{
  // return if obligation k is already solved
  if (!d_sol[k].isNull())
  {
    return;
  }

  Trace("sygus-rcons") << "sol: " << s << std::endl;
  Trace("sygus-rcons") << "builtin sol: " << datatypes::utils::sygusToBuiltin(s)
                       << std::endl;

  // First, mark `k` as solved
  d_obInfo[k].addCandidateSolution(s);
  d_sol[k] = s;
  d_parentOb[s] = k;

  std::vector<Node> stack;
  stack.push_back(k);

  while (!stack.empty())
  {
    Node curr = stack.back();
    stack.pop_back();

    // for each partial solution/parent of the now solved obligation `curr`
    for (Node parent : d_obInfo[curr].getWatchSet())
    {
      // remove `curr` and (possibly) other solved obligations from its list
      // of children
      while (!d_subObs[parent].empty()
             && !d_sol[d_subObs[parent].back()].isNull())
      {
        d_subObs[parent].pop_back();
      }

      // if the partial solution does not have any more children...
      if (d_subObs[parent].empty())
      {
        // then it is completely solved and can be used as a solution of its
        // corresponding obligation
        // pass iterators of d_sol to avoid populating it with unsafe TNodes
        Node parentSol = parent.substitute(d_sol.cbegin(), d_sol.cend());
        Node parentOb = d_parentOb[parent];
        // proceed only if parent obligation is not already solved
        if (d_sol[parentOb].isNull())
        {
          d_obInfo[parentOb].addCandidateSolution(parentSol);
          d_sol[parentOb] = parentSol;
          d_parentOb[parentSol] = parentOb;
          // repeat the same process for the parent obligation
          stack.push_back(parentOb);
        }
      }
      else
      {
        // if it does have remaining children, add it to the watch list of one
        // of them (picked arbitrarily)
        d_obInfo[d_subObs[parent].back()].addCandidateSolutionToWatchSet(
            parent);
      }
    }
  }
}

void SygusReconstruct::initialize(TypeNode stn)
{
  std::vector<Node> builtinVars;

  // Cache the sygus variables introduced by the problem (which we treat as
  // ground terms when calling the `match` method) as opposed to the sygus
  // variables introduced by the enumerators (which we treat as bound
  // variables).
  for (Node sv : stn.getDType().getSygusVarList())
  {
    builtinVars.push_back(datatypes::utils::sygusToBuiltin(sv));
    d_sygusVars.emplace(datatypes::utils::sygusToBuiltin(sv),
                        datatypes::utils::sygusToBuiltin(sv));
  }

  SygusTypeInfo stnInfo;
  stnInfo.initialize(d_tds, stn);

  // find the non-terminals of the grammar
  std::vector<TypeNode> sfTypes;
  stnInfo.getSubfieldTypes(sfTypes);

  // initialize the enumerators and candidate rewrite databases. Notice here
  // that we treat the sygus variables introduced by the problem as bound
  // variables (needed for making sure that obligations are equal). This is fine
  // as we will never add variables that were introduced by the enumerators to
  // the database.
  for (TypeNode tn : sfTypes)
  {
    d_stnInfo[tn].initialize(d_tds, d_stats, tn, builtinVars);
  }
}

void SygusReconstruct::removeSolvedObs(TypeObligationSetMap& unsolvedObs)
{
  for (std::pair<const TypeNode, ObligationSet>& tempPair : unsolvedObs)
  {
    ObligationSet::iterator it = tempPair.second.begin();
    while (it != tempPair.second.end())
    {
      if (d_sol[*it].isNull())
      {
        ++it;
      }
      else
      {
        it = tempPair.second.erase(it);
      }
    }
  }
}

Node SygusReconstruct::mkGround(Node n) const
{
  // get the set of bound variables in n
  std::unordered_set<TNode, TNodeHashFunction> vars;
  expr::getVariables(n, vars);

  std::unordered_map<TNode, TNode, TNodeHashFunction> subs;

  // generate a ground value for each one of those variables
  for (const TNode& var : vars)
  {
    subs.emplace(var, var.getType().mkGroundValue());
  }

  // substitute the variables with ground values
  return n.substitute(subs);
}

bool SygusReconstruct::notify(Node s,
                              Node n,
                              std::vector<Node>& vars,
                              std::vector<Node>& subs)
{
  for (size_t i = 0; i < vars.size(); ++i)
  {
    // We consider sygus variables as ground terms. So, if they are not equal to
    // their substitution, then s is not matchable with n and we try the next
    // term s. Example: If s = (+ z x) and n = (+ z y), then s is not matchable
    // with n and we return true
    if (d_sygusVars.find(vars[i]) != d_sygusVars.cend() && vars[i] != subs[i])
    {
      return true;
    }
  }
  // Note: false here means that we finally found an s that is matchable with n,
  // so we should not add n to the pool
  return false;
}

void SygusReconstruct::clear()
{
  d_obInfo.clear();
  d_stnInfo.clear();
  d_sol.clear();
  d_subObs.clear();
  d_parentOb.clear();
  d_sygusVars.clear();
  d_poolTrie.clear();
}

void SygusReconstruct::printPool(
    const std::unordered_map<TypeNode, std::vector<Node>, TypeNodeHashFunction>&
        pool) const
{
  Trace("sygus-rcons") << "\nPool:\n[";

  for (const std::pair<const TypeNode, std::vector<Node>>& pair : pool)
  {
    Trace("sygus-rcons") << std::endl << pair.first << ":\n[" << std::endl;

    for (const Node& sygusTerm : pair.second)
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

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
