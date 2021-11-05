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
#include "smt/command.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/rewriter.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace quantifiers {

SygusReconstruct::SygusReconstruct(Env& env,
                                   TermDbSygus* tds,
                                   SygusStatistics& s)
    : EnvObj(env), d_tds(tds), d_stats(s)
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

  /** a set of builtin terms to reconstruct satisfied for each sygus datatype */
  TypeBuiltinSetMap termsToRecons;

  // add the main obligation to the set of obligations
  // paramaters stn and sol constitute the main obligation to satisfy
  d_obs.push_back(std::make_unique<RConsObligation>(stn, sol));
  termsToRecons[stn].emplace(sol);
  d_stnInfo[stn].setBuiltinToOb(sol, d_obs[0].get());
  RConsObligation* ob0 = d_obs[0].get();
  Node k0 = ob0->getSkolem();

  // We need to add the main obligation to the crd in case it cannot be broken
  // down by matching. By doing so, we can solve the obligation using
  // enumeration and crd (if it is in the grammar)
  d_stnInfo[stn].addTerm(sol);

  // the set of unique (up to rewriting) patterns/shapes in the grammar used by
  // matching
  std::unordered_map<TypeNode, std::vector<Node>> pool;

  uint64_t count = 0;

  // algorithm
  while (d_sol[k0].isNull() && count < enumLimit)
  {
    // enumeration phase
    // a temporary set of new terms to reconstruct cached for processing in the
    // match phase
    TypeBuiltinSetMap termsToReconsPrime;
    for (const std::pair<const TypeNode, BuiltinSet>& pair : termsToRecons)
    {
      // enumerate a new term
      Trace("sygus-rcons") << "enum: " << stn << ": ";
      Node sz = d_stnInfo[pair.first].nextEnum();
      if (sz.isNull())
      {
        continue;
      }
      Node builtin = rewrite(datatypes::utils::sygusToBuiltin(sz));
      // if enumerated term does not contain free variables, then its
      // corresponding obligation can be solved immediately
      if (sz.isConst())
      {
        Node rep = d_stnInfo[pair.first].addTerm(builtin);
        RConsObligation* ob = d_stnInfo[pair.first].builtinToOb(rep);
        // check if the enumerated term solves an obligation
        if (ob == nullptr)
        {
          // if not, create an "artifical" obligation whose solution would be
          // the enumerated term
          d_obs.push_back(
              std::make_unique<RConsObligation>(pair.first, builtin));
          d_stnInfo[pair.first].setBuiltinToOb(builtin, d_obs.back().get());
          ob = d_obs.back().get();
        }
        // mark the obligation as solved
        markSolved(ob, sz);
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
        for (const Node& t : pair.second)
        {
          RConsObligation* ob = d_stnInfo[pair.first].builtinToOb(t);
          if (d_sol[ob->getSkolem()].isNull())
          {
            Trace("sygus-rcons") << "ob: " << *ob << std::endl;
            // try to match builtin term `t` with the enumerated term sz
            TypeBuiltinSetMap temp = matchNewObs(t, sz);
            // cache the new obligations for processing in the match phase
            for (const std::pair<const TypeNode, BuiltinSet>& tempPair : temp)
            {
              termsToReconsPrime[tempPair.first].insert(
                  tempPair.second.cbegin(), tempPair.second.cend());
            }
          }
        }
      }
    }
    // match phase
    while (!termsToReconsPrime.empty())
    {
      // a temporary set of new terms to reconstruct cached for later processing
      TypeBuiltinSetMap obsDPrime;
      for (const std::pair<const TypeNode, BuiltinSet>& pair :
           termsToReconsPrime)
      {
        for (const Node& t : pair.second)
        {
          termsToRecons[pair.first].emplace(t);
          RConsObligation* ob = d_stnInfo[pair.first].builtinToOb(t);
          if (d_sol[ob->getSkolem()].isNull())
          {
            Trace("sygus-rcons") << "ob: " << *ob << std::endl;
            for (const Node& sz : pool[pair.first])
            {
              // try to match each newly generated and cached term with patterns
              // in pool
              TypeBuiltinSetMap temp = matchNewObs(t, sz);
              // cache the new terms for later processing
              for (const std::pair<const TypeNode, BuiltinSet>& tempPair : temp)
              {
                obsDPrime[tempPair.first].insert(tempPair.second.cbegin(),
                                                 tempPair.second.cend());
              }
            }
          }
        }
      }
      termsToReconsPrime = std::move(obsDPrime);
    }
    // remove reconstructed terms from termsToRecons
    removeReconstructedTerms(termsToRecons);
    ++count;
  }

  if (Trace("sygus-rcons").isConnected())
  {
    RConsObligation::printCandSols(ob0, d_obs);
    printPool(pool);
  }

  // if the main obligation is solved, return the solution
  if (!d_sol[k0].isNull())
  {
    reconstructed = 1;
    // The algorithm mostly works with rewritten terms and may not notice that
    // the original terms contain variables eliminated by the rewriter. For
    // example, rewrite((ite true 0 z)) = 0. In such cases, we replace those
    // variables with ground values.
    return d_sol[k0].isConst() ? Node(d_sol[k0]) : mkGround(d_sol[k0]);
  }

  // we ran out of elements, return null
  reconstructed = -1;
  warning() << CommandFailure(
      "Cannot get synth function: reconstruction to syntax failed.");
  return Node::null();
}

TypeBuiltinSetMap SygusReconstruct::matchNewObs(Node t, Node sz)
{
  TypeBuiltinSetMap termsToReconsPrime;

  // substitutions generated by match. Note that we might have already seen (and
  // even solved) obligations corresponsing to those substitutions
  NodePairMap matches;
  // the builtin terms corresponding to sygus variables in the grammar are bound
  // variables. However, we want the `match` method to treat them as ground
  // terms. So, we add redundant substitutions
  matches.insert(d_sygusVars.cbegin(), d_sygusVars.cend());

  // try to match the builtin term with the pattern sz
  if (expr::match(rewrite(datatypes::utils::sygusToBuiltin(sz)), t, matches))
  {
    // the bound variables z generated by the enumerators are reused across
    // enumerated terms, so we need to replace them with our own skolems
    NodePairMap subs;
    Trace("sygus-rcons") << "-- ct: " << sz << std::endl;
    // remove redundant substitutions
    for (const std::pair<const Node, Node>& pair : d_sygusVars)
    {
      matches.erase(pair.first);
    }
    // for each match
    for (const std::pair<const Node, Node>& match : matches)
    {
      TypeNode stn = datatypes::utils::builtinVarToSygus(match.first).getType();
      RConsObligation* newOb;
      // did we come across an equivalent obligation before?
      Node rep = d_stnInfo[stn].addTerm(match.second);
      RConsObligation* repOb = d_stnInfo[stn].builtinToOb(rep);
      if (repOb != nullptr)
      {
        // if so, use the original obligation
        newOb = repOb;
        // while `match.second` is equivalent to `rep`, it may be easier to
        // reconstruct than `rep`. For example:
        //
        // Grammar: S -> p | q | (not S) | (and S S) | (or S S)
        // rep = (= p q)
        // match.second = (or (and p q) (and (not p) (not q)))
        //
        // In this case, `match.second` is easy to reconstruct by matching
        // because it only uses operators that are already in the grammar.
        // `rep`, on the other hand, cannot be reconstructed by matching and
        // can only be solved by enumeration (currently).
        //
        // At this point, we do not know which one is easier to reconstruct by
        // matching, so we add `match.second` to the set of equivalent builtin
        // terms in `repOb` and match against both terms.
        if (repOb->getBuiltins().find(match.second)
            == repOb->getBuiltins().cend())
        {
          repOb->addBuiltin(match.second);
          d_stnInfo[stn].setBuiltinToOb(match.second, repOb);
          termsToReconsPrime[stn].emplace(match.second);
        }
      }
      else
      {
        // otherwise, create a new obligation of the corresponding sygus type
        d_obs.push_back(std::make_unique<RConsObligation>(stn, match.second));
        d_stnInfo[stn].setBuiltinToOb(match.second, d_obs.back().get());
        newOb = d_obs.back().get();
        // if the match is a constant and the grammar allows random constants
        if (match.second.isConst() && stn.getDType().getSygusAllowConst())
        {
          // then immediately solve the obligation
          markSolved(newOb, d_tds->getProxyVariable(stn, match.second));
        }
        else
        {
          // otherwise, add this match to the list of obligations
          termsToReconsPrime[stn].emplace(match.second);
        }
      }
      subs.emplace(datatypes::utils::builtinVarToSygus(match.first),
                   newOb->getSkolem());
    }
    // replace original free vars in sz with new ones
    if (!subs.empty())
    {
      sz = sz.substitute(subs.cbegin(), subs.cend());
    }
    // sz is solved if it has no sub-obligations or if all of them are solved
    bool isSolved = true;
    for (const std::pair<const Node, Node>& match : matches)
    {
      TypeNode stn = datatypes::utils::builtinVarToSygus(match.first).getType();
      RConsObligation* ob = d_stnInfo[stn].builtinToOb(match.second);
      if (d_sol[ob->getSkolem()].isNull())
      {
        isSolved = false;
        d_subObs[sz].push_back(ob);
      }
    }

    RConsObligation* ob = d_stnInfo[sz.getType()].builtinToOb(t);

    if (isSolved)
    {
      // As it traverses sz, substitute populates its input cache with TNodes
      // that are not preserved by this module and maybe destroyed after the
      // method call. To avoid referencing those unsafe TNodes throughout this
      // module, we pass a iterators of d_sol instead.
      Node s = sz.substitute(d_sol.cbegin(), d_sol.cend());
      markSolved(ob, s);
    }
    else
    {
      // add sz as a possible solution to ob
      ob->addCandidateSolution(sz);
      d_parentOb[sz] = ob;
      d_subObs[sz].back()->addCandidateSolutionToWatchSet(sz);
    }
  }

  return termsToReconsPrime;
}

void SygusReconstruct::markSolved(RConsObligation* ob, Node s)
{
  // return if ob is already solved
  if (!d_sol[ob->getSkolem()].isNull())
  {
    return;
  }

  Trace("sygus-rcons") << "sol: " << s << std::endl;
  Trace("sygus-rcons") << "builtin sol: " << datatypes::utils::sygusToBuiltin(s)
                       << std::endl;

  // First, mark ob as solved
  ob->addCandidateSolution(s);
  d_sol[ob->getSkolem()] = s;
  d_parentOb[s] = ob;

  std::vector<RConsObligation*> stack;
  stack.push_back(ob);

  while (!stack.empty())
  {
    RConsObligation* curr = stack.back();
    stack.pop_back();

    // for each partial solution/parent of the now solved obligation `curr`
    for (const Node& parent : curr->getWatchSet())
    {
      // remove `curr` and (possibly) other solved obligations from its list
      // of children
      while (!d_subObs[parent].empty()
             && !d_sol[d_subObs[parent].back()->getSkolem()].isNull())
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
        RConsObligation* parentOb = d_parentOb[parent];
        // proceed only if parent obligation is not already solved
        if (d_sol[parentOb->getSkolem()].isNull())
        {
          parentOb->addCandidateSolution(parentSol);
          d_sol[parentOb->getSkolem()] = parentSol;
          d_parentOb[parentSol] = parentOb;
          // repeat the same process for the parent obligation
          stack.push_back(parentOb);
        }
      }
      else
      {
        // if it does have remaining children, add it to the watch list of one
        // of them (picked arbitrarily)
        d_subObs[parent].back()->addCandidateSolutionToWatchSet(parent);
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
    d_stnInfo[tn].initialize(d_env, d_tds, d_stats, tn, builtinVars);
  }
}

void SygusReconstruct::removeReconstructedTerms(
    TypeBuiltinSetMap& termsToRecons)
{
  for (std::pair<const TypeNode, BuiltinSet>& pair : termsToRecons)
  {
    BuiltinSet::iterator it = pair.second.begin();
    while (it != pair.second.end())
    {
      if (d_sol[d_stnInfo[pair.first].builtinToOb(*it)->getSkolem()].isNull())
      {
        ++it;
      }
      else
      {
        it = pair.second.erase(it);
      }
    }
  }
}

Node SygusReconstruct::mkGround(Node n) const
{
  // get the set of bound variables in n
  std::unordered_set<TNode> vars;
  expr::getVariables(n, vars);

  std::unordered_map<TNode, TNode> subs;

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
  d_obs.clear();
  d_stnInfo.clear();
  d_sol.clear();
  d_subObs.clear();
  d_parentOb.clear();
  d_sygusVars.clear();
  d_poolTrie.clear();
}

void SygusReconstruct::printPool(
    const std::unordered_map<TypeNode, std::vector<Node>>& pool) const
{
  Trace("sygus-rcons") << std::endl << "Pool:" << std::endl << '{';

  for (const std::pair<const TypeNode, std::vector<Node>>& pair : pool)
  {
    Trace("sygus-rcons") << std::endl
                         << "  " << pair.first << ':' << std::endl
                         << "  [" << std::endl;

    for (const Node& sygusTerm : pair.second)
    {
      Trace("sygus-rcons")
          << "    "
          << rewrite(datatypes::utils::sygusToBuiltin(sygusTerm)).toString()
          << std::endl;
    }

    Trace("sygus-rcons") << "  ]" << std::endl;
  }

  Trace("sygus-rcons") << '}' << std::endl;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
