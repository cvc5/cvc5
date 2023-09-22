/******************************************************************************
 * Top contributors (to current version):
 *   Abdalrhman Mohamed, Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation for Sygus reconstruct.
 */

#include "theory/quantifiers/sygus/sygus_reconstruct.h"

#include "expr/dtype_cons.h"
#include "expr/node_algorithm.h"
#include "options/quantifiers_options.h"
#include "printer/printer.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/rewriter.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
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

  // add the main obligation to the set of obligations
  // paramaters stn and sol constitute the main obligation to satisfy
  d_obs.push_back(std::make_unique<RConsObligation>(stn, sol));
  d_stnInfo[stn].setBuiltinToOb(sol, d_obs[0].get());
  RConsObligation* ob0 = d_obs[0].get();
  Node k0 = ob0->getSkolem();

  if (options().quantifiers.cegqiSingleInvReconstruct
      == cvc5::internal::options::CegqiSingleInvRconsMode::TRY)
  {
    fast(sol, stn, reconstructed);
  }
  else
  {
    main(sol, stn, reconstructed, enumLimit);
  }

  if (Trace("sygus-rcons").isConnected())
  {
    RConsObligation::printCandSols(ob0, d_obs);
    printPool();
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
  Printer::getPrinter(warning())->toStreamCmdFailure(
      warning(), "Cannot get synth function: reconstruction to syntax failed.");
  return Node::null();
}

void SygusReconstruct::main(Node sol,
                            TypeNode stn,
                            int8_t& reconstructed,
                            uint64_t enumLimit)
{
  bool noLimit = options().quantifiers.cegqiSingleInvReconstruct
                 == cvc5::internal::options::CegqiSingleInvRconsMode::ALL;

  // Skolem of the main obligation
  Node k0 = d_obs[0]->getSkolem();

  // a set of builtin terms to reconstruct for each sygus datatype
  TypeBuiltinSetMap termsToRecons;
  termsToRecons[stn].emplace(sol);

  uint64_t count = 0;

  // We need to add the main obligation to the crd in case it cannot be broken
  // down by matching. By doing so, we can solve the obligation using
  // enumeration and crd (if it is in the grammar)
  d_stnInfo[stn].addTerm(sol);

  // procedure
  while (d_sol[k0].isNull() && (noLimit || count < enumLimit))
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
        d_pool[pair.first].push_back(sz);
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
      TypeBuiltinSetMap termsToReconsDPrime;
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
            for (const Node& sz : d_pool[pair.first])
            {
              // try to match each newly generated and cached term with patterns
              // in pool
              TypeBuiltinSetMap temp = matchNewObs(t, sz);
              // cache the new terms for later processing
              for (const std::pair<const TypeNode, BuiltinSet>& tempPair : temp)
              {
                termsToReconsDPrime[tempPair.first].insert(
                    tempPair.second.cbegin(), tempPair.second.cend());
              }
            }
          }
        }
      }
      termsToReconsPrime = std::move(termsToReconsDPrime);
    }
    // remove reconstructed terms from termsToRecons
    removeReconstructedTerms(termsToRecons);
    ++count;
  }
}

void SygusReconstruct::fast(Node sol, TypeNode stn, int8_t& reconstructed)
{
  NodeManager* nm = NodeManager::currentNM();

  Assert(stn.isDatatype());
  Assert(stn.getDType().isSygus());
  SygusTypeInfo sti;
  sti.initialize(d_tds, stn);
  std::vector<TypeNode> stns;
  sti.getSubfieldTypes(stns);
  std::map<cvc5::internal::TypeNode, int> varCount;

  // add the constructors for each sygus datatype to the pool
  for (const TypeNode& cstn : stns)
  {
    for (const std::shared_ptr<DTypeConstructor>& cons :
         cstn.getDType().getConstructors())
    {
      if (cons->getNumArgs() == 0)
      {
        // just like in the main procedure, add no-argument constructors
        // directly to the crd
        Node sz = nm->mkNode(Kind::APPLY_CONSTRUCTOR, cons->getConstructor());
        Node builtin = datatypes::utils::sygusToBuiltin(sz);
        Node rep = d_stnInfo[cstn].addTerm(builtin);
        RConsObligation* ob = d_stnInfo[cstn].builtinToOb(rep);
        // check if the enumerated term solves an obligation
        if (ob == nullptr)
        {
          // if not, create an "artifical" obligation whose solution would be
          // the enumerated term
          d_obs.push_back(std::make_unique<RConsObligation>(cstn, builtin));
          d_stnInfo[cstn].setBuiltinToOb(builtin, d_obs.back().get());
          ob = d_obs.back().get();
        }
        // mark the obligation as solved
        markSolved(ob, sz);
      }
      else
      {
        std::vector<Node> args;
        args.push_back(cons->getConstructor());
        // populate each constructor argument with a free variable of the
        // corresponding type
        for (const std::shared_ptr<cvc5::internal::DTypeSelector>& arg : cons->getArgs())
        {
          args.push_back(d_tds->getFreeVarInc(arg->getRangeType(), varCount));
        }
        Node sz = nm->mkNode(Kind::APPLY_CONSTRUCTOR, args);
        d_pool[cstn].push_back(sz);
      }
    }
  }

  // a set of builtin terms to reconstruct for each sygus datatype
  TypeBuiltinSetMap termsToRecons;
  termsToRecons[stn].emplace(sol);

  // match phase of the rcons procedure
  while (!termsToRecons.empty())
  {
    // a temporary set of new terms to reconstruct cached for later processing
    TypeBuiltinSetMap termsToReconsPrime;
    for (const std::pair<const TypeNode, BuiltinSet>& pair : termsToRecons)
    {
      for (const Node& t : pair.second)
      {
        RConsObligation* ob = d_stnInfo[pair.first].builtinToOb(t);
        if (d_sol[ob->getSkolem()].isNull())
        {
          Trace("sygus-rcons") << "ob: " << *ob << std::endl;
          for (const Node& sz : d_pool[pair.first])
          {
            // try to match each newly generated and cached term with patterns
            // in pool
            TypeBuiltinSetMap temp = matchNewObs(t, sz);
            // cache the new terms for later processing
            for (const std::pair<const TypeNode, BuiltinSet>& tempPair : temp)
            {
              termsToReconsPrime[tempPair.first].insert(
                  tempPair.second.cbegin(), tempPair.second.cend());
            }
          }
        }
      }
    }
    termsToRecons = std::move(termsToReconsPrime);
  }
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
  if (match(t, datatypes::utils::sygusToBuiltin(sz), matches))
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

bool SygusReconstruct::match(Node t, Node tz, NodePairMap& subs)
{
  // rewrite pattern and replace n-ary ops with binary ones before performing
  // simple pattern-matching.
  return expr::match(convert(rewrite(tz)), convert(t), subs);
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
  NodeManager* nm = NodeManager::currentNM();
  for (const TNode& var : vars)
  {
    subs.emplace(var, nm->mkGroundValue(var.getType()));
  }

  // substitute the variables with ground values
  return n.substitute(subs);
}

bool SygusReconstruct::notify(Node s,
                              Node n,
                              std::vector<Node>& vars,
                              std::vector<Node>& subs)
{
  // If we are too aggressive in filtering enumerated shapes, we may miss some
  // that speedup reconstruction time. So, for now, we disable filtering.
  return true;
}

Node SygusReconstruct::postConvert(Node n)
{
  Kind k = n.getKind();
  if (NodeManager::isNAryKind(n.getKind()))
  {
    if (n.getNumChildren() > 2)
    {
      NodeManager* nm = NodeManager::currentNM();
      Node np = n[0];
      for (size_t i = 1, num = n.getNumChildren(); i < num; ++i)
      {
        np = nm->mkNode(k, np, n[i]);
      }
      return np;
    }
  }
  return Node::null();
}

void SygusReconstruct::clear()
{
  d_obs.clear();
  d_stnInfo.clear();
  d_sol.clear();
  d_subObs.clear();
  d_parentOb.clear();
  d_sygusVars.clear();
  d_pool.clear();
  d_poolTrie.clear();
}

void SygusReconstruct::printPool() const
{
  Trace("sygus-rcons") << std::endl << "Pool:" << std::endl << '{';

  for (const std::pair<const TypeNode, std::vector<Node>>& pair : d_pool)
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
}  // namespace cvc5::internal
