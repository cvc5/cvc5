/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Hanna Lachnitt, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities for resolution proofs.
 */

#include "proof/resolution_proofs_util.h"

#include "proof/proof.h"
#include "proof/proof_checker.h"
#include "proof/proof_node_manager.h"

namespace cvc5::internal {
namespace proof {

/** The information relevant for converting MACRO_RESOLUTION steps into
 * CHAIN_RESOLUTION+FACTORING steps when "crowding literals" are present. See
 * `ProofPostprocessCallback::eliminateCrowdingLits` for more information. */
struct CrowdingLitInfo
{
  CrowdingLitInfo(size_t lastInclusion = static_cast<size_t>(-1),
                  size_t eliminator = static_cast<size_t>(-1),
                  bool onlyCrowdAndConcLitsInElim = false,
                  size_t maxSafeMovePosition = static_cast<size_t>(-1))
      : d_lastInclusion(lastInclusion),
        d_eliminator(eliminator),
        d_onlyCrowdAndConcLitsInElim(onlyCrowdAndConcLitsInElim),
        d_maxSafeMovePosition(maxSafeMovePosition)
  {
  }
  /* Index of last (left-to-right) premise to introduce this crowding literal */
  size_t d_lastInclusion;
  /* Index of last premise to eliminate this crowding literal */
  size_t d_eliminator;
  /* Whether there are only crowding/conclusion literals in the eliminator. */
  bool d_onlyCrowdAndConcLitsInElim;
  /* Maximum position to which the eliminator premise can be moved without
   * changing the behavior of the resolution chain. Note this only applies when
   * d_onlyCrowdAndConcLitsInElim is true. */
  size_t d_maxSafeMovePosition;
};

std::ostream& operator<<(std::ostream& out, CrowdingLitInfo info)
{
  out << "{" << info.d_lastInclusion << ", " << info.d_eliminator << ", ";
  if (info.d_onlyCrowdAndConcLitsInElim)
  {
    out << "true, " << info.d_maxSafeMovePosition;
  }
  else
  {
    out << "false";
  }
  out << "}";
  return out;
}

Node eliminateCrowdingLits(bool reorderPremises,
                           const std::vector<Node>& clauseLits,
                           const std::vector<Node>& targetClauseLits,
                           const std::vector<Node>& children,
                           const std::vector<Node>& args,
                           CDProof* cdp,
                           ProofNodeManager* pnm)
{
  Trace("crowding-lits") << push;
  Trace("crowding-lits") << "Clause lits: " << clauseLits << "\n";
  Trace("crowding-lits") << "Target lits: " << targetClauseLits << "\n\n";
  std::vector<Node> newChildren{children}, newArgs{args};
  NodeManager* nm = NodeManager::currentNM();
  Node trueNode = nm->mkConst(true);
  // get crowding lits and the position of the last clause that includes
  // them. The factoring step must be added after the last inclusion and before
  // its elimination.
  std::unordered_set<TNode> crowding;
  size_t childrenSize = children.size(), numCrowding = 0;
  std::vector<std::pair<Node, size_t>> lastInclusion;
  // for each crowding lit, the information that is used to eliminate it
  std::map<Node, CrowdingLitInfo> crowdLitsInfo;
  // positions of eliminators of crowding literals, which are the positions of
  // the clauses that eliminate crowding literals *after* their last inclusion
  std::vector<size_t> eliminators;
  for (size_t i = 0, size = clauseLits.size(); i < size; ++i)
  {
    // repeated crowding literal or conclusion literal
    if (crowding.count(clauseLits[i])
        || std::find(
               targetClauseLits.begin(), targetClauseLits.end(), clauseLits[i])
               != targetClauseLits.end())
    {
      continue;
    }
    Node crowdLit = clauseLits[i];
    crowding.insert(crowdLit);
    Trace("crowding-lits3") << "crowding lit " << crowdLit << "\n";
    // found crowding lit, now get its last inclusion position, which is the
    // position of the last resolution link that introduces the crowding
    // literal. Note that this position has to be *before* the last link, as a
    // link *after* the last inclusion must eliminate the crowding literal.
    size_t j;
    for (j = childrenSize - 1; j > 0; --j)
    {
      // notice that only non-singleton clauses may be introducing the
      // crowding literal, so we only care about non-singleton OR nodes. We
      // check then against the kind and whether the whole OR node occurs as a
      // pivot of the respective resolution
      if (newChildren[j - 1].getKind() != kind::OR)
      {
        continue;
      }
      uint64_t pivotIndex = 2 * (j - 1);
      if (newArgs[pivotIndex] == newChildren[j - 1]
          || newArgs[pivotIndex].notNode() == newChildren[j - 1])
      {
        continue;
      }
      if (std::find(
              newChildren[j - 1].begin(), newChildren[j - 1].end(), crowdLit)
          != newChildren[j - 1].end())
      {
        break;
      }
    }
    Assert(j > 0);
    lastInclusion.emplace_back(crowdLit, j - 1);
    CrowdingLitInfo info;
    info.d_lastInclusion = j - 1;

    Trace("crowding-lits3") << "last inc " << j - 1 << "\n";
    // get elimination position, starting from the following link as the last
    // inclusion one. The result is the last (in the chain, but first from
    // this point on) resolution link that eliminates the crowding literal. A
    // literal l is eliminated by a link if it contains a literal l' with
    // opposite polarity to l.
    for (; j < childrenSize; ++j)
    {
      bool posFirst = newArgs[(2 * j) - 1] == trueNode;
      Node pivot = newArgs[(2 * j)];
      Trace("crowding-lits3")
          << "\tcheck w/ args " << posFirst << " / " << pivot << "\n";
      // To eliminate the crowding literal (crowdLit), the clause must contain
      // it with opposite polarity. There are three successful cases,
      // according to the pivot and its sign
      //
      // - crowdLit is the same as the pivot and posFirst is true, which means
      //   that the clause contains its negation and eliminates it
      //
      // - crowdLit is the negation of the pivot and posFirst is false, so the
      //   clause contains the node whose negation is crowdLit. Note that this
      //   case may either be crowdLit.notNode() == pivot or crowdLit ==
      //   pivot.notNode().
      if ((crowdLit == pivot && posFirst)
          || (crowdLit.notNode() == pivot && !posFirst)
          || (pivot.notNode() == crowdLit && !posFirst))
      {
        Trace("crowding-lits3") << "\t\tfound it!\n";
        eliminators.push_back(j);
        break;
      }
    }
    info.d_eliminator = eliminators.back();
    crowdLitsInfo[crowdLit] = info;
    Trace("crowding-lits3") << "last inc " << info.d_lastInclusion << ", elim "
                            << info.d_eliminator << "\n";
    AlwaysAssert(j < childrenSize);
  }
  Assert(!lastInclusion.empty());
  Trace("crowding-lits") << "..total of " << lastInclusion.size()
                         << " crowding literals\n";
  numCrowding = lastInclusion.size();
  // order map so that we process crowding literals in the order of the clauses
  // that last introduce them
  auto cmp = [](std::pair<Node, size_t>& a, std::pair<Node, size_t>& b) {
    return a.second < b.second;
  };
  std::sort(lastInclusion.begin(), lastInclusion.end(), cmp);
  // order eliminators
  std::sort(eliminators.begin(), eliminators.end());
  if (reorderPremises)
  {
    // compute extra information. We are trying to determine if we can move
    // crowding literal eliminators further to the right in the resolution
    // chain. This will reduce the number of divisions to the chain to be made
    // in the expansion below. Currently we determine this moving worthwhile
    // when the eliminator has no non-crowding, non-conclusion, non-pivot
    // literals, since they would necessarily be eliminated somewhere down the
    // road, and moving the premise beyond that point would break the resolution
    // chain. While this may also happen for conclusion and other crowding
    // literals, we can compute the safe point to move relatively cheaply.
    for (size_t i = 0; i < numCrowding; ++i)
    {
      Node crowdingLit = lastInclusion[i].first;
      size_t elim = crowdLitsInfo[crowdingLit].d_eliminator;
      // Since this primise is an eliminator, if it's an OR it can only be a
      // singleton if the crowding literal is its negation.
      size_t maxSafeMove = childrenSize,
             numLits = (newChildren[elim].getKind() != kind::OR
                        || (crowdingLit.getKind() == kind::NOT
                            && crowdingLit[0] == newChildren[elim]))
                           ? 1
                           : newChildren[elim].getNumChildren();
      // unit eliminators can be moved to the end
      if (numLits == 1)
      {
        Trace("crowding-lits2") << "....elim " << elim << " is unit (of " << i
                                << "-th crowding lit)\n";
        crowdLitsInfo[lastInclusion[i].first].d_onlyCrowdAndConcLitsInElim =
            true;
        crowdLitsInfo[lastInclusion[i].first].d_maxSafeMovePosition =
            maxSafeMove;
        continue;
      }
      // how many non-crowding non-conclusion lits
      uint32_t regularLits = 0;
      // only search while it's possible (no non-crowding, non-conclusion,
      // non-pivot literals) or worthwhile (would move at least one
      // position). Note that there will always be at least one "regular"
      // literal, i.e., the pivot that eliminates the crowding literal.
      for (size_t j = 0;
           j < numLits && regularLits <= 1 && (maxSafeMove - elim) > 1;
           ++j)
      {
        bool isCrowdingLit = crowding.count(newChildren[elim][j]);
        // if not crowding and not in conclusion it's a regular literal
        if (!isCrowdingLit
            && std::find(targetClauseLits.begin(),
                         targetClauseLits.end(),
                         newChildren[elim][j])
                   == targetClauseLits.end())
        {
          regularLits++;
          continue;
        }
        // If it's a crowding literal we know it's unsafe to move this premise
        // beyond its last inclusion
        if (isCrowdingLit)
        {
          Assert(crowdLitsInfo.find(newChildren[elim][j])
                 != crowdLitsInfo.end());
          size_t lastInc = crowdLitsInfo[newChildren[elim][j]].d_lastInclusion;
          maxSafeMove = lastInc < maxSafeMove ? lastInc : maxSafeMove;
        }
        // We check the pivots of the steps until the current limit
        // (maxSafeMove). If this literal is a pivot in any such step then it is
        // unsafe to move the eliminator beyond it. That then becomes the new
        // limit. The literal is such a pivot if it matches a lhs pivot, i.e.,
        // the same as a (pivot, +pol) or the negation of a (pivot, -pol).
        for (size_t k = 2 * (elim + 1) - 1, checkLim = (2 * maxSafeMove) - 1;
             k < checkLim;
             k = k + 2)
        {
          bool posPivot = newArgs[k] == trueNode;
          if ((newChildren[elim][j] == newArgs[k + 1] && posPivot)
              || (newChildren[elim][j] == newArgs[k + 1].notNode()
                  && !posPivot))
          {
            maxSafeMove = (k + 1) / 2;
            break;
          }
        }
      }
      // If there is a single regular literal, all other are either crowiding or
      // conclusion literals.
      if (regularLits == 1 && maxSafeMove > elim && maxSafeMove - elim > 1)
      {
        Trace("crowding-lits2")
            << "....elim " << elim << " has only crowd/conc lits (of " << i
            << "-th crowding lit). MaxSafeMove: " << maxSafeMove << "\n";
        crowdLitsInfo[lastInclusion[i].first].d_onlyCrowdAndConcLitsInElim =
            true;
        crowdLitsInfo[lastInclusion[i].first].d_maxSafeMovePosition =
            maxSafeMove;
      }
    }
    if (TraceIsOn("crowding-lits"))
    {
      Trace("crowding-lits") << "crowding lits last inclusion:\n";
      for (size_t i = 0, size = lastInclusion.size(); i < size; ++i)
      {
        Node crowdingLit = lastInclusion[i].first;
        Trace("crowding-lits")
            << "\t- [" << crowdLitsInfo[crowdingLit].d_lastInclusion << "] : {"
            << crowdLitsInfo[crowdingLit].d_eliminator << "} " << crowdingLit
            << "\n";
        if (crowdLitsInfo[crowdingLit].d_onlyCrowdAndConcLitsInElim)
        {
          Trace("crowding-lits")
              << "\t\t- onlyCrowdAndConcLitsInElim; maxSafeMove: "
              << crowdLitsInfo[crowdingLit].d_maxSafeMovePosition << "\n";
        }
      }
    }
    // Every eliminator can be moved, without loss of generality, up to the
    // immediate position before a clause that eliminates one its non-pivot
    // literals. We also add restrict the move to be up to the minimal last
    // inclusion of a crowding literal, as moving beyond that would require
    // recomputing the information of that crowding literal. So for example, an
    // eliminator in position i, which has only crowding/conclusion literals
    // that are not eliminated before a minimun last inclusion position i+1000,
    // can be moved anywhere in the premises between i and i+999. This is the
    // case since all the literals that are introduced by the eliminator are
    // going to be killed (or preserved for conclusion) only starting at i+1000.
    //
    // Given the above we proceed, based on the crowding lits information, to
    // move up to maximum all eliminators.
    //
    // We will use std::rotate to do the moving of the premises, which moves to
    // target position (first argument) an interval [l, u), where l and u are
    // the second and third arguments. For each eliminator in position i that
    // has a minimum crowding last inclusion k bigger than i + 1, we do the
    // moving with arguments (i, i+1, k). As a consequence newChildren[i] will
    // move to position k-1. Since we are moving premises we also need to move
    // arguments. The polarity/pivot of the eliminator in position i are (2*i)
    // -1 and 2*i. So the rotation in the arguments is with (2*i-1, 2*i+1,
    // 2*k-1).
    Trace("smt-proof-pp-debug") << "Moving eliminators\n" << push;
    // This guys will be used to search for the position of the eliminator
    // within newChildren after the moves below. This is necessary because an
    // eliminator originally moved to position k can end up in some position
    // before k if any other eliminator is moved ahead of k
    uint32_t counterMoved = 0;
    for (size_t i = 0; i < numCrowding; ++i)
    {
      Node crowdingLit = lastInclusion[i].first;
      size_t elim = crowdLitsInfo[crowdingLit].d_eliminator;
      size_t maxSafeMove = crowdLitsInfo[crowdingLit].d_maxSafeMovePosition;
      Assert(maxSafeMove >= elim) << i << "-th crowding lit " << crowdingLit
                                  << " has info " << crowdLitsInfo[crowdingLit];
      if (!crowdLitsInfo[crowdingLit].d_onlyCrowdAndConcLitsInElim
          || maxSafeMove - elim <= 1)
      {
        continue;
      }
      ++counterMoved;
      Trace("crowding-lits")
          << "..move elim " << elim << " to " << maxSafeMove - 1 << "\n";
      std::rotate(newChildren.begin() + elim,
                  newChildren.begin() + elim + 1,
                  newChildren.begin() + maxSafeMove);
      std::rotate(newArgs.begin() + (2 * elim) - 1,
                  newArgs.begin() + (2 * elim) + 1,
                  newArgs.begin() + (2 * maxSafeMove) - 1);
      // Being pedantic here we should assert that the rotated
      // newChildren/newArgs still yield the same conclusion with a
      // MACRO_RESOLUTION step. However this can be very expensive to check, so
      // we don't do this. Only if one is debugging this code this test should
      // be added.

      // Now we need to update the indices, since we have changed newChildren.
      // For every crowding literal whose information indices are in the
      // interval [elim+1, maxSafeMove), these indices should be decremented
      // by 1.
      for (std::pair<const Node, CrowdingLitInfo>& p : crowdLitsInfo)
      {
        bool updated = false;
        // guarantee we update who we just moved...
        if (p.first == crowdingLit)
        {
          p.second.d_eliminator = maxSafeMove - 1;
          continue;
        }
        // can update lastInclusion, eliminator and maxSafeMovePosition
        if (p.second.d_lastInclusion >= elim + 1
            && p.second.d_lastInclusion < maxSafeMove)
        {
          --p.second.d_lastInclusion;
          updated = true;
        }
        if (p.second.d_eliminator >= elim + 1
            && p.second.d_eliminator < maxSafeMove)
        {
          --p.second.d_eliminator;
          updated = true;
        }
        if (p.second.d_onlyCrowdAndConcLitsInElim
            && p.second.d_maxSafeMovePosition >= elim + 1
            && p.second.d_maxSafeMovePosition < maxSafeMove)
        {
          --p.second.d_maxSafeMovePosition;
          updated = true;
        }
        if (updated)
        {
          Trace("crowding-lits")
              << "\tUpdated other crowding lit " << p.first << " info to "
              << crowdLitsInfo[p.first] << "\n";
        }
      }
    }
    Trace("smt-proof-pp-debug") << pop;
    if (counterMoved)
    {
      Trace("crowding-lits")
          << "..moved up " << counterMoved << " eliminators\n";
      Trace("smt-proof-pp-debug")
          << "Updating bookkeeping of lastInclusion/eliminators vectors\n";
      Trace("crowding-lits") << "New premises " << newChildren << "\n";
      Trace("crowding-lits") << "New args " << newArgs << "\n";
      // lastInclusion order will not have changed, so we just traverse in the
      // same way and update
      for (auto& p : lastInclusion)
      {
        p.second = crowdLitsInfo[p.first].d_lastInclusion;
      }
      // since eliminators may have changed drastically, we fully recompute
      eliminators.clear();
      for (const std::pair<const Node, CrowdingLitInfo>& p : crowdLitsInfo)
      {
        eliminators.push_back(p.second.d_eliminator);
      }
      std::sort(eliminators.begin(), eliminators.end());
    }
  }
  if (TraceIsOn("crowding-lits"))
  {
    Trace("crowding-lits") << "crowding lits last inclusion:\n";
    for (size_t i = 0, size = lastInclusion.size(); i < size; ++i)
    {
      Node crowdingLit = lastInclusion[i].first;
      Trace("crowding-lits")
          << "\t- [" << crowdLitsInfo[crowdingLit].d_lastInclusion << "] : {"
          << crowdLitsInfo[crowdingLit].d_eliminator << "} " << crowdingLit
          << "\n";
      if (crowdLitsInfo[crowdingLit].d_onlyCrowdAndConcLitsInElim)
      {
        Trace("crowding-lits")
            << "\t\t- onlyCrowdingInElim; maxSafeMove: "
            << crowdLitsInfo[lastInclusion[i].first].d_maxSafeMovePosition
            << "\n";
      }
    }
  }
  // TODO (cvc4-wishues/issues/77): implement also simpler version and compare
  //
  // We now start to break the chain, one step at a time. Naively this breaking
  // down would be one resolution/factoring to each crowding literal, but we can
  // merge some of the cases. We do the following:
  //
  //
  // lastClause   children[start] ... children[end]
  // ---------------------------------------------- CHAIN_RES
  //         C
  //    ----------- FACTORING
  //    lastClause'                children[start'] ... children[end']
  //    -------------------------------------------------------------- CHAIN_RES
  //                                    ...
  //
  // where
  //   lastClause_0 = children[0]
  //   start_0 = 1
  //   end_0 = eliminators[0] - 1
  //   start_i+1 = nextGuardedElimPos - 1
  //
  // The important point is how end_i+1 is computed. It is based on what we call
  // the "nextGuardedElimPos", i.e., the next elimination position that requires
  // removal of duplicates. The intuition is that a factoring step may eliminate
  // the duplicates of crowding literals l1 and l2. If the last inclusion of l2
  // is before the elimination of l1, then we can go ahead and also perform the
  // elimination of l2 without another factoring. However if another literal l3
  // has its last inclusion after the elimination of l2, then the elimination of
  // l3 is the next guarded elimination.
  //
  // To do the above computation then we determine, after a resolution/factoring
  // step, the first crowded literal to have its last inclusion after "end". The
  // first elimination position to be bigger than the position of that crowded
  // literal is the next guarded elimination position.
  size_t lastElim = 0;
  Node lastClause = newChildren[0];
  std::vector<Node> childrenRes;
  std::vector<Node> childrenResArgs;
  Node resPlaceHolder;
  size_t nextGuardedElimPos = eliminators[0];
  do
  {
    size_t start = lastElim + 1;
    size_t end = nextGuardedElimPos - 1;
    Trace("crowding-lits") << "res with:\n\t\tlastClause: " << lastClause
                           << "\n\t\tstart: " << start << "\n\t\tend: " << end
                           << "\n";
    childrenRes.push_back(lastClause);
    // note that the interval of insert is exclusive in the end, so we add 1
    childrenRes.insert(childrenRes.end(),
                       newChildren.begin() + start,
                       newChildren.begin() + end + 1);
    childrenResArgs.insert(childrenResArgs.end(),
                           newArgs.begin() + (2 * start) - 1,
                           newArgs.begin() + (2 * end) + 1);
    Trace("crowding-lits") << "\tres children: " << childrenRes << "\n";
    Trace("crowding-lits") << "\tres args: " << childrenResArgs << "\n";
    resPlaceHolder = pnm->getChecker()->checkDebug(PfRule::CHAIN_RESOLUTION,
                                                   childrenRes,
                                                   childrenResArgs,
                                                   Node::null(),
                                                   "");
    Trace("crowding-lits") << "resPlaceHorder: " << resPlaceHolder << "\n";
    Trace("crowding-lits") << "-------\n";
    cdp->addStep(
        resPlaceHolder, PfRule::CHAIN_RESOLUTION, childrenRes, childrenResArgs);
    // I need to add factoring if end < children.size(). Otherwise, this is
    // to be handled by the caller
    if (end < childrenSize - 1)
    {
      lastClause = pnm->getChecker()->checkDebug(
          PfRule::FACTORING, {resPlaceHolder}, {}, Node::null(), "");
      if (!lastClause.isNull())
      {
        cdp->addStep(lastClause, PfRule::FACTORING, {resPlaceHolder}, {});
        Trace("crowding-lits") << "Apply factoring.\n";
      }
      else
      {
        lastClause = resPlaceHolder;
      }
      Trace("crowding-lits") << "lastClause: " << lastClause << "\n";
    }
    else
    {
      lastClause = resPlaceHolder;
      break;
    }
    // update for next round
    childrenRes.clear();
    childrenResArgs.clear();
    lastElim = end;

    // find the position of the last inclusion of the next crowded literal
    size_t nextCrowdedInclusionPos = numCrowding;
    for (size_t i = 0; i < numCrowding; ++i)
    {
      if (lastInclusion[i].second > lastElim)
      {
        nextCrowdedInclusionPos = i;
        break;
      }
    }
    Trace("crowding-lits") << "nextCrowdedInclusion/Pos: "
                           << lastInclusion[nextCrowdedInclusionPos].second
                           << "/" << nextCrowdedInclusionPos << "\n";
    // if there is none, then the remaining literals will be used in the next
    // round
    nextGuardedElimPos = childrenSize;
    if (nextCrowdedInclusionPos != numCrowding)
    {
      nextGuardedElimPos = newChildren.size();
      for (size_t i = 0; i < numCrowding; ++i)
      {
        //  nextGuardedElimPos is the largest element of
        // eliminators bigger the next crowded literal's last inclusion
        if (eliminators[i] > lastInclusion[nextCrowdedInclusionPos].second)
        {
          nextGuardedElimPos = eliminators[i];
          break;
        }
      }
      Assert(nextGuardedElimPos < childrenSize);
    }
    Trace("crowding-lits") << "nextGuardedElimPos: " << nextGuardedElimPos
                           << "\n";
  } while (true);
  Trace("crowding-lits") << pop;
  return lastClause;
}

bool isSingletonClause(TNode res,
                       const std::vector<Node>& children,
                       const std::vector<Node>& args)
{
  if (res.getKind() != kind::OR)
  {
    return true;
  }
  size_t i;
  Node trueNode = NodeManager::currentNM()->mkConst(true);
  // Find out the last child to introduced res, if any. We only need to
  // look at the last one because any previous introduction would have
  // been eliminated.
  //
  // After the loop finishes i is the index of the child C_i that
  // introduced res. If i=0 none of the children introduced res as a
  // subterm and therefore it cannot be a singleton clause.
  for (i = children.size(); i > 0; --i)
  {
    // only non-singleton clauses may be introducing
    // res, so we only care about non-singleton or nodes. We check then
    // against the kind and whether the whole or node occurs as a pivot of
    // the respective resolution
    if (children[i - 1].getKind() != kind::OR)
    {
      continue;
    }
    size_t pivotIndex = (i != 1) ? 2 * (i - 1) - 1 : 1;
    if (args[pivotIndex] == children[i - 1]
        || args[pivotIndex].notNode() == children[i - 1])
    {
      continue;
    }
    // if res occurs as a subterm of a non-singleton premise
    if (std::find(children[i - 1].begin(), children[i - 1].end(), res)
        != children[i - 1].end())
    {
      break;
    }
  }

  // If res is a subterm of one of the children we still need to check if
  // that subterm is eliminated
  if (i > 0)
  {
    bool posFirst = (i == 1) ? (args[0] == trueNode)
                             : (args[(2 * (i - 1)) - 2] == trueNode);
    Node pivot = (i == 1) ? args[1] : args[(2 * (i - 1)) - 1];

    // Check if it is eliminated by the previous resolution step
    if ((res == pivot && !posFirst) || (res.notNode() == pivot && posFirst)
        || (pivot.notNode() == res && posFirst))
    {
      // We decrease i by one, since it could have been the case that i
      // was equal to children.size(), so that we return false in the end
      --i;
    }
    else
    {
      // Otherwise check if any subsequent premise eliminates it
      for (; i < children.size(); ++i)
      {
        posFirst = args[(2 * i) - 2] == trueNode;
        pivot = args[(2 * i) - 1];
        // To eliminate res, the clause must contain it with opposite
        // polarity. There are three successful cases, according to the
        // pivot and its sign
        //
        // - res is the same as the pivot and posFirst is true, which
        // means that the clause contains its negation and eliminates it
        //
        // - res is the negation of the pivot and posFirst is false, so
        // the clause contains the node whose negation is res. Note that
        // this case may either be res.notNode() == pivot or res ==
        // pivot.notNode().
        if ((res == pivot && posFirst) || (res.notNode() == pivot && !posFirst)
            || (pivot.notNode() == res && !posFirst))
        {
          break;
        }
      }
    }
  }
  // if not eliminated (loop went to the end), then it's a singleton
  // clause
  return i == children.size();
}

}  // namespace proof
}  // namespace cvc5::internal
