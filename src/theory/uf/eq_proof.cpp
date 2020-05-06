/*********************                                                        */
/*! \file eq_proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of a proof as produced by the equality engine.
 **
 **/

#include "theory/uf/eq_proof.h"

namespace CVC4 {
namespace theory {
namespace eq {

void EqProof::debug_print(const char* c,
                          unsigned tb,
                          PrettyPrinter* prettyPrinter) const
{
  std::stringstream ss;
  debug_print(ss, tb, prettyPrinter);
  Debug(c) << ss.str();
}
void EqProof::debug_print(std::ostream& os,
                          unsigned tb,
                          PrettyPrinter* prettyPrinter) const
{
  for (unsigned i = 0; i < tb; i++)
  {
    os << "  ";
  }

  if (prettyPrinter)
  {
    os << prettyPrinter->printTag(d_id);
  }
  else
  {
    os << static_cast<MergeReasonType>(d_id);
  }
  os << "(";
  if (d_children.empty() && d_node.isNull())
  {
    os << ")";
    return;
  }
  if (!d_node.isNull())
  {
    os << std::endl;
    for (unsigned i = 0; i < tb + 1; ++i)
    {
      os << "  ";
    }
    os << d_node << (!d_children.empty() ? "," : "");
  }
  unsigned size = d_children.size();
  for (unsigned i = 0; i < size; ++i)
  {
    os << std::endl;
    d_children[i]->debug_print(os, tb + 1, prettyPrinter);
    if (i < size - 1)
    {
      for (unsigned j = 0; j < tb + 1; ++j)
      {
        os << "  ";
      }
      os << ",";
    }
  }
  if (size > 0)
  {
    for (unsigned i = 0; i < tb; ++i)
    {
      os << "  ";
    }
  }
  os << ")" << std::endl;
}

void EqProof::cleanReflPremisesInTranstivity(std::vector<Node>& premises) const
{
  std::vector<Node> newPremises;
  unsigned size = premises.size();
  for (unsigned i = 0; i < size; ++i)
  {
    if (premises[i][0] == premises[i][1])
    {
      continue;
    }
    newPremises.push_back(premises[i]);
  }
  if (newPremises.size() != size)
  {
    Trace("eqproof-conv") << "EqProof::cleanReflPremisesInTranstivity: removed "
                          << newPremises.size() - size << " refl premises from "
                          << premises << "\n";
    premises.clear();
    premises.insert(premises.begin(), newPremises.begin(), newPremises.end());
  }
}

bool EqProof::foldTransitivityChildren(Node conclusion,
                                       std::vector<Node>& premises,
                                       CDProof* p) const
{
  // traverse premises to see if any of the form (= (= t1 t2) false)
  unsigned size = premises.size();
  unsigned termPos = 2, offending = size;
  for (unsigned i = 0; i < size; ++i)
  {
    Assert(premises[i].getKind() == kind::EQUAL);
    for (unsigned j = 0; j < 2; ++j)
    {
      if (premises[i][j].getKind() == kind::CONST_BOOLEAN
          && !premises[i][j].getConst<bool>()
          && premises[i][1 - j].getKind() == kind::EQUAL)
      {
        // there is only one offending equality
        Assert(offending == size);
        offending = i;
        termPos = 1 - j;
        break;
      }
    }
  }
  // if no equality of the searched form, nothing to do
  if (offending == size)
  {
    return false;
  }
  Assert(termPos == 0 || termPos == 1);
  Trace("eqproof-conv") << "EqProof::foldTransitivityChildren: found "
                           "offending equality at index "
                        << offending << " : " << premises[offending] << "\n";
  // an offending premise (= (= t1 t2) false) indicates we are concluding,
  // modulo symmetry, (= false true) or the disequality (= (t3 t4) false). The
  // former can be fixed by having the remaining premises derive, with
  // TRANSITIVITY, (= t1 t2), but the latter requires a MACRO_SR_PRED_TRANSFORM
  // step which will turn (= (= t1 t2) false) into (= (= t3 t4) false). The
  // assumption is that one of t1,t2 is synctatically equal to one of t3,t4 and
  // that the remaining premises allow deriving the equality of the other case.
  Node foldConclusion;
  bool inSubstCase;
  if ((conclusion[0].getKind() == kind::CONST_BOOLEAN
       && conclusion[1].getKind() != kind::CONST_BOOLEAN)
      || (conclusion[1].getKind() == kind::CONST_BOOLEAN
          && conclusion[0].getKind() != kind::CONST_BOOLEAN))
  {
    inSubstCase = true;
    Node premiseTerm = premises[offending][termPos];
    Node conclusionTerm = conclusion[0].getKind() == kind::CONST_BOOLEAN
                              ? conclusion[1]
                              : conclusion[0];
    // at least of the arguments of premiseTerm and conclusionTerm must be the
    // same. The other args will compose the conclusion of folding of the
    // remaining premises
    std::vector<Node> sub;
    for (unsigned i = 0; i < 2 && sub.empty(); ++i)
    {
      for (unsigned j = 0; j < 2; ++j)
      {
        if (premiseTerm[i] == conclusionTerm[j])
        {
          sub.push_back(premiseTerm[1 - i]);
          sub.push_back(conclusionTerm[1 - j]);
          break;
        }
      }
    }
    Assert(sub.size() == 2);
    foldConclusion = sub[0].eqNode(sub[1]);
  }
  else
  {
    // conclusion must be, modulo symmetry, false = true
    Assert(conclusion[0].getKind() == kind::CONST_BOOLEAN
           && conclusion[1].getKind() == kind::CONST_BOOLEAN);
    inSubstCase = false;
    foldConclusion = premises[offending][termPos];
  }
  std::vector<Node> foldPremises;
  for (unsigned i = 0; i < size; ++i)
  {
    if (i != offending)
    {
      foldPremises.push_back(premises[i]);
    }
  }
  cleanReflPremisesInTranstivity(foldPremises);
  Assert(!foldPremises.empty());
  Trace("eqproof-conv") << "EqProof::foldTransitivityChildren: need to derive "
                        << foldConclusion << " with premises " << foldPremises
                        << "\n";
  Assert(foldPremises.size() > 1 || foldConclusion == foldPremises.back()
         || (foldConclusion[0] == foldPremises.back()[1]
             && foldConclusion[1] == foldPremises.back()[0]))
      << "EqProof::foldTransitivityChildren: single fold premise "
      << foldPremises.back() << " is not the same as foldConclusion "
      << foldConclusion << " and not its symmetric\n";
  if (foldPremises.size() > 1)
  {
    // create transitivity step to derive expected premise
    unsigned newSize = foldPremises.size();
    maybeAddSymmOrTrueIntroToProof(0, foldPremises, true, foldConclusion[0], p);
    for (unsigned i = 1; i < newSize - 1; ++i)
    {
      maybeAddSymmOrTrueIntroToProof(
          i, foldPremises, true, foldPremises[i - 1][1], p);
    }
    maybeAddSymmOrTrueIntroToProof(
        newSize - 1, foldPremises, false, foldConclusion[1], p);
    // create folding step
    if (!p->addStep(foldConclusion, PfRule::TRANS, foldPremises, {}, true))
    {
      Assert(false) << "EqProof::foldTransitivityChildren: couldn't add "
                       "folding trans step from "
                    << foldPremises << " to " << foldConclusion << "\n";
    }
  }
  // now build the proof step for the original conclusion
  premises.clear();
  premises.push_back(premises[offending]);
  Trace("eqproof-conv")
      << "EqProof::foldTransitivityChildren: now derive conclusion "
      << conclusion << " via ";
  if (inSubstCase)
  {
    premises.push_back(foldConclusion);
    Trace("eqproof-conv") << PfRule::MACRO_SR_PRED_TRANSFORM << " from "
                          << premises << "\n";
    if (!p->addStep(conclusion,
                    PfRule::MACRO_SR_PRED_TRANSFORM,
                    premises,
                    {conclusion},
                    true))
    {
      Assert(false) << "EqProof::foldTransitivityChildren: couldn't add "
                       "final trans step\n";
    }
  }
  else
  {
    // create TRUE_INTRO step for foldConclusion
    Trace("eqproof-conv") << "EqProof::foldTransitivityChildren: adding "
                          << PfRule::TRUE_INTRO << " step for "
                          << foldConclusion[0] << "\n";
    Node newFoldConclusion =
        foldConclusion.eqNode(NodeManager::currentNM()->mkConst<bool>(true));
    if (!p->addStep(
            newFoldConclusion, PfRule::TRUE_INTRO, {foldConclusion}, {}))
    {
      Assert(false) << "EqProof::foldTransitivityChildren: couldn't add "
                    << PfRule::TRUE_INTRO << " rule\n";
    }
    premises.push_back(newFoldConclusion);
    Trace("eqproof-conv") << PfRule::MACRO_SR_PRED_TRANSFORM << " from "
                          << premises << "\n";
    unsigned newSize = premises.size();
    maybeAddSymmOrTrueIntroToProof(0, premises, true, conclusion[0], p);
    for (unsigned i = 1; i < newSize - 1; ++i)
    {
      maybeAddSymmOrTrueIntroToProof(i, premises, true, premises[i - 1][1], p);
    }
    maybeAddSymmOrTrueIntroToProof(
        newSize - 1, premises, false, conclusion[1], p);
    // create final transitivity step
    if (!p->addStep(conclusion, PfRule::TRANS, premises, {}, true))
    {
      Assert(false) << "EqProof::foldTransitivityChildren: couldn't add "
                       "final trans step\n";
    }
  }
  return true;
}

void EqProof::maybeAddSymmOrTrueIntroToProof(unsigned i,
                                             std::vector<Node>& premises,
                                             bool first,
                                             Node termInEq,
                                             CDProof* p) const
{
  // nothing to do
  if (premises[i][first ? 0 : 1] == termInEq)
  {
    return;
  }
  NodeManager* nm = NodeManager::currentNM();
  Trace("eqproof-conv") << "EqProof::maybeAddSymmOrTrueIntroToProof: seach for "
                        << termInEq << " as " << (first ? "fst" : "snd")
                        << " term starting in index " << i << " in " << premises
                        << "\n";
  // look for first premise with termInEq in it. If j != i, move that
  // premise to the position i of the list
  unsigned j, size = premises.size();
  bool correctlyOrdered = false;
  for (j = i; j < size; ++j)
  {
    bool occurs = false;
    if (termInEq == premises[j][first ? 0 : 1])
    {
      occurs = correctlyOrdered = true;
    }
    else if (termInEq == premises[j][first ? 1 : 0])
    {
      occurs = true;
    }
    if (occurs)
    {
      Trace("eqproof-conv")
          << "EqProof::maybeAddSymmOrTrueIntroToProof: found termInEq "
          << termInEq << " in premise " << j << "\n";
      if (j != i)
      {
        // move premise to position i.
        Node premise = premises[j];
        premises.erase(premises.begin() + j);
        premises.insert(premises.begin() + i, premise);
        Trace("eqproof-conv")
            << "EqProof::maybeAddSymmOrTrueIntroToProof: reordering premises: "
            << premises << "\n";
      }
      break;
    }
  }
  // did not find it. It must be the case that termInEq is a boolean
  // constant and a TRUE_INTRO step is applied
  if (j == size)
  {
    Assert(termInEq.getKind() == kind::CONST_BOOLEAN
           && termInEq.getConst<bool>())
        << "term " << termInEq
        << " is not True, so it should have been in a premise\n";
    // add TRUE_INTRO step for first premise
    Node conclusion = premises[i].eqNode(nm->mkConst<bool>(true));
    Trace("eqproof-conv") << "EqProof::maybeAddSymmOrTrueIntroToProof: adding "
                          << PfRule::TRUE_INTRO << " step for " << premises[i]
                          << "\n";
    if (!p->addStep(conclusion, PfRule::TRUE_INTRO, {premises[i]}, {}))
    {
      Assert(false) << "EqProof::maybeAddSymmOrTrueIntroToProof: couldn't add "
                    << PfRule::TRUE_INTRO << " rule\n";
    }
    premises[i] = conclusion;
    // not correctly ordered unless I'm looking for TRUE as the second argument
    correctlyOrdered = !first;
  }
  // reorder. Don't need to add symm step because it'll be added silently when
  // the reordered premise is used.
  if (!correctlyOrdered)
  {
    Node symmChild = premises[i][1].eqNode(premises[i][0]);
    premises[i] = symmChild;
  }
}

Node EqProof::addToProof(CDProof* p) const
{
  std::unordered_map<Node, Node, NodeHashFunction> cache;
  return addToProof(p, cache);
}

Node EqProof::addToProof(
    CDProof* p, std::unordered_map<Node, Node, NodeHashFunction>& visited) const
{
  std::unordered_map<Node, Node, NodeHashFunction>::const_iterator it =
      visited.find(d_node);
  if (it != visited.end())
  {
    Trace("eqproof-conv") << "EqProof::addToProof: already processed " << d_node
                          << ", returning " << it->second << "\n";
    return it->second;
  }
  // assumption
  if (d_id == MERGED_THROUGH_EQUALITY)
  {
    Trace("eqproof-conv") << "EqProof::addToProof: adding assumption step for "
                          << d_node << "\n";
#ifdef CVC4_ASSERTIONS
    // make sure there are no (= true/false true/false) assumptions
    if (d_node.getKind() != kind::EQUAL)
    {
      for (unsigned i = 0; i < 2; ++i)
      {
        Assert(d_node[i].getKind() != kind::CONST_BOOLEAN
               || d_node[1 - 1].getKind() != kind::CONST_BOOLEAN)
            << "EqProof::addToProof: fully boolean constant assumption is "
               "disallowed\n";
      }
    }
#endif
    if (d_node.getKind() == kind::EQUAL
        && ((d_node[0].getKind() == kind::CONST_BOOLEAN
             && d_node[1].getKind() != kind::CONST_BOOLEAN)
            || (d_node[1].getKind() == kind::CONST_BOOLEAN
                && d_node[0].getKind() != kind::CONST_BOOLEAN)))
    {
      unsigned constIndex = d_node[0].getKind() == kind::CONST_BOOLEAN ? 0 : 1;
      std::vector<Node> introChildren;
      PfRule introRule;
      if (d_node[constIndex].getConst<bool>())
      {
        introRule = PfRule::TRUE_INTRO;
        introChildren.push_back(d_node[1 - constIndex]);
      }
      else
      {
        introRule = PfRule::FALSE_INTRO;
        introChildren.push_back(d_node[1 - constIndex].notNode());
      }
      // the assumption can be e.g. (= false (= t1 t2)) in which case the
      // necessary proof to be built is
      //     --------------- ASSUME
      //     (not (= t1 t2))
      //  -------------------- FALSE_INTRO
      //  (= (= t1 t2) false)
      //  -------------------- SYMM
      //  (= false (= t1 t2))
      //
      // with the SYMM step happening automatically whenever the assumption is
      // used in the proof p
      Node introConclusion =
          constIndex == 1 ? d_node : d_node[1].eqNode(d_node[0]);
      if (!p->addStep(introConclusion, introRule, introChildren, {}))
      {
        Assert(false) << "EqProof::addToProof: couldn't add " << introRule
                      << " from " << d_node[1 - constIndex].notNode() << " to "
                      << introConclusion << "\n";
      }
    }
    if (!p->addStep(d_node, PfRule::ASSUME, {}, {d_node}))
    {
      Assert(false) << "EqProof::addToProof: couldn't add assumption\n";
    }
    // if non-equality predicate, turn into one via TRUE/FALSE intro
    Node conclusion = d_node;
    if (d_node.getKind() != kind::EQUAL)
    {
      PfRule intro;
      if (d_node.getKind() == kind::NOT)
      {
        conclusion =
            d_node[0].eqNode(NodeManager::currentNM()->mkConst<bool>(false));
        intro = PfRule::FALSE_INTRO;
      }
      else
      {
        intro = PfRule::TRUE_INTRO;
        conclusion =
            d_node.eqNode(NodeManager::currentNM()->mkConst<bool>(true));
      }
      Trace("eqproof-conv") << "EqProof::addToProof: adding " << intro
                            << " step for " << d_node << "\n";
      if (!p->addStep(conclusion, intro, {d_node}, {}))
      {
        Assert(false) << "EqProof::addToProof: couldn't add " << intro
                      << " rule from " << d_node << "\n";
      }
    }
    visited[d_node] = conclusion;
    return conclusion;
  }
  // refl
  if (d_id == MERGED_THROUGH_REFLEXIVITY)
  {
    Trace("eqproof-conv") << "EqProof::addToProof: adding refl step for "
                          << d_node << "\n";
    Assert(d_node.getKind() == kind::EQUAL);
    std::vector<Node> children;
    std::vector<Node> args{d_node[0]};
    if (!p->addStep(d_node, PfRule::REFL, children, args))
    {
      Assert(false) << "EqProof::addToProof: couldn't add refl step\n";
    }
    visited[d_node] = d_node;
    return d_node;
  }
  // can support case of negative merged throgh constants, but not positive one
  // yet
  if (d_id == MERGED_THROUGH_CONSTANTS)
  {
    Assert(false) << "Unsupported rule: " << d_id << "\n";
    visited[d_node] = d_node;
    return d_node;
  }
  if (d_id == MERGED_THROUGH_TRANS)
  {
    AlwaysAssert(d_node.getKind() == kind::EQUAL
                 || (d_node.getKind() == kind::NOT
                     && d_node[0].getKind() == kind::EQUAL))
        << "EqProof::addToProof: transitivity step conclusion " << d_node
        << " is not equality or negated equality\n";
    Trace("eqproof-conv") << "EqProof::addToProof: adding trans step for "
                          << d_node << "\n";
    std::vector<Node> children;
    for (unsigned i = 0, size = d_children.size(); i < size; ++i)
    {
      // if one of the steps is a fake congruence one, it must deleted. Its
      // premises are moved down to premises of the transitivity step
      EqProof* childProof = d_children[i].get();
      if (childProof->d_id == MERGED_THROUGH_CONGRUENCE
          && childProof->d_node.isNull())
      {
        CVC4_UNUSED bool addedChild = false;
        Trace("eqproof-conv") << "EqProof::addToProof: child proof " << i
                              << " is fake cong step. Fold it.\n";
        Assert(childProof->d_children.size() == 2);
        Trace("eqproof-conv")
            << push << "EqProof::addToProof: recurse on child 0\n"
            << push;
        Node child = childProof->d_children[0].get()->addToProof(p, visited);
        // ignore reflexivity
        if (child[0] != child[1])
        {
          children.push_back(child);
          addedChild = true;
        }
        Trace("eqproof-conv")
            << pop << "EqProof::addToProof: recurse on child 1\n"
            << push;
        child = childProof->d_children[1].get()->addToProof(p, visited);
        // ignore reflexivity
        // ignore reflexivity
        if (child[0] != child[1])
        {
          children.push_back(child);
          addedChild = true;
        }
        Trace("eqproof-conv") << pop << pop;
        Assert(addedChild);
        continue;
      }
      Trace("eqproof-conv")
          << "EqProof::addToProof: recurse on child " << i << "\n"
          << push;
      children.push_back(childProof->addToProof(p, visited));
      Trace("eqproof-conv") << pop;
    }
    // if conclusion is (not (= t1 t2)) change it to (= (= t1 t2) false) so that
    // the reasoning below is uniform. After the transitivity proof is processed
    // the conclusion will be turned again into (not (= t1 t2)) via FALSE_ELIM
    Node conclusion =
        d_node.getKind() != kind::NOT
            ? d_node
            : d_node[0].eqNode(NodeManager::currentNM()->mkConst<bool>(false));
    // if premises contain one equality between false and an equality then maybe
    // it'll be necessary to fix the transitivity premises before reaching the
    // original conclusion. For example
    //
    //  (= t1 t2) (= t3 t2) (= (t1 t3) false)
    //  ------------------------------------- TRANS
    //             false = true
    //
    // must, before the processing below, become
    //
    //            (= t3 t2)
    //            --------- SYMM
    //  (= t1 t2) (= t2 t3)
    //  ------------------- TRANS
    //       (= t1 t3)             (= (t1 t3) false)
    //  --------------------------------------------- TRANS
    //             false = true
    //
    // If the conclusion is, modulo symmetry, (= (= t1 t2) false), then the
    // above construction may fail. Consider
    //
    //  (= t3 t4) (= t3 t2) (= (t1 t2) false)
    //  ------------------------------------- TRANS
    //             (= (= t4 t1) false)
    //
    //  whose premises other than (= (t1 t2) false) do not allow the derivation
    //  of (= (= t1 t2) (= t4 t1)). The original conclusion however can be
    //  derived with
    //                          (= t2 t3) (= t3 t4)
    //                          ------------------- TRANS
    //  (= (t1 t2) false)           (= t2 t4)
    //  ------------------------------------------- MACRO_SR_PRED_TRANSFORM
    //             (= (= t4 t1) false)
    //
    // where note that the conclusion is equal to the left premise with the
    // right premise as a substitution applied to it, modulo rewriting (which
    // accounts for the different order of the equality with false).
    //
    // If in either of the above cases then the conclusion is directly derived
    // in the call, so only in the other cases we try to build a transitivity
    // step below
    bool folded = foldTransitivityChildren(conclusion, children, p);
    Assert(!folded || p->hasStep(conclusion));
    if (!folded)
    {
      cleanReflPremisesInTranstivity(children);
      Trace("eqproof-conv")
          << "EqProof::addToProof: maybe reorder trans premises " << children
          << " to conclude " << conclusion << "\n";
      // conclusion is t1 = tn. Children MUST BE (= t1 t2), ..., (= t{n-1} tn).
      // If t1 or tn are true or false, then premises may have to be amended
      // with TRUE/FALSE intro rules. Process children to ensure this
      unsigned size = children.size();
      maybeAddSymmOrTrueIntroToProof(0, children, true, conclusion[0], p);
      for (unsigned i = 1; i < size - 1; ++i)
      {
        Assert(children[i - 1].getKind() == kind::EQUAL);
        maybeAddSymmOrTrueIntroToProof(
            i, children, true, children[i - 1][1], p);
      }
      maybeAddSymmOrTrueIntroToProof(
          size - 1, children, false, conclusion[1], p);
      // add step while making sure that all children have been added to the
      // proof, as well as that the proof should be rewritten in case it exists.
      // Overwritting is necessary because of a literal potentially having
      // different explanations at different points of the solving.
      if (!p->addStep(conclusion, PfRule::TRANS, children, {}, true, true))
      {
        Assert(false) << "EqProof::addToProof: couldn't add TRANS "
                      << conclusion << " " << children << "\n";
      }
    }
    // If t1 = tn is of the form (= t true/false), in which t is not true/false,
    // it must be turned into t or (not t) with TRUE/FALSE_ELIM.
    Assert(conclusion.getKind() == kind::EQUAL);
    if ((conclusion[0].getKind() == kind::CONST_BOOLEAN
         && conclusion[1].getKind() != kind::CONST_BOOLEAN)
        || (conclusion[1].getKind() == kind::CONST_BOOLEAN
            && conclusion[0].getKind() != kind::CONST_BOOLEAN))
    {
      std::vector<Node> elimChildren{conclusion};
      unsigned constIndex =
          conclusion[0].getKind() == kind::CONST_BOOLEAN ? 0 : 1;
      PfRule elimRule;
      if (conclusion[constIndex].getConst<bool>())
      {
        elimRule = PfRule::TRUE_ELIM;
        conclusion = conclusion[1 - constIndex];
      }
      else
      {
        elimRule = PfRule::FALSE_ELIM;
        conclusion = conclusion[1 - constIndex].notNode();
      }
      Trace("eqproof-conv") << "EqProof::addToProof: adding " << elimRule
                            << " step for " << elimChildren.back() << "\n";
      if (!p->addStep(conclusion, elimRule, elimChildren, {}))
      {
        Assert(false) << "EqProof::addToProof: couldn't add " << elimRule
                      << " rule\n";
      }
    }
    visited[d_node] = conclusion;
    return conclusion;
  }
  Assert(d_id == MERGED_THROUGH_CONGRUENCE);
  Trace("eqproof-conv") << "EqProof::addToProof: adding cong step for "
                        << d_node << "\n";
  // congruence steps must be flattened (since it assumes currying) and the
  // conclusion must be reconstructed (since only one of the terms is
  // represented)
  Assert(d_node.getKind() == kind::EQUAL)
      << "EqProof::addToProof: conclusion " << d_node << " is not equality\n";
  // The given conclusion is taken as ground truth. If the premises do not
  // align, for example with (= (f t1) (f t2)) but a premise being t2 = t1, we
  // reorder it via a symmetry step
  Assert(d_node[0].getNumChildren() == d_node[1].getNumChildren())
      << "EqProof::addToProof: apps in conclusion " << d_node
      << " have different arity\n";
  // premises to be retrieved
  std::vector<Node> children;
  const EqProof* childProof = this;
  unsigned arity = d_node[0].getNumChildren();
  // iterate over children proofs. first child proof is always bogus
  for (unsigned i = 0; i < arity; ++i)
  {
    Assert(childProof->d_children.size() == 2);
    Trace("eqproof-conv") << "EqProof::addToProof: recurse on second child of "
                          << i << "-th cong\n"
                          << push;
    Node childConclusion =
        childProof->d_children[1].get()->addToProof(p, visited);
    Assert(childConclusion.getKind() == kind::EQUAL);
    if (childConclusion[0] != d_node[0][arity - 1 - i])
    {
      Assert(childConclusion[0] == d_node[1][arity - 1 - i]);
      // reorder. Don't need to add symm step because it'll be added silently
      // when the reordered premise is used.
      childConclusion = childConclusion[1].eqNode(childConclusion[0]);
    }
    children.insert(children.begin(), childConclusion);
    Trace("eqproof-conv") << pop;
    if (i < arity - 1)
    {
      // lhs proof should be a congruence step
      Assert(!childProof->d_children.empty());
      childProof = childProof->d_children[0].get();
      // if the left step is a fake transitivity one, which is standing in for
      // the actual congruence step being produced. In the simplest case the
      // premises are repetitions of the congruence step it should have been
      // considered. An example of a valid EqProof currently:
      //
      //  -- R  --R        -- R   --R
      //   f    t1          f     t1
      //  --------- CONG   --------- CONG
      //    f t1             f t1
      // ----------------------------- TRANS
      //       (= (f t1 t2) (f t1 t3))          (= t2 t3)
      //  ------------------------------------------------ CONG
      //             f t1 t2
      //
      // However this can be arbitraliry complicated, therefore it is necessary
      // to recursively process the transitivity proof according to the
      // following methodology:
      //
      // When a transitivity step is found in the first child of internal cong,
      // it'll have an equality as a conclusion. That equality is not the
      // conclusion of the (post-processed) transtivitiy step. That will be the
      // equality between the first child of each application (in a
      // curried view):
      //
      //     (= (f t1 t2) (f t3 t4)) is actually to be post processed into
      //     goal: (= (f t1) (f t3))
      //
      // For each child proof of the transitivity step, ignore its conclusion,
      // then process RHS. (If this the LHS is not (= f f), it's also necessary
      // to recursively process it). If the processing of the RHS is not a proof
      // of (= t1 t3), save it for a premise of the transitivity proof. Do this
      // for all subproofs.
      //
      if (childProof->d_id != MERGED_THROUGH_CONGRUENCE)
      {
#ifdef CVC4_ASSERTIONS
        Debug("eqproof::conv")
            << "EqProof::addToProof: Non-conforming first child of internal "
               "congruence step:\n";
        childProof->debug_print("eqproof::conv");
        Debug("eqproof::conv") << "\n";
        Assert(childProof->d_id == MERGED_THROUGH_TRANS);
        Assert(i == arity - 2)
            << "EqProof::addToProof: Can't process 'fake transitivity' steps "
               "that with non-trivial LHS\n";
        Assert(childProof->d_node.getKind() == kind::EQUAL);
        Assert(childProof->d_children.size() >= 2);
#endif
        Node neededConclusion =
            childProof->d_node[0][0].eqNode(childProof->d_node[1][0]);
        Trace("eqproof-conv") << "EqProof::addToProof: First child is "
                                 "transitivity. Turn into cong concluding "
                              << neededConclusion << ". Processing children:\n";
        bool foundConclusion = false;
        // bool foundConclusionNeedSym = false;
        std::vector<Node> transitivityPremises;
        for (unsigned j = 0, sizeTrans = childProof->d_children.size();
             j < sizeTrans;
             ++j)
        {
          Assert(childProof->d_children[j].get()->d_id
                 == MERGED_THROUGH_CONGRUENCE);
          Assert(childProof->d_children[j].get()->d_children[0].get()->d_id
                 == MERGED_THROUGH_REFLEXIVITY);
          Trace("eqproof-conv")
              << "EqProof::addToProof: recurse on second child of " << j
              << "-th cong premise\n"
              << push;
          transitivityPremises.push_back(
              childProof->d_children[j].get()->d_children[1].get()->addToProof(
                  p, visited));
          Trace("eqproof-conv") << pop;
          if (transitivityPremises.back() == neededConclusion)
          {
            Trace("eqproof-conv")
                << "EqProof::addToProof: found required conclusion\n";
            foundConclusion = true;
            break;
          }
          // TODO do I need this and use the flag to generate a sym step below?
          // else if (transitivityPremises.back()[0] == neededConclusion[1]
          //          && transitivityPremises.back()[1] == neededConclusion[0])
          // {
          //   foundConclusion = true;
          //   foundConclusionNeedSym = true;
          //   break;
          // }
        }
        // build transtivity step with premises if did not straight found the
        // needed conclusion. Since those might not be properly ordered, process
        // it as the transitivity premises
        //
        // TODO: do a method for this processing. It's happenning here, in the
        // regular TRANS case and in the transitivity folding
        if (!foundConclusion)
        {
          cleanReflPremisesInTranstivity(transitivityPremises);
          // be sure to recompute this since the above method may change the
          // size
          unsigned sizeTrans = transitivityPremises.size();
          maybeAddSymmOrTrueIntroToProof(
              0, transitivityPremises, true, neededConclusion[0], p);
          for (unsigned j = 1; j < sizeTrans - 1; ++j)
          {
            Assert(transitivityPremises[j - 1].getKind() == kind::EQUAL);
            maybeAddSymmOrTrueIntroToProof(j,
                                           transitivityPremises,
                                           true,
                                           transitivityPremises[j - 1][1],
                                           p);
          }
          maybeAddSymmOrTrueIntroToProof(sizeTrans - 1,
                                         transitivityPremises,
                                         false,
                                         neededConclusion[1],
                                         p);
          if (!p->addStep(neededConclusion,
                          PfRule::TRANS,
                          transitivityPremises,
                          {},
                          true,
                          true))
          {
            Assert(false) << "EqProof::addToProof: couldn't add trans step\n";
          }
        }
        children.insert(children.begin(), neededConclusion);
        break;
      }
    }
    else
    {
      // case of f = f
      Assert(childProof->d_children[0].get()->d_id
             == MERGED_THROUGH_REFLEXIVITY);
    }
  }
  // build args
  std::vector<Node> args;
  Kind k = d_node[0].getKind();
  if (kind::metaKindOf(k) == kind::metakind::PARAMETERIZED)
  {
    args.push_back(d_node[0].getOperator());
  }
  else
  {
    args.push_back(NodeManager::currentNM()->operatorOf(k));
  }
  // build conclusion
  Trace("eqproof-conv") << "EqProof::addToProof: build cong step of " << d_node
                        << " with op " << args[0] << " and children "
                        << children << "\n";
  if (!p->addStep(d_node, PfRule::CONG, children, args, true, true))
  {
    Assert(false) << "EqProof::addToProof: couldn't add cong step\n";
  }
  if (Trace.isOn("eqproof-conv"))
  {
    Trace("eqproof-conv") << "EqProof::addToProof: proof node of " << d_node
                          << " is:\n";
    std::stringstream out;
    p->mkProof(d_node).get()->printDebug(out);
    Trace("eqproof-conv") << out.str() << "\n";
  }
  visited[d_node] = d_node;
  return d_node;
}

}  // namespace eq
}  // Namespace theory
}  // Namespace CVC4
