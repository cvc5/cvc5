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

#include "expr/proof.h"

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
    Trace("eqproof-conv")
        << "EqProof::cleanReflPremisesInTranstivity: new premises " << premises
        << "\n";
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

void EqProof::reduceNestedCongruence(
    unsigned i,
    Node conclusion,
    std::vector<std::vector<Node>>& children,
    CDProof* p,
    std::unordered_map<Node, Node, NodeHashFunction>& visited) const
{
  Trace("eqproof-conv") << "EqProof::reduceNestedCongruence: building for " << i
                        << "-th arg\n";
  if (d_id == MERGED_THROUGH_CONGRUENCE)
  {
    Assert(d_children.size() == 2);
    Trace("eqproof-conv") << "EqProof::reduceNestedCongruence: it's a "
                             "congruence step. Reduce second child\n"
                          << push;
    children[i].push_back(d_children[1].get()->addToProof(p, visited));
    Trace("eqproof-conv")
        << pop << "EqProof::reduceNestedCongruence: child conclusion "
        << children[i].back() << "\n";
    // recurse
    if (i > 0)
    {
      Trace("eqproof-conv")
          << "EqProof::reduceNestedCongruence: Reduce first child\n"
          << push;
      d_children[0].get()->reduceNestedCongruence(
          i - 1, conclusion, children, p, visited);
      Trace("eqproof-conv") << pop;
    }
    else
    {
      // case of f = f
      Assert(d_children[0].get()->d_id == MERGED_THROUGH_REFLEXIVITY);
    }
    return;
  }
  Assert(d_id == MERGED_THROUGH_TRANS);
  // TODO update this doc
  //
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
  Trace("eqproof-conv") << "EqProof::reduceNestedCongruence: it's a "
                           "transitivity step.\n";
  for (unsigned j = 0, sizeTrans = d_children.size(); j < sizeTrans; ++j)
  {
    Assert(d_children[j].get()->d_id == MERGED_THROUGH_CONGRUENCE);
    Trace("eqproof-conv") << "EqProof::reduceNestedCongruence: Reduce " << j
                          << "-th transitivity child\n"
                          << push;
    d_children[j].get()->reduceNestedCongruence(
        i, conclusion, children, p, visited);
    Trace("eqproof-conv") << pop;
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
  Trace("eqproof-conv") << "EqProof::addToProof: adding step for "
                        << static_cast<MergeReasonType>(d_id)
                        << " with conclusion " << d_node << "\n";
  // assumption
  if (d_id == MERGED_THROUGH_EQUALITY)
  {
#ifdef CVC4_ASSERTIONS
    // make sure there are no (= true/false true/false) assumptions
    if (d_node.getKind() == kind::EQUAL)
    {
      for (unsigned i = 0; i < 2; ++i)
      {
        Assert(d_node[i].getKind() != kind::CONST_BOOLEAN
               || d_node[1 - i].getKind() != kind::CONST_BOOLEAN)
            << "EqProof::addToProof: fully boolean constant assumption "
            << d_node << " is disallowed\n";
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
    Assert(!d_node.isNull() && d_node.getKind() == kind::EQUAL
           && d_node[0].getKind() == kind::EQUAL
           && d_node[1].getKind() == kind::CONST_BOOLEAN
           && !d_node[1].getConst<bool>())
        << "EqProof::addToProof: Unsupported case of "
        << static_cast<MergeReasonType>(d_id) << ". Conclusion " << d_node
        << " was expected to be (= (= t1 t2) false)\n";
    Assert(d_children.size() == 2)
        << "EqProof::addToProof: wrong number of assumptions for "
           "MACRO_SR_PRED_INTRO concluding "
        << d_node << "\n";
    // Build
    //
    // (= t1 c1)  (= t2 c2)
    // -------------------- MACRO_SR_PRED_INTRO
    //  ((= t1 t2) false)
    // ------------------ FALSE_ELIM
    //  (not (= t1 t2))
    //
    // First process the children proofs
    std::vector<Node> premises;
    for (unsigned i = 0; i < 2; ++i)
    {
      Trace("eqproof-conv")
          << "EqProof::addToProof: recurse on child " << i << "\n"
          << push;
      premises.push_back(d_children[i].get()->addToProof(p, visited));
      Trace("eqproof-conv") << pop;
    }
    // Now get the constants in the premises
    std::vector<Node> constants(2);
    for (unsigned i = 0; i < 2; ++i)
    {
      Node term = d_node[0][i];
      // look in children
      for (unsigned j = 0; j < 2; ++j)
      {
        Assert(premises[j].getKind() == kind::EQUAL);
        if (premises[j][0] == term)
        {
          Assert(premises[j][1].isConst());
          constants[i] = premises[j][1];
        }
        else if (premises[j][1] == term)
        {
          Assert(premises[j][0].isConst());
          constants[i] = premises[j][0];
        }
      }
    }
    Assert(!constants[0].isNull() && !constants[1].isNull())
        << "EqProof::addToProof: premises w/o all constants from conclusion "
        << d_node << "\n";
    // build rule premises in right order
    std::vector<Node> children;
    children.push_back(d_node[0][0].eqNode(constants[0]));
    children.push_back(d_node[0][1].eqNode(constants[1]));
    Trace("eqproof-conv") << "EqProof::addToProof: adding "
                          << PfRule::MACRO_SR_PRED_INTRO << " step from "
                          << children << "\n";
    if (!p->addStep(d_node, PfRule::MACRO_SR_PRED_INTRO, children, {d_node}))
    {
      Assert(false) << "EqProof::addToProof: couldn't add "
                    << PfRule::MACRO_SR_PRED_INTRO << " rule\n";
    }
    Node conclusion = d_node[0].notNode();
    Trace("eqproof-conv") << "EqProof::addToProof: adding "
                          << PfRule::FALSE_ELIM << " step from " << d_node
                          << "\n";
    if (!p->addStep(conclusion, PfRule::FALSE_ELIM, {d_node}, {}))
    {
      Assert(false) << "EqProof::addToProof: couldn't add "
                    << PfRule::FALSE_ELIM << " rule\n";
    }
    visited[d_node] = conclusion;
    return conclusion;
  }
  if (d_id == MERGED_THROUGH_TRANS)
  {
    AlwaysAssert(d_node.getKind() == kind::EQUAL
                 || (d_node.getKind() == kind::NOT
                     && d_node[0].getKind() == kind::EQUAL))
        << "EqProof::addToProof: transitivity step conclusion " << d_node
        << " is not equality or negated equality\n";
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
        Trace("eqproof-conv") << push;
        for (unsigned j = 0, sizeJ = childProof->d_children.size(); j < sizeJ;
             ++j)
        {
          Trace("eqproof-conv")
              << "EqProof::addToProof: recurse on child " << j << "\n"
              << push;
          Node child = childProof->d_children[j].get()->addToProof(p, visited);
          // ignore reflexivity
          if (child[0] != child[1])
          {
            children.push_back(child);
            addedChild = true;
          }
          Trace("eqproof-conv") << pop;
        }
        Trace("eqproof-conv") << pop;
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
  std::vector<std::vector<Node>> transtivityChildren;
  unsigned arity = d_node[0].getNumChildren();
  // intialize children matrix
  for (unsigned i = 0; i < arity; ++i)
  {
    transtivityChildren.push_back(std::vector<Node>());
  }
  reduceNestedCongruence(arity - 1, d_node, transtivityChildren, p, visited);
  if (Trace.isOn("eqproof-conv"))
    {
    Trace("eqproof-conv")
        << "EqProof::addToProof: premises from reduced cong:\n";
    for (unsigned i = 0; i < arity; ++i)
    {
      Trace("eqproof-conv") << "EqProof::addToProof:\t" << i
                            << "-th arg:" << transtivityChildren[i] << "\n";
    }
  }
  // bulid transitivity steps for the arguments with transitivity proofs
  std::vector<Node> children(arity);
  for (unsigned i = 0; i < arity; ++i)
    {
    Assert(!transtivityChildren[i].empty())
        << "EqProof::addToProof: did not add any justification for " << i
        << "-th arg of congruence " << d_node << "\n";
    // nothing to do
    if (transtivityChildren[i].size() == 1)
      {
      children[i] = transtivityChildren[i][0];
      continue;
    }
    cleanReflPremisesInTranstivity(transtivityChildren[i]);
    // if after refl elimination it has only one child, take that
    if (transtivityChildren[i].size() == 1)
        {
      children[i] = transtivityChildren[i][0];
      continue;
    }
    Node transConclusion = d_node[0][i].eqNode(d_node[1][i]);
    // if conclusion, or its symmetric, occurs in the premises, nothing to do
    bool occurs = false;
    unsigned sizeTrans = transtivityChildren[i].size();
    for (unsigned j = 0; j < sizeTrans; ++j)
          {
      if (transtivityChildren[i][j] == transConclusion
          || (transtivityChildren[i][j][0] == transConclusion[1]
              && transtivityChildren[i][j][1] == transConclusion[0]))
      {
        occurs = true;
            break;
          }
    }
    if (!occurs && sizeTrans > 0)
    {
      // Build transitivity step. Since premises might not be properly ordered,
      // process it as the transitivity premises
          maybeAddSymmOrTrueIntroToProof(
          0, transtivityChildren[i], true, transConclusion[0], p);
          for (unsigned j = 1; j < sizeTrans - 1; ++j)
          {
        Assert(transtivityChildren[i][j - 1].getKind() == kind::EQUAL);
            maybeAddSymmOrTrueIntroToProof(j,
                                       transtivityChildren[i],
                                           true,
                                       transtivityChildren[i][j - 1][1],
                                           p);
          }
      maybeAddSymmOrTrueIntroToProof(
          sizeTrans - 1, transtivityChildren[i], false, transConclusion[1], p);
      Trace("eqproof-conv")
          << "EqProof::addToProof: adding trans step for cong premise "
          << transConclusion << " with children " << transtivityChildren[i]
          << "\n";
      if (!p->addStep(transConclusion,
                          PfRule::TRANS,
                      transtivityChildren[i],
                          {},
                          true,
                          true))
          {
            Assert(false) << "EqProof::addToProof: couldn't add trans step\n";
          }
        }
    children[i] = transConclusion;
    }
  Trace("eqproof-conv")
      << "EqProof::addToProof: premises after adding trans steps:" << children
      << "\n";
  // reorder children potentially
  for (unsigned i = 0; i < arity; ++i)
    {
    if (children[i][0] != d_node[0][i])
    {
      Assert(children[i][0] == d_node[1][i])
          << "EqProof::reduceNestedCongruence: child conclusion " << children[i]
          << " disconnectod from expected conclusion (" << d_node[0][i] << ", "
          << d_node[1][i] << "\n";
      // reorder. Don't need to add symm step because it'll be added silently
      // when the reordered premise is used.
      children[i] = children[i][1].eqNode(children[i][0]);
    }
  }
  Trace("eqproof-conv") << "EqProof::addToProof: premises after reordering:"
                        << children << "\n";
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
    p->getProof(d_node).get()->printDebug(out);
    Trace("eqproof-conv") << out.str() << "\n";
  }
  visited[d_node] = d_node;
  return d_node;
}

}  // namespace eq
}  // Namespace theory
}  // Namespace CVC4
