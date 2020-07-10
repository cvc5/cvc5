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
                          << (newPremises.size() >= size
                                  ? newPremises.size() - size
                                  : 0)
                          << " refl premises from " << premises << "\n";
    premises.clear();
    premises.insert(premises.begin(), newPremises.begin(), newPremises.end());
    Trace("eqproof-conv")
        << "EqProof::cleanReflPremisesInTranstivity: new premises " << premises
        << "\n";
  }
}

bool EqProof::foldTransitivityChildren(
    Node conclusion,
    std::vector<Node>& premises,
    CDProof* p,
    std::unordered_set<Node, NodeHashFunction>& assumptions) const
{
  Trace("eqproof-conv") << "EqProof::foldTransitivityChildren: check if need "
                           "to fold transitivity to conclude "
                        << conclusion << " from premises " << premises << "\n";
  // traverse premises to see if any of the form (= (= t1 t2) false)
  unsigned size = premises.size();
  unsigned termPos = 2, offending = size;
  for (unsigned i = 0; i < size; ++i)
  {
    AlwaysAssert(premises[i].getKind() == kind::EQUAL);
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
  NodeManager* nm = NodeManager::currentNM();
  Assert(termPos == 0 || termPos == 1);
  Trace("eqproof-conv") << "EqProof::foldTransitivityChildren: found "
                           "offending equality at index "
                        << offending << " : " << premises[offending] << "\n";
  // we name the premise to be added later for the original conclusion. It might
  // be reordered below if we are in the subst case below
  Node premise = premises[offending];
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
  // an offending premise (= (= t1 t2) false) indicates we are concluding,
  // modulo symmetry, (= false true) or the disequality (= (t3 t4) false). The
  // former can be fixed by having the remaining premises derive, with
  // TRANSITIVITY, (= t1 t2), but the latter requires building a subistuttion so
  // that (= (= t1 t2) false) becomes (= (= t3 t4) false). The premises will
  // constitute two independent transitivity proofs of (= t1 t3) and (= t2 t4).
  Node foldConclusion;
  std::vector<Node> substPremises;
  bool inSubstCase = false, substConclusionInReverseOrder = false;
  if ((conclusion[0].getKind() == kind::CONST_BOOLEAN
       && conclusion[1].getKind() != kind::CONST_BOOLEAN)
      || (conclusion[1].getKind() == kind::CONST_BOOLEAN
          && conclusion[0].getKind() != kind::CONST_BOOLEAN))
  {
    // A variation of
    //
    //  (= (= t1 t2) false) (= t1 x1) ... (= xn t3) (= t2 y1) ... (= ym t4)
    // ------------------------------------------------------------------ TR
    //         (= (= t4 t3) false)
    //
    // leads to:
    //
    //   (= t1 x1) ... (= xn t3)      (= t2 y1) ... (= ym t4)
    //  ------------------------ TR  ------------------------ TR
    //   (= t1 t3)                    (= t2 t4)
    //  ----------- SYMM             ----------- SYMM
    //   (= t3 t1)                    (= t4 t2)
    //  ---------------------------------------- CONG
    //   (= (= t3 t4) (= t1 t2))                         (= (= t1 t2) false)
    //  --------------------------------------------------------------------- TR
    //           (= (= t3 t4) false)
    //          --------------------- MACRO_SR_PRED_TRANSFORM
    //           (= (= t4 t3) false)
    //
    // Note that the last step is only necessary if the conclusion has the
    // arguments in reverse order than expected. Moreover, the symm steps are
    // done implicitly.
    //
    // Due to the two transitivity proofs happenning in the same set of
    // premises, we build the transitivity proofs for both children by greedly
    // searching for the sets of premises that allow concluding the
    // substitutions.
    inSubstCase = true;
    // reorder premise and conclusion if constant is the first argument
    premise = termPos == 0 ? premise : premise[1].eqNode(premise[0]);
    conclusion = conclusion[1].getKind() == kind::CONST_BOOLEAN
                     ? conclusion
                     : conclusion[1].eqNode(conclusion[0]);
    Node premiseTermEq = premise[0];
    Node conclusionTermEq = conclusion[0];
    Trace("eqproof-conv") << "EqProof::foldTransitivityChildren: Substitition "
                             "case. Need to build subst from "
                          << premiseTermEq << " to " << conclusionTermEq
                          << "\n";
    // If only one argument in the premise is substituted, premiseTermEq and
    // conclusionTermEq will share one argument and how the other change
    // characterizes the substitution. If no substitution can be substituted in
    // this way, then both arguments are replaced.
    std::vector<Node> subs[2];
    subs[0].push_back(premiseTermEq[0]);
    subs[1].push_back(premiseTermEq[1]);
    int equalArg = -1;
    for (unsigned i = 0; i < 2; ++i)
    {
      for (unsigned j = 0; j < 2; ++j)
      {
        if (premiseTermEq[i] == conclusionTermEq[j])
        {
          equalArg = i;
          subs[i].push_back(conclusionTermEq[j]);
          subs[1 - i].push_back(conclusionTermEq[1 - j]);
          substConclusionInReverseOrder = i != j;
          break;
        }
      }
    }
    if (equalArg >= 0)
    {
      foldConclusion = subs[1 - equalArg][0].eqNode(subs[1 - equalArg][1]);
      Trace("eqproof-conv")
          << "EqProof::foldTransitivityChildren: Need to fold premises into "
          << foldConclusion << "\n";
      // add refl step for other substitution, just in case
      p->addStep(subs[equalArg][0].eqNode(subs[equalArg][1]),
                 PfRule::REFL,
                 {},
                 {subs[equalArg][0]});
    }
    else
    {
      Trace("eqproof-conv") << "EqProof::foldTransitivityChildren: Need two "
                               "substitutions, so no fold can happen\n";
      // The substitutions t1 -> t3/t4 and t2 -> t3/t4 are built based on the
      // available premises. We must guarantee that the subsitution equality is
      // a premise or its symmetric
      Trace("eqproof-conv") << "EqProof::foldTransitivityChildren: Look for "
                            << premiseTermEq[0] << " and " << premiseTermEq[1]
                            << " in premises " << foldPremises << "\n";
      Assert(foldPremises.size() >= 2)
          << "Less than 2 fold premises for substituting BOTH terms in "
             "disequality.\nDisequality: "
          << premise << "\nFold premises: " << foldPremises
          << "\nConclusion: " << conclusion << "\n";
      // easy case where we can determine the substitution by directly looking
      // at the premises
      if (foldPremises.size() == 2)
      {
        // iterate over args to be substituted
        for (unsigned i = 0; i < 2; ++i)
        {
          // iterate over premises
          for (unsigned j = 0; j < 2; ++j)
          {
            // iterate over args in premise
            for (unsigned k = 0; k < 2; ++k)
            {
              if (premiseTermEq[i] == foldPremises[j][k])
              {
                subs[i].push_back(foldPremises[j][1 - k]);
                break;
              }
            }
          }
          Assert(subs[i].size() == 2)
              << " did not find term " << subs[i][0] << "\n";
          // check if argument to be substituted is in the same order in the
          // conclusion
          substConclusionInReverseOrder =
              premiseTermEq[i] != conclusionTermEq[i];
        }
      }
      else
      {
        Trace("eqproof-conv")
            << "EqProof::foldTransitivityChildren: Build transitivity chains "
               "for two subs among more than 2 premises: "
            << foldPremises << "\n";
        // hard case. Try first with t1 = t3 and see if can build it. If it can,
        // go on and build t2 = t4. Otherwise go on and build t1 = t4, t2 = t3.
        subs[0].push_back(conclusionTermEq[0]);
        subs[1].push_back(conclusionTermEq[1]);
        for (unsigned i = 0; i < 2; ++i)
        {
          // copy premises, since buildTransitivityChain is destructive
          std::vector<Node> copy1foldPremises(foldPremises.begin(),
                                              foldPremises.end());
          Node transConclusion1 = subs[0][0].eqNode(subs[0][1]);
          if (!buildTransitivityChain(transConclusion1, copy1foldPremises))
          {
            AlwaysAssert(i == 0)
                << "Couldn't find sub at all for substituting BOTH terms in "
                   "disequality.\nDisequality: "
                << premise << "\nFold premises: " << foldPremises
                << "\nConclusion: " << conclusion << "\n";
            // Failed. So flip sub and try again
            subs[0][1] = conclusionTermEq[1];
            subs[1][1] = conclusionTermEq[0];
            substConclusionInReverseOrder = false;
            continue;
          }
          // build next chain
          std::vector<Node> copy2foldPremises(foldPremises.begin(),
                                              foldPremises.end());
          Node transConclusion2 = subs[1][0].eqNode(subs[1][1]);
          if (!buildTransitivityChain(transConclusion2, copy2foldPremises))
          {
            AlwaysAssert(false)
                << "Found sub " << transConclusion1 << " but not other sub "
                << transConclusion2 << ".\nDisequality: " << premise
                << "\nFold premises: " << foldPremises
                << "\nConclusion: " << conclusion << "\n";
          }
          Trace("eqproof-conv")
              << "EqProof::foldTransitivityChildren: Built trans chains: "
                 "for two subs among more than 2 premises:\n";
          Trace("eqproof-conv")
              << "EqProof::foldTransitivityChildren: " << transConclusion1
              << " <- " << copy1foldPremises << "\n";
          Trace("eqproof-conv")
              << "EqProof::foldTransitivityChildren: " << transConclusion2
              << " <- " << copy2foldPremises << "\n";
          // do transitivity steps if need be
          if (copy1foldPremises.size() > 1
              && !assumptions.count(transConclusion1))
          {
            p->addStep(
                transConclusion1, PfRule::TRANS, copy1foldPremises, {}, true);
          }
          if (copy2foldPremises.size() > 1
              && !assumptions.count(transConclusion2))
          {
            p->addStep(
                transConclusion2, PfRule::TRANS, copy2foldPremises, {}, true);
          }
        }
      }
    }
    Trace("eqproof-conv")
        << "EqProof::foldTransitivityChildren: Built substutitions " << subs[0]
        << " and " << subs[1] << " to map " << premiseTermEq << " -> "
        << conclusionTermEq << "\n";
    Assert(subs[0][1] == conclusion[0][0] || subs[0][1] == conclusion[0][1])
        << "EqProof::foldTransitivityChildren: First substitution " << subs[0]
        << " doest not map to conclusion " << conclusion << "\n";
    Assert(subs[1][1] == conclusion[0][0] || subs[1][1] == conclusion[0][1])
        << "EqProof::foldTransitivityChildren: Second substitution " << subs[1]
        << " doest not map to conclusion " << conclusion << "\n";
    // in the premises the substitution is stored reversed due to the
    // substitution proof being built via transitivity between the new
    // equality term equal to the old one and that to false, so the new one is
    // equal to false
    substPremises.push_back(subs[0][1].eqNode(subs[0][0]));
    substPremises.push_back(subs[1][1].eqNode(subs[1][0]));
  }
  else
  {
    // conclusion must be, modulo symmetry, false = true
    Assert(conclusion[0].getKind() == kind::CONST_BOOLEAN
           && conclusion[1].getKind() == kind::CONST_BOOLEAN);
    foldConclusion = premise[termPos];
  }
  // potentially need to fold non-offending premises into a transitivity step
  if (!foldConclusion.isNull())
  {
    Trace("eqproof-conv")
        << "EqProof::foldTransitivityChildren: need to derive "
        << foldConclusion << " with premises " << foldPremises << "\n";
    Assert(foldPremises.size() > 1 || foldConclusion == foldPremises.back()
           || (foldConclusion[0] == foldPremises.back()[1]
               && foldConclusion[1] == foldPremises.back()[0]))
        << "EqProof::foldTransitivityChildren: single fold premise "
        << foldPremises.back() << " is not the same as foldConclusion "
        << foldConclusion << " and not its symmetric\n";
    // if the fold conclusion is an assumption, we'd be generating a cyclic
    // proof below, so no need
    //
    //                -------- A  ------- A
    //                 l1 = ""     "" = t
    // ------- A     ----------------------- TR
    // l1 = ""              l1 = t
    // ------------------------------------- TR
    //            "" = t
    // ------------------------------------- TRUE_I
    //        ("" = t) = True                            ("" = t) = False
    // -------------------------------------------------------------------TR
    //                        False = True
    //
    if (foldPremises.size() > 1 && !assumptions.count(foldConclusion))
    {
      // create transitivity step to derive expected premise
      buildTransitivityChain(foldConclusion, foldPremises);
      Trace("eqproof-conv")
          << "EqProof::foldTransitivityChildren: add transitivity step for "
          << foldConclusion << " with premises " << foldPremises << "\n";
      // create folding step
      if (!p->addStep(foldConclusion, PfRule::TRANS, foldPremises, {}, true))
      {
        Assert(false) << "EqProof::foldTransitivityChildren: couldn't add "
                         "folding trans step from "
                      << foldPremises << " to " << foldConclusion << "\n";
      }
    }
  }
  // now build the proof step for the original conclusion
  premises.clear();
  premises.push_back(premise);
  Trace("eqproof-conv")
      << "EqProof::foldTransitivityChildren: now derive conclusion "
      << conclusion;
  if (inSubstCase)
  {
    Trace("eqproof-conv") << (substConclusionInReverseOrder ? " [inverted]"
                                                            : "")
                          << " via subsitution from " << premise
                          << " and (inverted subst) " << substPremises << "\n";
    // cong step between subst premises
    Node congConclusion = nm->mkNode(
        kind::EQUAL,
        nm->mkNode(kind::EQUAL, substPremises[0][0], substPremises[1][0]),
        premise[0]);
    if (!p->addStep(congConclusion,
                    PfRule::CONG,
                    substPremises,
                    {nm->operatorOf(kind::EQUAL)},
                    true))
    {
      Assert(false) << "EqProof::foldTransitivityChildren: couldn't add "
                       "congruence step for "
                    << congConclusion << " equating conclusion "
                    << conclusion[0] << " and premise " << premise[0]
                    << " of substitution\n";
    }
    Trace("eqproof-conv")
        << "EqProof::foldTransitivityChildren: via congruence derived "
        << congConclusion << "\n";
    // transitivity step between that and the original premise
    premises.insert(premises.begin(), congConclusion);
    Node transConclusion =
        !substConclusionInReverseOrder
            ? conclusion
            : nm->mkNode(kind::EQUAL, congConclusion[0], conclusion[1]);
    if (!assumptions.count(transConclusion))
    {
      if (!p->addStep(transConclusion, PfRule::TRANS, premises, {}, true))
      {
        Assert(false) << "EqProof::foldTransitivityChildren: couldn't add "
                         "transitivity step for deriving "
                      << transConclusion << " from " << premises << "\n";
      }
      Trace("eqproof-conv")
          << "EqProof::foldTransitivityChildren: via transitivity derived "
          << transConclusion << "\n";
    }
    // if order is reversed, to a MACRO_SR_PRED_TRANSFORM step
    if (substConclusionInReverseOrder)
    {
      if (!p->addStep(conclusion,
                      PfRule::MACRO_SR_PRED_TRANSFORM,
                      {transConclusion},
                      {conclusion},
                      true))
      {
        Assert(false) << "EqProof::foldTransitivityChildren: couldn't add "
                         "final rewriting step from "
                      << transConclusion << " into " << conclusion << "\n";
      }
      Trace("eqproof-conv")
          << "EqProof::foldTransitivityChildren: via macro transform derived "
          << conclusion << "\n";
    }
  }
  else
  {
    // create TRUE_INTRO step for foldConclusion
    Trace("eqproof-conv")
        << " via transitivity.\nEqProof::foldTransitivityChildren: adding "
        << PfRule::TRUE_INTRO << " step for " << foldConclusion[0] << "\n";
    Node newFoldConclusion = foldConclusion.eqNode(nm->mkConst<bool>(true));
    if (!p->addStep(
            newFoldConclusion, PfRule::TRUE_INTRO, {foldConclusion}, {}))
    {
      Assert(false) << "EqProof::foldTransitivityChildren: couldn't add "
                    << PfRule::TRUE_INTRO << " rule\n";
    }
    premises.push_back(newFoldConclusion);
    Trace("eqproof-conv") << PfRule::MACRO_SR_PRED_TRANSFORM << " from "
                          << premises << "\n";
    buildTransitivityChain(conclusion, premises);
    // create final transitivity step
    if (!p->addStep(conclusion, PfRule::TRANS, premises, {}, true))
    {
      Assert(false) << "EqProof::foldTransitivityChildren: couldn't add "
                       "final trans step\n";
    }
  }
  return true;
}

bool EqProof::buildTransitivityChain(Node conclusion,
                                     std::vector<Node>& premises) const
{
  Trace("eqproof-conv") << push
                        << "EqProof::buildTransitivityChain: Build chain for "
                        << conclusion << " with premises " << premises << "\n";
  for (unsigned i = 0, size = premises.size(); i < size; ++i)
  {
    bool occurs = false, correctlyOrdered = false;
    if (conclusion[0] == premises[i][0])
    {
      occurs = correctlyOrdered = true;
    }
    else if (conclusion[0] == premises[i][1])
    {
      occurs = true;
    }
    if (occurs)
    {
      Trace("eqproof-conv")
          << "EqProof::buildTransitivityChain: found " << conclusion[0] << " in"
          << (correctlyOrdered ? "" : " non-") << " ordered premise "
          << premises[i] << "\n";
      if (conclusion[1] == (correctlyOrdered ? premises[i][1] : premises[i][0]))
      {
        Trace("eqproof-conv")
            << "EqProof::buildTransitivityChain: found " << conclusion[1]
            << " in same premise. Closed chain.\n"
            << pop;
        premises.clear();
        premises.push_back(conclusion);
        return true;
      }
      // build chain with remaining equalities
      std::vector<Node> recursivePremises;
      for (unsigned j = 0; j < size; ++j)
      {
        if (j != i)
        {
          recursivePremises.push_back(premises[j]);
        }
      }
      Node newTarget = correctlyOrdered ? premises[i][1].eqNode(conclusion[1])
                                        : premises[i][0].eqNode(conclusion[1]);
      Trace("eqproof-conv")
          << "EqProof::buildTransitivityChain: search recursively for "
          << newTarget << "\n";
      bool success = buildTransitivityChain(newTarget, recursivePremises);
      if (success)
      {
        Trace("eqproof-conv")
            << "EqProof::buildTransitivityChain: closed chain with "
            << 1 + recursivePremises.size() << " of the original "
            << premises.size() << " premises\n"
            << pop;
        premises.clear();
        premises.insert(premises.begin(),
                        correctlyOrdered
                            ? premises[i]
                            : premises[i][1].eqNode(premises[i][0]));
        premises.insert(
            premises.end(), recursivePremises.begin(), recursivePremises.end());
        return true;
      }
    }
  }
  Trace("eqproof-conv")
      << "EqProof::buildTransitivityChain: Could not build chain for"
      << conclusion << " with premises " << premises << "\n";
  Trace("eqproof-conv") << pop;
  return false;
}

void EqProof::reduceNestedCongruence(
    unsigned i,
    Node conclusion,
    std::vector<std::vector<Node>>& children,
    CDProof* p,
    std::unordered_map<Node, Node, NodeHashFunction>& visited,
    std::unordered_set<Node, NodeHashFunction>& assumptions,
    bool isNary) const
{
  Trace("eqproof-conv") << "EqProof::reduceNestedCongruence: building for " << i
                        << "-th arg\n";
  if (d_id == MERGED_THROUGH_CONGRUENCE)
  {
    Assert(d_children.size() == 2);
    Trace("eqproof-conv") << "EqProof::reduceNestedCongruence: it's a "
                             "congruence step. Reduce second child\n"
                          << push;
    children[i].push_back(
        d_children[1].get()->addToProof(p, visited, assumptions));
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
          i - 1, conclusion, children, p, visited, assumptions, isNary);
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
  Assert(d_node.isNull()
         || d_node[0].getNumChildren() == d_node[1].getNumChildren() || isNary)
      << "Non-null (internal cong) transitivity conclusion of different arity "
         "but not marked by isNary flag\n";
  // if handling n-ary kinds and got a trans conclusion, we can just stop here
  // (in fact, it might be *necessary*). The arity of the original conclusion
  // will later be changet to arity - i.
  if (isNary && !d_node.isNull())
  {
    Trace("eqproof-conv") << "EqProof::reduceNestedCongruence: n-ary case, "
                             "break recursion and indepedently process "
                          << d_node << "\n"
                          << push;
    children[i].push_back(addToProof(p, visited, assumptions));
    Trace("eqproof-conv") << pop
                          << "EqProof::reduceNestedCongruence: Got conclusion "
                          << children[i].back()
                          << " from n-ary transitivity processing\n";
    return;
  }
  // regular recursive processing
  for (unsigned j = 0, sizeTrans = d_children.size(); j < sizeTrans; ++j)
  {
    if (d_children[j].get()->d_id == MERGED_THROUGH_CONGRUENCE)
    {
      Trace("eqproof-conv") << "EqProof::reduceNestedCongruence: Reduce " << j
                            << "-th transitivity congruence child\n"
                            << push;
      d_children[j].get()->reduceNestedCongruence(
          i, conclusion, children, p, visited, assumptions, isNary);
      Trace("eqproof-conv") << pop;
    }
    else
    {
      Trace("eqproof-conv") << "EqProof::reduceNestedCongruence: Add " << j
                            << "-th transitivity child to proof\n"
                            << push;
      children[i].push_back(
          d_children[j].get()->addToProof(p, visited, assumptions));
      Trace("eqproof-conv") << pop;
    }
  }
}

Node EqProof::addToProof(CDProof* p) const
{
  std::unordered_map<Node, Node, NodeHashFunction> cache;
  std::unordered_set<Node, NodeHashFunction> assumptions;
  Node conclusion = addToProof(p, cache, assumptions);
  Trace("eqproof-conv") << "EqProof::addToProof: root of proof: " << conclusion
                        << "\n";
  Trace("eqproof-conv") << "EqProof::addToProof: tracked assumptions: "
                        << assumptions << "\n";
  // If conclusion t1 = tn is, modulo symmetry, of the form (= t true/false), in
  // which t is not true/false, it must be turned into t or (not t) with
  // TRUE/FALSE_ELIM.
  Node newConclusion = conclusion;
  Assert(conclusion.getKind() == kind::EQUAL);
  if ((conclusion[0].getKind() == kind::CONST_BOOLEAN
       && conclusion[1].getKind() != kind::CONST_BOOLEAN)
      || (conclusion[1].getKind() == kind::CONST_BOOLEAN
          && conclusion[0].getKind() != kind::CONST_BOOLEAN))
  {
    Trace("eqproof-conv")
        << "EqProof::addToProof: process root for TRUE/FALSE_ELIM\n";
    // Index of constant in equality
    unsigned constIndex =
        conclusion[0].getKind() == kind::CONST_BOOLEAN ? 0 : 1;
    // The premise for the elimination rule must have the constant as the second
    // argument of the equality. If that's not the case, build it as such
    Node elimPremise =
        constIndex == 1 ? conclusion : conclusion[1].eqNode(conclusion[0]);
    // Determine whether TRUE_ELIM or FALSE_ELIM, depending on the constant
    // value. The new conclusion, whether t or (not t), is also determined
    // accordingly.
    //
    // We also track  which intro rule, TRUE_INTRO or FALSE_INTRO, could have
    // been used to introduce the conclusion (= t true/false), modulo symmetry,
    // in case t / (not t) is an assumption, so that we avoid creating a cyclic
    // proof with t / (not t) being derived with t / (not t) as an assumption.
    PfRule elimRule, introRule;
    if (conclusion[constIndex].getConst<bool>())
    {
      elimRule = PfRule::TRUE_ELIM;
      newConclusion = conclusion[1 - constIndex];
      introRule = PfRule::TRUE_INTRO;
    }
    else
    {
      elimRule = PfRule::FALSE_ELIM;
      newConclusion = conclusion[1 - constIndex].notNode();
      introRule = PfRule::FALSE_INTRO;
    }
    // The cycle is characterized, for example, by
    //
    //    t
    //   ----- TRUE_INTRO
    //   (= t true)
    //   ----------
    //     ....
    //   ----------
    //   ()
    bool cyclic = false;
    std::shared_ptr<ProofNode> pc = p->getProofFor(conclusion);
    if (assumptions.count(newConclusion))
    {
      cyclic = true;
    }
    else if (pc.get()->getRule() == introRule)
    {
      Trace("eqproof-conv") << "EqProof::addToProof: root came from "
                            << introRule << ", avoid " << elimRule << " step\n";
      cyclic = true;
    }
    else if (pc.get()->getRule() == PfRule::SYMM)
    {
      const std::vector<std::shared_ptr<ProofNode>>& pcc = pc->getChildren();
      Trace("eqproof-conv")
          << "EqProof::addToProof: root came from " << PfRule::SYMM
          << ", check its child " << pcc[0].get()->getResult()
          << " derived via " << pcc[0].get()->getRule() << "\n";
      if (pcc[0].get()->getRule() == introRule)
      {
        Trace("eqproof-conv")
            << "EqProof::addToProof: root child came from " << introRule
            << ", avoid " << elimRule << " step\n";
        cyclic = true;
      }
    }
    if (!cyclic)
    {
      Trace("eqproof-conv")
          << "EqProof::addToProof: conclude " << newConclusion << " via "
          << elimRule << " step for " << elimPremise << ", introduced via "
          << p->getProofFor(conclusion).get()->getRule() << "\n";
      if (!p->addStep(newConclusion, elimRule, {elimPremise}, {}))
      {
        Assert(false) << "EqProof::addToProof: couldn't add " << elimRule
                      << " rule\n";
      }
    }
  }
  return newConclusion;
}

Node EqProof::addToProof(
    CDProof* p,
    std::unordered_map<Node, Node, NodeHashFunction>& visited,
    std::unordered_set<Node, NodeHashFunction>& assumptions) const
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
    // (= t true/false) case, in which t is not a Boolean variable
    if (d_node.getKind() == kind::EQUAL
        && ((d_node[0].getKind() == kind::CONST_BOOLEAN
             && d_node[1].getKind() != kind::CONST_BOOLEAN)
            || (d_node[1].getKind() == kind::CONST_BOOLEAN
                && d_node[0].getKind() != kind::CONST_BOOLEAN)))
    {
      Trace("eqproof-conv")
          << "EqProof::addToProof: add an intro step for " << d_node << "\n";
      unsigned constIndex = d_node[0].getKind() == kind::CONST_BOOLEAN ? 0 : 1;
      std::vector<Node> introChildren;
      PfRule introRule;
      if (d_node[constIndex].getConst<bool>())
      {
        introRule = PfRule::TRUE_INTRO;
        Node introChild = d_node[1 - constIndex];
        introChildren.push_back(introChild);
        // track it and, if it's an equality, its symmetric
        assumptions.insert(introChild);
        if (introChild.getKind() == kind::EQUAL)
        {
          assumptions.insert(introChild[1].eqNode(introChild[0]));
        }
      }
      else
      {
        introRule = PfRule::FALSE_INTRO;
        Node introChild = d_node[1 - constIndex].notNode();
        introChildren.push_back(introChild);
        // track it and, if it's a negated equality, its symmetric
        assumptions.insert(introChild);
        if (introChild[0].getKind() == kind::EQUAL)
        {
          assumptions.insert(
              introChild[0][1].eqNode(introChild[0][0]).notNode());
        }
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
        // add (not lit)
        assumptions.insert(d_node);
      }
      else
      {
        intro = PfRule::TRUE_INTRO;
        conclusion =
            d_node.eqNode(NodeManager::currentNM()->mkConst<bool>(true));
        // add lit
        assumptions.insert(d_node);
      }
      Trace("eqproof-conv") << "EqProof::addToProof: adding " << intro
                            << " step for " << d_node << "\n";
      if (!p->addStep(conclusion, intro, {d_node}, {}))
      {
        Assert(false) << "EqProof::addToProof: couldn't add " << intro
                      << " rule from " << d_node << "\n";
      }
    }
    // keep track of assumptions to avoid cyclic proofs. Both the assumption and
    // its symmetric are added
    assumptions.insert(conclusion);
    assumptions.insert(conclusion[1].eqNode(conclusion[0]));
    Trace("eqproof-conv") << "EqProof::addToProof: tracking assumptions "
                          << conclusion << ", (= " << conclusion[1] << " "
                          << conclusion[0] << ")\n";
    visited[d_node] = conclusion;
    return conclusion;
  }
  // refl and laborious congruence steps of (= (f t1 ... tn) (f t1 ... tn))
  if (d_id == MERGED_THROUGH_REFLEXIVITY
      || (d_node.getKind() == kind::EQUAL && d_node[0] == d_node[1]))
  {
    Trace("eqproof-conv-debug") << "Refl node: " << d_node << std::endl;
    Node conclusion =
        d_node.getKind() == kind::EQUAL ? d_node : d_node.eqNode(d_node);
    if (!p->addStep(conclusion, PfRule::REFL, {}, {conclusion[0]}))
    {
      Assert(false) << "EqProof::addToProof: couldn't add refl step\n";
    }
    visited[d_node] = conclusion;
    return conclusion;
  }
  // can support case of negative merged throgh constants, but not positive one
  // yet
  if (d_id == MERGED_THROUGH_CONSTANTS)
  {
    Assert(!d_node.isNull() && d_node.getKind() == kind::EQUAL
           && d_node[0].getKind() == kind::EQUAL
           && d_node[1].getKind() == kind::CONST_BOOLEAN
           && !d_node[1].getConst<bool>())
        << ". Conclusion " << d_node << " from "
        << static_cast<MergeReasonType>(d_id)
        << " was expected to be (= (= t1 t2) false)\n";
    Assert(!assumptions.count(d_node))
        << "Conclusion " << d_node << " from "
        << static_cast<MergeReasonType>(d_id) << " is an assumption\n";
    // Build
    //
    // (= t1 c1)  (= t2 c2)
    // -------------------- MACRO_SR_PRED_INTRO
    //  (= (= t1 t2) false)
    //
    // First process the children proofs
    std::vector<Node> premises;
    for (unsigned i = 0; i < d_children.size(); ++i)
    {
      Trace("eqproof-conv")
          << "EqProof::addToProof: recurse on child " << i << "\n"
          << push;
      premises.push_back(
          d_children[i].get()->addToProof(p, visited, assumptions));
      Trace("eqproof-conv") << pop;
    }
    // build rule premises in right order
    std::vector<Node> children;
    // Now get the constants in the premises
    for (unsigned i = 0; i < 2; ++i)
    {
      Node term = d_node[0][i];
      if (term.isConst())
      {
        continue;
      }
      Node constant;
      // look in children
      for (unsigned j = 0; j < premises.size(); ++j)
      {
        Trace("eqproof-conv-debug") << "Premise : " << premises[j] << std::endl;
        AlwaysAssert(premises[j].getKind() == kind::EQUAL);
        if (premises[j][0] == term)
        {
          Assert(premises[j][1].isConst());
          constant = premises[j][1];
        }
        else if (premises[j][1] == term)
        {
          Assert(premises[j][0].isConst());
          constant = premises[j][0];
        }
      }
      children.push_back(term.eqNode(constant));
    }
    Trace("eqproof-conv") << "EqProof::addToProof: adding "
                          << PfRule::MACRO_SR_PRED_INTRO << " step from "
                          << children << "\n";
    if (!p->addStep(d_node, PfRule::MACRO_SR_PRED_INTRO, children, {d_node}))
    {
      Assert(false) << "EqProof::addToProof: couldn't add "
                    << PfRule::MACRO_SR_PRED_INTRO << " rule\n";
    }
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
    // if conclusion is (not (= t1 t2)) change it to (= (= t1 t2) false) so that
    // the reasoning below is uniform. A FALSE_ELIM to revert this is only
    // necessary when this is the root. That step is done in the non-recursive
    // caller of this function
    Node conclusion =
        d_node.getKind() != kind::NOT
            ? d_node
            : d_node[0].eqNode(NodeManager::currentNM()->mkConst<bool>(false));
    // if the conclusion is an assumption, the proof processing below may
    // potentially be generate cyclic proofs, which will be useless anyway since
    // this is an assumption
    if (assumptions.count(conclusion))
    {
      visited[d_node] = conclusion;
      return conclusion;
    }
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
          Node child = childProof->d_children[j].get()->addToProof(
              p, visited, assumptions);
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
      children.push_back(childProof->addToProof(p, visited, assumptions));
      Trace("eqproof-conv") << pop;
    }
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
    bool folded =
        foldTransitivityChildren(conclusion, children, p, assumptions);
    Assert(!folded || p->hasStep(conclusion));
    if (!folded)
    {
      cleanReflPremisesInTranstivity(children);
      Assert(!children.empty());
      Trace("eqproof-conv")
          << "EqProof::addToProof: build chain for transitivity premises"
          << children << " to conclude " << conclusion << "\n";
      // conclusion is t1 = tn. Children MUST BE (= t1 t2), ..., (= t{n-1} tn).
      // If t1 or tn are true or false, then premises may have to be amended
      // with TRUE/FALSE intro rules. Process children to ensure this
      buildTransitivityChain(conclusion, children);
      // add step while making sure that all children have been added to the
      // proof, as well as that the proof should be rewritten in case it exists.
      // Overwritting is necessary because of a literal potentially having
      // different explanations at different points of the solving.
      Assert(children.size() > 1
             || (!children.empty()
                 && (children[0] == conclusion
                     || children[0][1].eqNode(children[0][0]) == conclusion)));
      if (children.size() > 1)
      {
        if (!p->addStep(conclusion, PfRule::TRANS, children, {}, true))
        {
          Assert(false) << "EqProof::addToProof: couldn't add TRANS "
                        << conclusion << " " << children << "\n";
        }
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
  //
  // N-ary operators are fun. The following proof is a valid congruence proof
  //
  //   (= (f t1 t2 t3) (f t6 t5)) (= (f t6 t5) (f t5 t6))
  //   -------------------------------------------------- TR
  //             (= (f t1 t2 t3) (f t5 t6))                 (= t4 t7)
  //          ------------------------------------------------------ CONG
  //          (= (f t1 t2 t3 t4) (f t5 t6 t7))
  //
  // The reason it's valid is that the conclusion is actually
  //
  //   (= (f (f t1 t2 t3) t4) (f (f t5 t6) t7))
  //
  // which means that one of the internal congruence steps will *necessarily* be
  // a transitivity step corresponding to the "arity mismatch". To process the
  // above proof correctly we assume the maximal arity (4 in the above example)
  // and, when an internal transitivity proof is found that equates applications
  // of different arity, the recursion halts and that proof is processed
  // indepedently. Thus, in the matrix of children at least one of the initial
  // rows will be empty. The new arity will be the orginal one minus the number
  // of empty rows.
  //
  // Moreover note that a situation as above may happen EVEN WHEN THE ARITY IS
  // THE SAME:
  //
  //    (= (f t1 t2) x)    (= (f t1 t4) x)
  //   ----------------------------------- TR
  //      (= (f t1 t2) (f t1 t4))                 (= t3 t5)
  //     --------------------------------------------------- CONG
  //          (= (f t1 t2 t3) (f t1 t4 t5))
  unsigned arity = d_node[0].getNumChildren();
  Kind k = d_node[0].getKind();
  bool isNary = ExprManager::isNAryKind(k);
  // if mismatch, update arity to be initially the maximal one
  if (d_node[0].getNumChildren() != d_node[1].getNumChildren())
  {
    Assert(isNary);
    arity =
        d_node[1].getNumChildren() < arity ? arity : d_node[1].getNumChildren();
    Trace("eqproof-conv")
        << "EqProof::addToProof: Mismatching arities in cong conclusion "
        << d_node << ". Use tentative arity " << arity << "\n";
  }
  // premises to be retrieved
  std::vector<std::vector<Node>> transitivityChildren;
  // intialize children matrix
  for (unsigned i = 0; i < arity; ++i)
  {
    transitivityChildren.push_back(std::vector<Node>());
  }
  reduceNestedCongruence(
      arity - 1, d_node, transitivityChildren, p, visited, assumptions, isNary);
  // may change conclusion if in n-ary case, so use alias
  Node conclusion = d_node;
  NodeManager* nm = NodeManager::currentNM();
  if (isNary)
  {
    unsigned emptyRows = 0;
    for (unsigned i = 0; i < arity; ++i)
    {
      if (transitivityChildren[i].empty())
      {
        emptyRows++;
      }
    }
    if (emptyRows > 0)
    {
      Trace("eqproof-conv")
          << "EqProof::addToProof: Found " << emptyRows
          << " empty rows. Rebuild conclusion " << d_node << "\n";
      std::vector<std::vector<Node>> newTransitivityChildren{
          transitivityChildren.begin() + emptyRows, transitivityChildren.end()};
      transitivityChildren.clear();
      transitivityChildren.insert(transitivityChildren.begin(),
                                  newTransitivityChildren.begin(),
                                  newTransitivityChildren.end());
      // build new conclusion
      unsigned arityPrefix1 =
          emptyRows + 1 - (arity - d_node[0].getNumChildren());
      Assert(arityPrefix1 < d_node[0].getNumChildren())
          << "arityPrefix1 " << arityPrefix1 << " not smaller than "
          << d_node[0] << "'s arity " << d_node[0].getNumChildren() << "\n";
      unsigned arityPrefix2 =
          emptyRows + 1 - (arity - d_node[1].getNumChildren());
      Assert(arityPrefix2 < d_node[1].getNumChildren())
          << "arityPrefix2 " << arityPrefix2 << " not smaller than "
          << d_node[1] << "'s arity " << d_node[1].getNumChildren() << "\n";
      Trace("eqproof-conv") << "EqProof::addToProof: New internal "
                               "applications with arities "
                            << arityPrefix1 << ", " << arityPrefix2 << ":\n";
      std::vector<Node> childrenPrefix1{d_node[0].begin(),
                                        d_node[0].begin() + arityPrefix1};
      std::vector<Node> childrenPrefix2{d_node[1].begin(),
                                        d_node[1].begin() + arityPrefix2};
      Node newFirstChild1 = nm->mkNode(k, childrenPrefix1);
      Node newFirstChild2 = nm->mkNode(k, childrenPrefix2);
      Trace("eqproof-conv")
          << "EqProof::addToProof:\t " << newFirstChild1 << "\n";
      Trace("eqproof-conv")
          << "EqProof::addToProof:\t " << newFirstChild2 << "\n";
      std::vector<Node> newChildren1{newFirstChild1};
      newChildren1.insert(newChildren1.end(),
                          d_node[0].begin() + arityPrefix1,
                          d_node[0].end());
      std::vector<Node> newChildren2{newFirstChild2};
      newChildren2.insert(newChildren2.end(),
                          d_node[1].begin() + arityPrefix2,
                          d_node[1].end());
      conclusion = nm->mkNode(kind::EQUAL,
                              nm->mkNode(k, newChildren1),
                              nm->mkNode(k, newChildren2));
      // update arity
      Assert((arity - emptyRows) == conclusion[0].getNumChildren());
      arity = arity - emptyRows;
      Trace("eqproof-conv")
          << "EqProof::addToProof: New conclusion " << conclusion << "\n";
    }
  }
  if (Trace.isOn("eqproof-conv"))
  {
    Trace("eqproof-conv")
        << "EqProof::addToProof: premises from reduced cong of " << conclusion
        << ":\n";
    for (unsigned i = 0; i < arity; ++i)
    {
      Trace("eqproof-conv") << "EqProof::addToProof:\t" << i
                            << "-th arg: " << transitivityChildren[i] << "\n";
    }
  }
  // The above builds a matrix, for n = arity -1:
  //
  //   [0] -> p_{0,0} ... p_{m_0,0}
  //   ...
  //   [n] -> p_{0,n} ... p_{m_n,n}
  //
  // in which each row has at least one premise. Rows with more than one premise
  // may require transitivity steps.
  //
  // An invariant is that for every row i we must derive a_i = b_i, given the
  // congruence conclusion (f a_0 ... a_n) = (f b_1 ... b_n). That will either
  // be the sole premise in the row (modulo reflexivity) or the result of a
  // transitivity step.
  std::vector<Node> children(arity);
  for (unsigned i = 0; i < arity; ++i)
  {
    Node transConclusion = conclusion[0][i].eqNode(conclusion[1][i]);
    children[i] = transConclusion;
    Assert(!transitivityChildren[i].empty())
        << "EqProof::addToProof: did not add any justification for " << i
        << "-th arg of congruence " << conclusion << "\n";
    cleanReflPremisesInTranstivity(transitivityChildren[i]);
    // nothing to do
    Assert(transitivityChildren[i].size() > 1 || transitivityChildren[i].empty()
           || transitivityChildren[i][0] == transConclusion
           || (transitivityChildren[i][0][0] == transConclusion[1]
               && transitivityChildren[i][0][1] == transConclusion[0]))
        << "EqProof::addToProof: premises " << transitivityChildren[i] << "for "
        << i << "-th cong premise " << transConclusion << " don't justify it\n";
    unsigned sizeTrans = transitivityChildren[i].size();
    // if no transitivity premise left or if the conclusion is an assumption
    // (which might lead to a cycle with a transtivity step), nothing else to do
    if (sizeTrans == 0 || assumptions.count(transConclusion) > 0)
    {
      continue;
    }
    // if the transitivity conclusion is a reflexivity step (this can happen due
    // to the n-ary congruences between the same term being explained not by
    // reflexivity in the current equality engine), just add a reflexivity step
    if (transConclusion[0] == transConclusion[1])
    {
      if (!p->addStep(transConclusion, PfRule::REFL, {}, {transConclusion[0]}))
      {
        Assert(false) << "EqProof::addToProof: couldn't add refl step\n";
      }
      continue;
    }
    // if the transitivity conclusion, or its symmetric, occurs in the
    // transitivity premises, nothing to do
    bool occurs = false;
    for (unsigned j = 0; j < sizeTrans && !occurs; ++j)
    {
      if (transitivityChildren[i][j] == transConclusion
          || (transitivityChildren[i][j][0] == transConclusion[1]
              && transitivityChildren[i][j][1] == transConclusion[0]))
      {
        occurs = true;
      }
    }
    if (!occurs)
    {
      // Build transitivity step. Apply a reconstructor that greedily builds a
      // closed chain for the given conclusion
      buildTransitivityChain(transConclusion, transitivityChildren[i]);
      Trace("eqproof-conv")
          << "EqProof::addToProof: adding trans step for cong premise "
          << transConclusion << " with children " << transitivityChildren[i]
          << "\n";
      if (!p->addStep(transConclusion,
                      PfRule::TRANS,
                      transitivityChildren[i],
                      {},
                      true))
      {
        Assert(false) << "EqProof::addToProof: couldn't add trans step\n";
      }
    }
  }
  Trace("eqproof-conv")
      << "EqProof::addToProof: premises after adding trans steps:" << children
      << "\n";
  // build args
  std::vector<Node> args;
  if (kind::metaKindOf(k) == kind::metakind::PARAMETERIZED)
  {
    args.push_back(conclusion[0].getOperator());
  }
  else
  {
    args.push_back(NodeManager::currentNM()->operatorOf(k));
  }
  // build conclusion
  Trace("eqproof-conv") << "EqProof::addToProof: build cong step of "
                        << conclusion << " with op " << args[0]
                        << " and children " << children << "\n";
  if (!p->addStep(conclusion, PfRule::CONG, children, args, true))
  {
    Assert(false) << "EqProof::addToProof: couldn't add cong step\n";
  }
  // whether had to change cong conclusion because of n-ary handling
  if (conclusion != d_node)
  {
    Trace("eqproof-conv") << "EqProof::addToProof: add "
                          << PfRule::MACRO_SR_PRED_TRANSFORM
                          << " step to flatten rebuilt conclusion "
                          << conclusion << "into " << d_node << "\n";
    if (!p->addStep(d_node,
                    PfRule::MACRO_SR_PRED_TRANSFORM,
                    {conclusion},
                    {d_node},
                    true))
    {
      Assert(false) << "EqProof::addToProof: couldn't add "
                    << PfRule::MACRO_SR_PRED_TRANSFORM << " step\n";
    }
  }
  if (Trace.isOn("eqproof-conv"))
  {
    Trace("eqproof-conv") << "EqProof::addToProof: proof node of " << conclusion
                          << " is:\n";
    std::stringstream out;
    p->getProofFor(conclusion).get()->printDebug(out);
    Trace("eqproof-conv") << out.str() << "\n";
  }
  visited[d_node] = d_node;
  return d_node;
}

}  // namespace eq
}  // Namespace theory
}  // Namespace CVC4
