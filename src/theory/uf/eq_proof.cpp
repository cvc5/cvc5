/*********************                                                        */
/*! \file eq_proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
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

void EqProof::debug_print(const char* c, unsigned tb) const
{
  std::stringstream ss;
  debug_print(ss, tb);
  Debug(c) << ss.str();
}

void EqProof::debug_print(std::ostream& os, unsigned tb) const
{
  for (unsigned i = 0; i < tb; i++)
  {
    os << "  ";
  }
  os << d_id << "(";
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
    d_children[i]->debug_print(os, tb + 1);
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

void EqProof::cleanReflPremises(std::vector<Node>& premises) const
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
    Trace("eqproof-conv") << "EqProof::cleanReflPremises: removed "
                          << (newPremises.size() >= size
                                  ? newPremises.size() - size
                                  : 0)
                          << " refl premises from " << premises << "\n";
    premises.clear();
    premises.insert(premises.end(), newPremises.begin(), newPremises.end());
    Trace("eqproof-conv") << "EqProof::cleanReflPremises: new premises "
                          << premises << "\n";
  }
}

bool EqProof::expandTransitivityForDisequalities(
    Node conclusion,
    std::vector<Node>& premises,
    CDProof* p,
    std::unordered_set<Node, NodeHashFunction>& assumptions) const
{
  Trace("eqproof-conv")
      << "EqProof::expandTransitivityForDisequalities: check if need "
         "to expand transitivity step to conclude "
      << conclusion << " from premises " << premises << "\n";
  // Check premises to see if any of the form (= (= t1 t2) false), modulo
  // symmetry
  unsigned size = premises.size();
  // termPos is, in (= (= t1 t2) false) or (= false (= t1 t2)), the position of
  // the equality. When the i-th premise has that form, offending = i
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
  NodeManager* nm = NodeManager::currentNM();
  Assert(termPos == 0 || termPos == 1);
  Trace("eqproof-conv") << "EqProof::expandTransitivityForDisequalities: found "
                           "offending equality at index "
                        << offending << " : " << premises[offending] << "\n";
  // collect the premises to be used in the expansion, which are all but the
  // offending one
  std::vector<Node> expansionPremises;
  for (unsigned i = 0; i < size; ++i)
  {
    if (i != offending)
    {
      expansionPremises.push_back(premises[i]);
    }
  }
  // Eliminate spurious premises. Reasoning below assumes no refl steps.
  cleanReflPremises(expansionPremises);
  Assert(!expansionPremises.empty());
  // Check if we are in the substitution case
  Node expansionConclusion;
  std::vector<Node> substPremises;
  bool inSubstCase = false, substConclusionInReverseOrder = false;
  if ((conclusion[0].getKind() == kind::CONST_BOOLEAN)
      != (conclusion[1].getKind() == kind::CONST_BOOLEAN))
  {
    inSubstCase = true;
    // reorder offending premise if constant is the first argument
    if (termPos == 1)
    {
      premises[offending] =
          premises[offending][1].eqNode(premises[offending][0]);
    }
    // reorder conclusion if constant is the first argument
    conclusion = conclusion[1].getKind() == kind::CONST_BOOLEAN
                     ? conclusion
                     : conclusion[1].eqNode(conclusion[0]);
    // equality term in premise disequality
    Node premiseTermEq = premises[offending][0];
    // equality term in conclusion disequality
    Node conclusionTermEq = conclusion[0];
    Trace("eqproof-conv")
        << "EqProof::expandTransitivityForDisequalities: Substitition "
           "case. Need to build subst from "
        << premiseTermEq << " to " << conclusionTermEq << "\n";
    // If only one argument in the premise is substituted, premiseTermEq and
    // conclusionTermEq will share one argument and the other argument change
    // defines the single substitution. Otherwise both arguments are replaced,
    // so there are two substitutions.
    std::vector<Node> subs[2];
    subs[0].push_back(premiseTermEq[0]);
    subs[1].push_back(premiseTermEq[1]);
    // which of the arguments of premiseTermEq, if any, is equal to one argument
    // of conclusionTermEq
    int equalArg = -1;
    for (unsigned i = 0; i < 2; ++i)
    {
      for (unsigned j = 0; j < 2; ++j)
      {
        if (premiseTermEq[i] == conclusionTermEq[j])
        {
          equalArg = i;
          // identity sub
          subs[i].push_back(conclusionTermEq[j]);
          // sub that changes argument
          subs[1 - i].push_back(conclusionTermEq[1 - j]);
          // wither e.g. (= t1 t2), with sub t1->t3, becomes (= t2 t3)
          substConclusionInReverseOrder = i != j;
          break;
        }
      }
    }
    // simple case of single substitution
    if (equalArg >= 0)
    {
      // case of
      //   (= (= t1 t2) false) (= t1 x1) ... (= xn t3)
      //  -------------------------------------------- EQP::TR
      //          (= (= t3 t2) false)
      // where
      //
      //   (= t1 x1) ... (= xn t3)           - expansion premises
      //  ------------------------ TRANS
      //          (= t1 t3)                  - expansion conclusion
      //
      // will be the expansion made to justify the substitution for t1->t3.
      expansionConclusion = subs[1 - equalArg][0].eqNode(subs[1 - equalArg][1]);
      Trace("eqproof-conv") << "EqProof::expandTransitivityForDisequalities: "
                               "Need to expand premises into "
                            << expansionConclusion << "\n";
      // add refl step for the substitition t2->t2
      p->addStep(subs[equalArg][0].eqNode(subs[equalArg][1]),
                 PfRule::REFL,
                 {},
                 {subs[equalArg][0]});
    }
    else
    {
      // Hard case. We determine, and justify, the substitutions t1->t3/t4 and
      // t2->t3/t4 based on the expansion premises.
      Trace("eqproof-conv") << "EqProof::expandTransitivityForDisequalities: "
                               "Need two substitutions. Look for "
                            << premiseTermEq[0] << " and " << premiseTermEq[1]
                            << " in premises " << expansionPremises << "\n";
      Assert(expansionPremises.size() >= 2)
          << "Less than 2 expansion premises for substituting BOTH terms in "
             "disequality.\nDisequality: "
          << premises[offending]
          << "\nExpansion premises: " << expansionPremises
          << "\nConclusion: " << conclusion << "\n";
      // Easier case where we can determine the substitutions by directly
      // looking at the premises, i.e. the two expansion premises are for
      // example (= t1 t3) and (= t2 t4)
      if (expansionPremises.size() == 2)
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
              if (premiseTermEq[i] == expansionPremises[j][k])
              {
                subs[i].push_back(expansionPremises[j][1 - k]);
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
        Trace("eqproof-conv") << "EqProof::expandTransitivityForDisequalities: "
                                 "Build transitivity chains "
                                 "for two subs among more than 2 premises: "
                              << expansionPremises << "\n";
        // Hardest case. Try building a transitivity chain for (= t1 t3). If it
        // can be built, use the remaining expansion premises to build a chain
        // for (= t2 t4). Otherwise build it for (= t1 t4) and then build it for
        // (= t2 t3). It should always succeed.
        subs[0].push_back(conclusionTermEq[0]);
        subs[1].push_back(conclusionTermEq[1]);
        for (unsigned i = 0; i < 2; ++i)
        {
          // copy premises, since buildTransitivityChain is destructive
          std::vector<Node> copy1ofExpPremises(expansionPremises.begin(),
                                               expansionPremises.end());
          Node transConclusion1 = subs[0][0].eqNode(subs[0][1]);
          if (!buildTransitivityChain(transConclusion1, copy1ofExpPremises))
          {
            AlwaysAssert(i == 0)
                << "Couldn't find sub at all for substituting BOTH terms in "
                   "disequality.\nDisequality: "
                << premises[offending]
                << "\nExpansion premises: " << expansionPremises
                << "\nConclusion: " << conclusion << "\n";
            // Failed. So flip sub and try again
            subs[0][1] = conclusionTermEq[1];
            subs[1][1] = conclusionTermEq[0];
            substConclusionInReverseOrder = false;
            continue;
          }
          // build next chain
          std::vector<Node> copy2ofExpPremises(expansionPremises.begin(),
                                               expansionPremises.end());
          Node transConclusion2 = subs[1][0].eqNode(subs[1][1]);
          if (!buildTransitivityChain(transConclusion2, copy2ofExpPremises))
          {
            Unreachable() << "Found sub " << transConclusion1
                          << " but not other sub " << transConclusion2
                          << ".\nDisequality: " << premises[offending]
                          << "\nExpansion premises: " << expansionPremises
                          << "\nConclusion: " << conclusion << "\n";
          }
          Trace("eqproof-conv")
              << "EqProof::expandTransitivityForDisequalities: Built trans "
                 "chains: "
                 "for two subs among more than 2 premises:\n";
          Trace("eqproof-conv")
              << "EqProof::expandTransitivityForDisequalities: "
              << transConclusion1 << " <- " << copy1ofExpPremises << "\n";
          Trace("eqproof-conv")
              << "EqProof::expandTransitivityForDisequalities: "
              << transConclusion2 << " <- " << copy2ofExpPremises << "\n";
          // do transitivity steps if need be to justify each substitution
          if (copy1ofExpPremises.size() > 1
              && !assumptions.count(transConclusion1))
          {
            p->addStep(
                transConclusion1, PfRule::TRANS, copy1ofExpPremises, {}, true);
          }
          if (copy2ofExpPremises.size() > 1
              && !assumptions.count(transConclusion2))
          {
            p->addStep(
                transConclusion2, PfRule::TRANS, copy2ofExpPremises, {}, true);
          }
        }
      }
    }
    Trace("eqproof-conv")
        << "EqProof::expandTransitivityForDisequalities: Built substutitions "
        << subs[0] << " and " << subs[1] << " to map " << premiseTermEq
        << " -> " << conclusionTermEq << "\n";
    Assert(subs[0][1] == conclusion[0][0] || subs[0][1] == conclusion[0][1])
        << "EqProof::expandTransitivityForDisequalities: First substitution "
        << subs[0] << " doest not map to conclusion " << conclusion << "\n";
    Assert(subs[1][1] == conclusion[0][0] || subs[1][1] == conclusion[0][1])
        << "EqProof::expandTransitivityForDisequalities: Second substitution "
        << subs[1] << " doest not map to conclusion " << conclusion << "\n";
    // In the premises for the original conclusion, the substitution of
    // premiseTermEq (= t1 t2) into conclusionTermEq (= t3 t4) is stored
    // reversed, i.e. as (= (= t3 t4) (= t1 t2)), since the transitivity with
    // the disequality is built as as
    //   (= (= t3 t4) (= t1 t2))                         (= (= t1 t2) false)
    //  --------------------------------------------------------------------- TR
    //                      (= (= t3 t4) false)
    substPremises.push_back(subs[0][1].eqNode(subs[0][0]));
    substPremises.push_back(subs[1][1].eqNode(subs[1][0]));
  }
  else
  {
    // In simple case the conclusion is always, modulo symmetry, false = true
    Assert(conclusion[0].getKind() == kind::CONST_BOOLEAN
           && conclusion[1].getKind() == kind::CONST_BOOLEAN);
    // The expansion conclusion is the same as the equality term in the
    // disequality, which is going to be justified by a transitivity step from
    // the expansion premises
    expansionConclusion = premises[offending][termPos];
  }
  // Unless we are in the double-substitution case, the proof has the shape
  //
  //                           ... ... ... ...         - expansionPremises
  //                          ------------------ TRANS
  //     (= (= (t t') false)    (= t'' t''')           - expansionConclusion
  //  ---------------------------------------------- TRANS or PRED_TRANSFORM
  //             conclusion
  //
  // although note that if it's a TRANS step, (= t'' t''') will be turned into a
  // predicate equality and the premises are ordered.
  //
  // We build the transitivity step for the expansionConclusion here. It being
  // non-null marks that we are not in the double-substitution case.
  if (!expansionConclusion.isNull())
  {
    Trace("eqproof-conv")
        << "EqProof::expandTransitivityForDisequalities: need to derive "
        << expansionConclusion << " with premises " << expansionPremises
        << "\n";
    Assert(expansionPremises.size() > 1
           || expansionConclusion == expansionPremises.back()
           || (expansionConclusion[0] == expansionPremises.back()[1]
               && expansionConclusion[1] == expansionPremises.back()[0]))
        << "single expansion premise " << expansionPremises.back()
        << " is not the same as expansionConclusion " << expansionConclusion
        << " and not its symmetric\n";
    // We track assumptions to avoid cyclic proofs, which can happen in EqProofs
    // such as:
    //
    //              (= l1 "")     (= "" t)
    //            ----------------------- EQP::TR
    //  (= l1 "")           (= l1 t)                  (= (= "" t) false)
    // ----------------------------------------------------------------- EQP::TR
    //                        (= false true)
    //
    // which would lead to the cyclic expansion proof:
    //
    //       (= l1 "")             (= l1 "")   (= "" t)
    //       --------- SYMM      ----------------------- TRANS
    //       (= "" l1)                     (= l1 t)
    //      ------------------------------------------ TRANS
    //                       (= "" t)
    if (expansionPremises.size() > 1 && !assumptions.count(expansionConclusion))
    {
      // create transitivity step to derive expected premise
      buildTransitivityChain(expansionConclusion, expansionPremises);
      Trace("eqproof-conv")
          << "EqProof::expandTransitivityForDisequalities: add transitivity "
             "step for "
          << expansionConclusion << " with premises " << expansionPremises
          << "\n";
      // create expansion step
      p->addStep(
          expansionConclusion, PfRule::TRANS, expansionPremises, {}, true);
    }
  }
  Trace("eqproof-conv")
      << "EqProof::expandTransitivityForDisequalities: now derive conclusion "
      << conclusion;
  premises.clear();
  premises.push_back(premises[offending]);
  if (inSubstCase)
  {
    Trace("eqproof-conv") << (substConclusionInReverseOrder ? " [inverted]"
                                                            : "")
                          << " via subsitution from " << premises[offending]
                          << " and (inverted subst) " << substPremises << "\n";
    //  By this point, for premise disequality (= (= t1 t2) false), we have
    //  potentially already built
    //
    //     (= t1 x1) ... (= xn t3)      (= t2 y1) ... (= ym t4)
    //    ------------------------ TR  ------------------------ TR
    //     (= t1 t3)                    (= t2 t4)
    //
    // to justify the substitutions t1->t3 and t2->t4 (where note that if t1=t3
    // or t2=4, the step will actually be a REFL one). Not do
    //
    //  ----------- SYMM             ----------- SYMM
    //   (= t3 t1)                    (= t4 t2)
    //  ---------------------------------------- CONG
    //   (= (= t3 t4) (= t1 t2))                         (= (= t1 t2) false)
    //  --------------------------------------------------------------------- TR
    //                   (= (= t3 t4) false)
    //
    // where note that the SYMM steps are implicitly added by CDProof.
    Node congConclusion = nm->mkNode(
        kind::EQUAL,
        nm->mkNode(kind::EQUAL, substPremises[0][0], substPremises[1][0]),
        premises[offending][0]);
    p->addStep(congConclusion,
               PfRule::CONG,
               substPremises,
               {ProofRuleChecker::mkKindNode(kind::EQUAL)},
               true);
    Trace("eqproof-conv") << "EqProof::expandTransitivityForDisequalities: via "
                             "congruence derived "
                          << congConclusion << "\n";
    // transitivity step between that and the original premise
    premises.insert(premises.begin(), congConclusion);
    Node transConclusion =
        !substConclusionInReverseOrder
            ? conclusion
            : nm->mkNode(kind::EQUAL, congConclusion[0], conclusion[1]);
    // check to avoid cyclic proofs
    if (!assumptions.count(transConclusion))
    {
      p->addStep(transConclusion, PfRule::TRANS, premises, {}, true);
      Trace("eqproof-conv") << "EqProof::expandTransitivityForDisequalities: "
                               "via transitivity derived "
                            << transConclusion << "\n";
    }
    // if order is reversed, finish the proof of conclusion with
    //           (= (= t3 t4) false)
    //          --------------------- MACRO_SR_PRED_TRANSFORM
    //           (= (= t4 t3) false)
    if (substConclusionInReverseOrder)
    {
      p->addStep(conclusion,
                 PfRule::MACRO_SR_PRED_TRANSFORM,
                 {transConclusion},
                 {conclusion},
                 true);
      Trace("eqproof-conv") << "EqProof::expandTransitivityForDisequalities: "
                               "via macro transform derived "
                            << conclusion << "\n";
    }
  }
  else
  {
    // create TRUE_INTRO step for expansionConclusion and add it to the premises
    Trace("eqproof-conv")
        << " via transitivity.\nEqProof::expandTransitivityForDisequalities: "
           "adding "
        << PfRule::TRUE_INTRO << " step for " << expansionConclusion[0] << "\n";
    Node newExpansionConclusion =
        expansionConclusion.eqNode(nm->mkConst<bool>(true));
    p->addStep(
        newExpansionConclusion, PfRule::TRUE_INTRO, {expansionConclusion}, {});
    premises.push_back(newExpansionConclusion);
    Trace("eqproof-conv") << PfRule::TRANS << " from " << premises << "\n";
    buildTransitivityChain(conclusion, premises);
    // create final transitivity step
    p->addStep(conclusion, PfRule::TRANS, premises, {}, true);
  }
  return true;
}

// TEMPORARY NOTE: This may not be enough. Worst case scenario I need to
// reproduce here a search for arbitrary chains between each of the variables in
// the conclusion and a constant
bool EqProof::expandTransitivityForTheoryDisequalities(
    Node conclusion, std::vector<Node>& premises, CDProof* p) const
{
  // whether conclusion is a disequality (= (= t1 t2) false), modulo symmetry
  unsigned termPos = -1;
  for (unsigned i = 0; i < 2; ++i)
  {
    if (conclusion[i].getKind() == kind::CONST_BOOLEAN
        && !conclusion[i].getConst<bool>()
        && conclusion[1 - i].getKind() == kind::EQUAL)
    {
      termPos = i - 1;
      break;
    }
  }
  // no disequality
  if (termPos == static_cast<unsigned>(-1))
  {
    return false;
  }
  Trace("eqproof-conv")
      << "EqProof::expandTransitivityForTheoryDisequalities: check if need "
         "to expand transitivity step to conclude disequality "
      << conclusion << " from premises " << premises << "\n";

  // Check if the premises are (= t1 c1) and (= t2 c2), modulo symmetry
  std::vector<Node> subChildren, constChildren;
  for (unsigned i = 0; i < 2; ++i)
  {
    Node term = conclusion[termPos][i];
    for (const Node& premise : premises)
    {
      for (unsigned j = 0; j < 2; ++j)
      {
        if (premise[j] == term && premise[1 - j].isConst())
        {
          subChildren.push_back(premise[j].eqNode(premise[1 - j]));
          constChildren.push_back(premise[1 - j]);
          break;
        }
      }
    }
  }
  if (subChildren.size() < 2)
  {
    return false;
  }
  // Now build
  //   (= t1 c1)    (= t2 c2)
  //  ------------------------- CONG   ------------------- MACRO_SR_PRED_INTRO
  //   (= (= t1 t2) (= c1 c2))         (= (= c1 c2) false)
  //  --------------------------------------------------------------------- TR
  //                   (= (= t1 t2) false)
  Node constApp = NodeManager::currentNM()->mkNode(kind::EQUAL, constChildren);
  Node constEquality = constApp.eqNode(conclusion[1 - termPos]);
  Trace("eqproof-conv")
      << "EqProof::expandTransitivityForTheoryDisequalities: adding "
      << PfRule::MACRO_SR_PRED_INTRO << " step for " << constApp << " = "
      << conclusion[1 - termPos] << "\n";
  p->addStep(constEquality, PfRule::MACRO_SR_PRED_INTRO, {}, {constEquality});
  // build congruence conclusion (= (= t1 t2) (t c1 c2))
  Node congConclusion = conclusion[termPos].eqNode(constApp);
  Trace("eqproof-conv")
      << "EqProof::expandTransitivityForTheoryDisequalities: adding  "
      << PfRule::CONG << " step for " << congConclusion << " from "
      << subChildren << "\n";
  p->addStep(congConclusion,
             PfRule::CONG,
             {subChildren},
             {ProofRuleChecker::mkKindNode(kind::EQUAL)},
             true);
  Trace("eqproof-conv") << "EqProof::expandTransitivityForDisequalities: via "
                           "congruence derived "
                        << congConclusion << "\n";
  std::vector<Node> transitivityChildren{congConclusion, constEquality};
  p->addStep(conclusion, PfRule::TRANS, {transitivityChildren}, {});
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
      if (conclusion[1] == premises[i][correctlyOrdered ? 1 : 0])
      {
        Trace("eqproof-conv")
            << "EqProof::buildTransitivityChain: found " << conclusion[1]
            << " in same premise. Closed chain.\n"
            << pop;
        premises.clear();
        premises.push_back(conclusion);
        return true;
      }
      // Build chain with remaining equalities
      std::vector<Node> recursivePremises;
      for (unsigned j = 0; j < size; ++j)
      {
        if (j != i)
        {
          recursivePremises.push_back(premises[j]);
        }
      }
      Node newTarget =
          premises[i][correctlyOrdered ? 1 : 0].eqNode(conclusion[1]);
      Trace("eqproof-conv")
          << "EqProof::buildTransitivityChain: search recursively for "
          << newTarget << "\n";
      if (buildTransitivityChain(newTarget, recursivePremises))
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
    std::vector<std::vector<Node>>& transitivityMatrix,
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
    transitivityMatrix[i].push_back(
        d_children[1]->addToProof(p, visited, assumptions));
    Trace("eqproof-conv")
        << pop << "EqProof::reduceNestedCongruence: child conclusion "
        << transitivityMatrix[i].back() << "\n";
    // if i == 0, first child must be REFL step, standing for (= f f), which can
    // be ignored in a first-order calculus
    Assert(i > 0 || d_children[0]->d_id == MERGED_THROUGH_REFLEXIVITY);
    // recurse
    if (i > 0)
    {
      Trace("eqproof-conv")
          << "EqProof::reduceNestedCongruence: Reduce first child\n"
          << push;
      d_children[0]->reduceNestedCongruence(i - 1,
                                            conclusion,
                                            transitivityMatrix,
                                            p,
                                            visited,
                                            assumptions,
                                            isNary);
      Trace("eqproof-conv") << pop;
    }
    return;
  }
  Assert(d_id == MERGED_THROUGH_TRANS);
  Trace("eqproof-conv") << "EqProof::reduceNestedCongruence: it's a "
                           "transitivity step.\n";
  Assert(d_node.isNull()
         || d_node[0].getNumChildren() == d_node[1].getNumChildren() || isNary)
      << "Non-null (internal cong) transitivity conclusion of different arity "
         "but not marked by isNary flag\n";
  // If handling n-ary kinds and got a transitivity conclusion, we process it
  // with addToProof, store the result into row i, and stop. This marks an
  // "adjustment" of the arity, with empty rows 0..i-1 in the matrix determining
  // the adjustment in addToProof processing the congruence of the original
  // conclusion. See details there.
  if (isNary && !d_node.isNull())
  {
    Trace("eqproof-conv") << "EqProof::reduceNestedCongruence: n-ary case, "
                             "break recursion and indepedently process "
                          << d_node << "\n"
                          << push;
    transitivityMatrix[i].push_back(addToProof(p, visited, assumptions));
    Trace("eqproof-conv") << pop
                          << "EqProof::reduceNestedCongruence: Got conclusion "
                          << transitivityMatrix[i].back()
                          << " from n-ary transitivity processing\n";
    return;
  }
  // Regular recursive processing of each transitivity premise
  for (unsigned j = 0, sizeTrans = d_children.size(); j < sizeTrans; ++j)
  {
    if (d_children[j]->d_id == MERGED_THROUGH_CONGRUENCE)
    {
      Trace("eqproof-conv") << "EqProof::reduceNestedCongruence: Reduce " << j
                            << "-th transitivity congruence child\n"
                            << push;
      d_children[j]->reduceNestedCongruence(
          i, conclusion, transitivityMatrix, p, visited, assumptions, isNary);
      Trace("eqproof-conv") << pop;
    }
    else
    {
      Trace("eqproof-conv") << "EqProof::reduceNestedCongruence: Add " << j
                            << "-th transitivity child to proof\n"
                            << push;
      transitivityMatrix[i].push_back(
          d_children[j]->addToProof(p, visited, assumptions));
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
  if ((conclusion[0].getKind() == kind::CONST_BOOLEAN)
      != (conclusion[1].getKind() == kind::CONST_BOOLEAN))
  {
    Trace("eqproof-conv")
        << "EqProof::addToProof: process root for TRUE/FALSE_ELIM\n";
    // Index of constant in equality
    unsigned constIndex =
        conclusion[0].getKind() == kind::CONST_BOOLEAN ? 0 : 1;
    // The premise for the elimination rule must have the constant as the second
    // argument of the equality. If that's not the case, build it as such,
    // relying on an implicit SYMM step to be added to the proof when justifying
    // t / (not t).
    Node elimPremise =
        constIndex == 1 ? conclusion : conclusion[1].eqNode(conclusion[0]);
    // Determine whether TRUE_ELIM or FALSE_ELIM, depending on the constant
    // value. The new conclusion, whether t or (not t), is also determined
    // accordingly.
    PfRule elimRule;
    if (conclusion[constIndex].getConst<bool>())
    {
      elimRule = PfRule::TRUE_ELIM;
      newConclusion = conclusion[1 - constIndex];
    }
    else
    {
      elimRule = PfRule::FALSE_ELIM;
      newConclusion = conclusion[1 - constIndex].notNode();
    }
    // We also check if the final conclusion t / (not t) has already been
    // justified, so that we can avoid a cyclic proof, which can be due to
    // either t / (not t) being assumption in the original EqProof or it having
    // a non-assumption proof step in the proof of (= t true/false).
    if (!assumptions.count(newConclusion) && !p->hasStep(newConclusion))
    {
      Trace("eqproof-conv")
          << "EqProof::addToProof: conclude " << newConclusion << " via "
          << elimRule << " step for " << elimPremise << "\n";
      p->addStep(newConclusion, elimRule, {elimPremise}, {});
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
  Trace("eqproof-conv") << "EqProof::addToProof: adding step for " << d_id
                        << " with conclusion " << d_node << "\n";
  // Assumption
  if (d_id == MERGED_THROUGH_EQUALITY)
  {
    // Check that no (= true/false true/false) assumptions
    if (Configuration::isDebugBuild() && d_node.getKind() == kind::EQUAL)
    {
      for (unsigned i = 0; i < 2; ++i)
      {
        Assert(d_node[i].getKind() != kind::CONST_BOOLEAN
               || d_node[1 - i].getKind() != kind::CONST_BOOLEAN)
            << "EqProof::addToProof: fully boolean constant assumption "
            << d_node << " is disallowed\n";
      }
    }
    // If conclusion is (= t true/false), we add a proof step
    //          t
    //  ---------------- TRUE/FALSE_INTRO
    //  (= t true/false)
    // according to the value of the Boolean constant
    if (d_node.getKind() == kind::EQUAL
        && ((d_node[0].getKind() == kind::CONST_BOOLEAN)
            != (d_node[1].getKind() == kind::CONST_BOOLEAN)))
    {
      Trace("eqproof-conv")
          << "EqProof::addToProof: add an intro step for " << d_node << "\n";
      // Index of constant in equality
      unsigned constIndex = d_node[0].getKind() == kind::CONST_BOOLEAN ? 0 : 1;
      // The premise for the intro rule is either t or (not t), according to the
      // Boolean constant.
      Node introPremise;
      PfRule introRule;
      if (d_node[constIndex].getConst<bool>())
      {
        introRule = PfRule::TRUE_INTRO;
        introPremise = d_node[1 - constIndex];
        // Track the new assumption. If it's an equality, also its symmetric
        assumptions.insert(introPremise);
        if (introPremise.getKind() == kind::EQUAL)
        {
          assumptions.insert(introPremise[1].eqNode(introPremise[0]));
        }
      }
      else
      {
        introRule = PfRule::FALSE_INTRO;
        introPremise = d_node[1 - constIndex].notNode();
        // Track the new assumption. If it's a disequality, also its symmetric
        assumptions.insert(introPremise);
        if (introPremise[0].getKind() == kind::EQUAL)
        {
          assumptions.insert(
              introPremise[0][1].eqNode(introPremise[0][0]).notNode());
        }
      }
      // The original assumption can be e.g. (= false (= t1 t2)) in which case
      // the necessary proof to be built is
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
      p->addStep(introConclusion, introRule, {introPremise}, {});
    }
    else
    {
      p->addStep(d_node, PfRule::ASSUME, {}, {d_node});
    }
    // If non-equality predicate, turn into one via TRUE/FALSE intro
    Node conclusion = d_node;
    if (d_node.getKind() != kind::EQUAL)
    {
      // Track original assumption
      assumptions.insert(d_node);
      PfRule intro;
      if (d_node.getKind() == kind::NOT)
      {
        intro = PfRule::FALSE_INTRO;
        conclusion =
            d_node[0].eqNode(NodeManager::currentNM()->mkConst<bool>(false));
      }
      else
      {
        intro = PfRule::TRUE_INTRO;
        conclusion =
            d_node.eqNode(NodeManager::currentNM()->mkConst<bool>(true));
      }
      Trace("eqproof-conv") << "EqProof::addToProof: adding " << intro
                            << " step for " << d_node << "\n";
      p->addStep(conclusion, intro, {d_node}, {});
    }
    // Keep track of assumptions to avoid cyclic proofs. Both the assumption and
    // its symmetric are added
    assumptions.insert(conclusion);
    assumptions.insert(conclusion[1].eqNode(conclusion[0]));
    Trace("eqproof-conv") << "EqProof::addToProof: tracking assumptions "
                          << conclusion << ", (= " << conclusion[1] << " "
                          << conclusion[0] << ")\n";
    visited[d_node] = conclusion;
    return conclusion;
  }
  // Refl and laborious congruence steps for (= (f t1 ... tn) (f t1 ... tn)),
  // which can be safely turned into reflexivity steps. These laborious
  // congruence steps are currently generated in the equality engine because of
  // the suboptimal handling of n-ary operators.
  if (d_id == MERGED_THROUGH_REFLEXIVITY
      || (d_node.getKind() == kind::EQUAL && d_node[0] == d_node[1]))
  {
    Node conclusion =
        d_node.getKind() == kind::EQUAL ? d_node : d_node.eqNode(d_node);
    p->addStep(conclusion, PfRule::REFL, {}, {conclusion[0]});
    visited[d_node] = conclusion;
    return conclusion;
  }
  // Equalities due to theory reasoning
  if (d_id == MERGED_THROUGH_CONSTANTS)
  {
    Assert(!d_node.isNull() && d_node.getKind() == kind::EQUAL
           && d_node[1].isConst())
        << ". Conclusion " << d_node << " from " << d_id
        << " was expected to be (= (f t1 ... tn) c)\n";
    Assert(!assumptions.count(d_node))
        << "Conclusion " << d_node << " from " << d_id << " is an assumption\n";
    // The step has the form
    //  [(= t1 c1)] ... [(= tn cn)]
    //  ------------------------
    //    (= (f t1 ... tn) c)
    // where premises equating ti to constants are present when they are not
    // already constants. Note that the premises may be in any order, e.g. with
    // the equality for the second term being justified in the first premise.
    // Moreover, they may be of the form (= ci ti).
    //
    // First recursively process premises, if any
    std::vector<Node> premises;
    for (unsigned i = 0; i < d_children.size(); ++i)
    {
      Trace("eqproof-conv")
          << "EqProof::addToProof: recurse on child " << i << "\n"
          << push;
      premises.push_back(d_children[i]->addToProof(p, visited, assumptions));
      Trace("eqproof-conv") << pop;
    }
    // After building the proper premises we could build a step like
    //  [(= t1 c1)] ...  [(= tn cn)]
    //  ---------------------------- MACRO_SR_PRED_INTRO
    //    (= (f t1 ... tn) c)
    // but note that since the substitution applied by MACRO_SR_PRED_INTRO is
    // *not* simultenous this could lead to issues if t_{i+1} occurred in some
    // t_{i}. So we build proofs as
    //
    //    [(= t1 c1)] ...  [(= tn cn)]
    //  ------------------------------- CONG  -------------- MACRO_SR_PRED_INTRO
    //  (= (f t1 ... tn) (f c1 ... cn))       (= (f c1 ... cn) c)
    // ---------------------------------------------------------- TRANS
    //                     (= (f t1 ... tn) c)
    std::vector<Node> subChildren, constChildren;
    for (unsigned i = 0, size = d_node[0].getNumChildren(); i < size; ++i)
    {
      Node term = d_node[0][i];
      // term already is a constant, add a REFL step
      if (term.isConst())
      {
        subChildren.push_back(term.eqNode(term));
        p->addStep(subChildren.back(), PfRule::REFL, {}, {term});
        constChildren.push_back(term);
        continue;
      }
      // Build the equality (= ti ci) as a premise, finding the respective ci is
      // the original premises
      Node constant;
      for (const Node& premise : premises)
      {
        Assert(premise.getKind() == kind::EQUAL);
        if (premise[0] == term)
        {
          Assert(premise[1].isConst());
          constant = premise[1];
          break;
        }
        if (premise[1] == term)
        {
          Assert(premise[0].isConst());
          constant = premise[0];
          break;
        }
      }
      Assert(!constant.isNull());
      subChildren.push_back(term.eqNode(constant));
      constChildren.push_back(constant);
    }
    // build constant application (f c1 ... cn) and equality (= (f c1 ... cn) c)
    Kind k = d_node[0].getKind();
    Node constApp = NodeManager::currentNM()->mkNode(k, constChildren);
    Node constEquality = constApp.eqNode(d_node[1]);
    Trace("eqproof-conv") << "EqProof::addToProof: adding "
                          << PfRule::MACRO_SR_PRED_INTRO << " step for "
                          << constApp << " = " << d_node[1] << "\n";
    p->addStep(constEquality, PfRule::MACRO_SR_PRED_INTRO, {}, {constEquality});
    // build congruence conclusion (= (f t1 ... tn) (f c1 ... cn))
    Node congConclusion = d_node[0].eqNode(constApp);
    Trace("eqproof-conv") << "EqProof::addToProof: adding  " << PfRule::CONG
                          << " step for " << congConclusion << " from "
                          << subChildren << "\n";
    p->addStep(congConclusion,
               PfRule::CONG,
               {subChildren},
               {ProofRuleChecker::mkKindNode(k)},
               true);
    Trace("eqproof-conv") << "EqProof::addToProof: adding  " << PfRule::TRANS
                          << " step for original conclusion " << d_node << "\n";
    std::vector<Node> transitivityChildren{congConclusion, constEquality};
    p->addStep(d_node, PfRule::TRANS, {transitivityChildren}, {});
    visited[d_node] = d_node;
    return d_node;
  }
  // Transtivity and disequality reasoning steps
  if (d_id == MERGED_THROUGH_TRANS)
  {
    Assert(d_node.getKind() == kind::EQUAL
           || (d_node.getKind() == kind::NOT
               && d_node[0].getKind() == kind::EQUAL))
        << "EqProof::addToProof: transitivity step conclusion " << d_node
        << " is not equality or negated equality\n";
    // If conclusion is (not (= t1 t2)) change it to (= (= t1 t2) false), which
    // is the correct conclusion of the equality reasoning step. A FALSE_ELIM
    // step to revert this is only necessary when this is the root. That step is
    // done in the non-recursive caller of this function.
    Node conclusion =
        d_node.getKind() != kind::NOT
            ? d_node
            : d_node[0].eqNode(NodeManager::currentNM()->mkConst<bool>(false));
    // If the conclusion is an assumption, its derivation was spurious, so it
    // can be discarded. Moreover, reconstructing the step may lead to cyclic
    // proofs, so we *must* cut here.
    if (assumptions.count(conclusion))
    {
      visited[d_node] = conclusion;
      return conclusion;
    }
    // Process premises recursively
    std::vector<Node> children;
    for (unsigned i = 0, size = d_children.size(); i < size; ++i)
    {
      // If one of the steps is a "fake congruence" one, marked by a null
      // conclusion, it must deleted. Its premises are moved down to premises of
      // the transitivity step.
      EqProof* childProof = d_children[i].get();
      if (childProof->d_id == MERGED_THROUGH_CONGRUENCE
          && childProof->d_node.isNull())
      {
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
          children.push_back(
              childProof->d_children[j]->addToProof(p, visited, assumptions));
          Trace("eqproof-conv") << pop;
        }
        Trace("eqproof-conv") << pop;
        continue;
      }
      Trace("eqproof-conv")
          << "EqProof::addToProof: recurse on child " << i << "\n"
          << push;
      children.push_back(childProof->addToProof(p, visited, assumptions));
      Trace("eqproof-conv") << pop;
    }
    // Eliminate spurious premises. Reasoning below assumes no refl steps.
    cleanReflPremises(children);
    // If any premise is of the form (= (t1 t2) false), then the transitivity
    // step may be coarse-grained and needs to be expanded. If the expansion
    // happens it also finalizes the proof of conclusion.
    if (!expandTransitivityForDisequalities(
            conclusion, children, p, assumptions))
    {
      Assert(!children.empty());
      // similarly, if a disequality is concluded because of theory reasoning,
      // the step is coarse-grained and needs to be expanded, in which case the
      // proof is finalized in the call
      if (!expandTransitivityForTheoryDisequalities(conclusion, children, p))
      {
        Trace("eqproof-conv")
            << "EqProof::addToProof: build chain for transitivity premises"
            << children << " to conclude " << conclusion << "\n";
        // Build ordered transitivity chain from children to derive the
        // conclusion
        buildTransitivityChain(conclusion, children);
        Assert(
            children.size() > 1
            || (!children.empty()
                && (children[0] == conclusion
                    || children[0][1].eqNode(children[0][0]) == conclusion)));
        // Only add transitivity step if there is more than one premise in the
        // chain. Otherwise the premise will be the conclusion itself and it'll
        // already have had a step added to it when the premises were
        // recursively processed.
        if (children.size() > 1)
        {
          p->addStep(conclusion, PfRule::TRANS, children, {}, true);
        }
      }
    }
    Assert(p->hasStep(conclusion));
    visited[d_node] = conclusion;
    return conclusion;
  }
  Assert(d_id == MERGED_THROUGH_CONGRUENCE);
  // The processing below is mainly dedicated to flattening congruence steps
  // (since EqProof assumes currying) and to prossibly reconstructing the
  // conclusion in case it involves n-ary steps.
  Assert(d_node.getKind() == kind::EQUAL)
      << "EqProof::addToProof: conclusion " << d_node << " is not equality\n";
  // The given conclusion is taken as ground truth. If the premises do not
  // align, for example with (= (f t1) (f t2)) but a premise being (= t2 t1), we
  // use (= t1 t2) as a premise and rely on a symmetry step to justify it.
  unsigned arity = d_node[0].getNumChildren();
  Kind k = d_node[0].getKind();
  bool isNary = ExprManager::isNAryKind(k);

  // N-ary operators are fun. The following proof is a valid EqProof
  //
  //   (= (f t1 t2 t3) (f t6 t5)) (= (f t6 t5) (f t5 t6))
  //   -------------------------------------------------- TRANS
  //             (= (f t1 t2 t3) (f t5 t6))                      (= t4 t7)
  //          ------------------------------------------------------------ CONG
  //          (= (f t1 t2 t3 t4) (f t5 t6 t7))
  //
  // We modify the above proof to conclude
  //
  //   (= (f (f t1 t2 t3) t4) (f (f t5 t6) t7))
  //
  // which is a valid congruence conclusion (applications of f with the same
  // arity). For the processing below to be//  performed correctly we update
  // arity to be maximal one among the two applications (4 in the above
  // example).
  if (d_node[0].getNumChildren() != d_node[1].getNumChildren())
  {
    Assert(isNary);
    arity =
        d_node[1].getNumChildren() < arity ? arity : d_node[1].getNumChildren();
    Trace("eqproof-conv")
        << "EqProof::addToProof: Mismatching arities in cong conclusion "
        << d_node << ". Use tentative arity " << arity << "\n";
  }
  // For a congruence proof of (= (f a0 ... an-1) (f b0 ... bn-1)), build a
  // transitivity matrix where each row contains a transitivity chain justifying
  // (= ai bi)
  std::vector<std::vector<Node>> transitivityChildren;
  for (unsigned i = 0; i < arity; ++i)
  {
    transitivityChildren.push_back(std::vector<Node>());
  }
  reduceNestedCongruence(
      arity - 1, d_node, transitivityChildren, p, visited, assumptions, isNary);
  // Congruences over n-ary operators may require changing the conclusion (as in
  // the above example). This is handled in a general manner below according to
  // whether the transitivity matrix computed by reduceNestedCongruence contains
  // empty rows
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
    // Given two n-ary applications f1:(f a0 ... an-1), f2:(f b0 ... bm-1), of
    // arities n and m, arity = max(n,m), the number emptyRows establishes the
    // sizes of the prefixes of f1 of f2 that have been equated via a
    // transitivity step. The prefixes necessarily have different sizes. The
    // suffixes have the same sizes. The new conclusion will be of the form
    //     (= (f (f a0 ... ak1) ... an-1) (f (f b0 ... bk2) ... bm-1))
    // where
    //  k1 = emptyRows + 1 - (arity - n)
    //  k2 = emptyRows + 1 - (arity - m)
    //  k1 != k2
    //  n - k1 == m - k2
    // Note that by construction the equality between the first emptyRows + 1
    // arguments of each application is justified by the transitivity step in
    // the row emptyRows +1 in the matrix.
    if (emptyRows > 0)
    {
      Trace("eqproof-conv")
          << "EqProof::addToProof: Found " << emptyRows
          << " empty rows. Rebuild conclusion " << d_node << "\n";
      // New transitivity matrix is as before except that the empty rows in the
      // beginning are eliminated, as the new arity is the maximal arity among
      // the applications minus the number of empty rows.
      std::vector<std::vector<Node>> newTransitivityChildren{
          transitivityChildren.begin() + emptyRows, transitivityChildren.end()};
      transitivityChildren.clear();
      transitivityChildren.insert(transitivityChildren.begin(),
                                  newTransitivityChildren.begin(),
                                  newTransitivityChildren.end());
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
  // Proccess transitivity matrix to (possibly) generate transitivity steps for
  // congruence premises (= ai bi)
  std::vector<Node> children(arity);
  for (unsigned i = 0; i < arity; ++i)
  {
    Node transConclusion = conclusion[0][i].eqNode(conclusion[1][i]);
    children[i] = transConclusion;
    Assert(!transitivityChildren[i].empty())
        << "EqProof::addToProof: did not add any justification for " << i
        << "-th arg of congruence " << conclusion << "\n";
    // If the transitivity conclusion is a reflexivity step, just add it. Note
    // that this can happen with with transitivityChildren containing several
    // equalities in the case of (= ai bi) being the same n-ary application that
    // was justified by a congruence step, which can happen in the current
    // equality engine
    if (transConclusion[0] == transConclusion[1])
    {
      p->addStep(transConclusion, PfRule::REFL, {}, {transConclusion[0]});
      continue;
    }
    // Remove spurious refl steps from the premises for (= ai bi)
    cleanReflPremises(transitivityChildren[i]);
    Assert(transitivityChildren[i].size() > 1 || transitivityChildren[i].empty()
           || CDProof::isSame(transitivityChildren[i][0], transConclusion))
        << "EqProof::addToProof: premises " << transitivityChildren[i] << "for "
        << i << "-th cong premise " << transConclusion << " don't justify it\n";
    unsigned sizeTrans = transitivityChildren[i].size();
    // If no transitivity premise left or if (= ai bi) is an assumption (which
    // might lead to a cycle with a transtivity step), nothing else to do.
    if (sizeTrans == 0 || assumptions.count(transConclusion) > 0)
    {
      continue;
    }
    // If the transitivity conclusion, or its symmetric, occurs in the
    // transitivity premises, nothing to do, as it is already justified and
    // doing so again would lead to a cycle.
    bool occurs = false;
    for (unsigned j = 0; j < sizeTrans && !occurs; ++j)
    {
      if (CDProof::isSame(transitivityChildren[i][j], transConclusion))
      {
        occurs = true;
      }
    }
    if (!occurs)
    {
      // Build transitivity step
      buildTransitivityChain(transConclusion, transitivityChildren[i]);
      Trace("eqproof-conv")
          << "EqProof::addToProof: adding trans step for cong premise "
          << transConclusion << " with children " << transitivityChildren[i]
          << "\n";
      p->addStep(
          transConclusion, PfRule::TRANS, transitivityChildren[i], {}, true);
    }
  }
  // Get node of the function operator over which congruence is being applied.
  std::vector<Node> args;
  args.push_back(ProofRuleChecker::mkKindNode(k));
  if (kind::metaKindOf(k) == kind::metakind::PARAMETERIZED)
  {
    args.push_back(conclusion[0].getOperator());
  }
  // Add congruence step
  Trace("eqproof-conv") << "EqProof::addToProof: build cong step of "
                        << conclusion << " with op " << args[0]
                        << " and children " << children << "\n";
  p->addStep(conclusion, PfRule::CONG, children, args, true);
  // If the conclusion of the congruence step changed due to the n-ary handling,
  // we obtained for example (= (f (f t1 t2 t3) t4) (f (f t5 t6) t7)), which is
  // flattened into the original conclusion (= (f t1 t2 t3 t4) (f t5 t6 t7)) via
  // rewriting
  if (conclusion != d_node)
  {
    Trace("eqproof-conv") << "EqProof::addToProof: add "
                          << PfRule::MACRO_SR_PRED_TRANSFORM
                          << " step to flatten rebuilt conclusion "
                          << conclusion << "into " << d_node << "\n";
    p->addStep(
        d_node, PfRule::MACRO_SR_PRED_TRANSFORM, {conclusion}, {d_node}, true);
  }
  visited[d_node] = d_node;
  return d_node;
}

}  // namespace eq
}  // Namespace theory
}  // Namespace CVC4
