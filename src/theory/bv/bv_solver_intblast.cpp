/*********************                                                        */
/*! \file bv_solver_intblast.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Simple int-blast solver
 **
 ** Int-blast solver that uses IntBlaster to translate BV atoms to Integers.
 **/

#include "theory/bv/bv_solver_intblast.h"

#include "theory/bv/theory_bv.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/theory_model.h"

namespace CVC4 {
namespace theory {
namespace bv {

/* -------------------------------------------------------------------------- */

BVSolverIntblast::BVSolverIntblast(TheoryState* s,
                                   TheoryInferenceManager& inferMgr,
                                   ProofNodeManager* pnm)
    : BVSolver(*s, inferMgr),
      d_intblaster(new IntBlaster(
          s->getUserContext(), options::SolveBVAsIntMode::IAND, 1, true)),
      d_epg(pnm ? new EagerProofGenerator(pnm, s->getUserContext(), "")
                : nullptr)
{
}

void BVSolverIntblast::addIBLemma(TNode fact)
{
  NodeManager* nm = NodeManager::currentNM();

  std::vector<Node> lemmas;
  Node atom_ib = d_intblaster->intBlast(fact, lemmas, d_skolems);
  Node lemma = nm->mkNode(kind::EQUAL, fact, atom_ib);
  d_inferManager.lemma(lemma);
  if (!lemmas.empty())
  {
    d_inferManager.lemma(nm->mkAnd(lemmas));
  }
}

bool BVSolverIntblast::preNotifyFact(
    TNode atom, bool pol, TNode fact, bool isPrereg, bool isInternal)
{
  if (fact.getKind() == kind::NOT)
  {
    fact = fact[0];
  }
  addIBLemma(fact);
  return true;
}

bool BVSolverIntblast::collectModelValues(TheoryModel* m,
                                          const std::set<Node>& termSet)
{
  for (const auto& term : termSet)
  {
    auto it = d_skolems.find(term);
    if (it == d_skolems.end())
    {
      continue;
    }
    if (!m->assertEquality(term, it->second, true))
    {
      return false;
    }
  }
  return true;
}

}  // namespace bv
}  // namespace theory
}  // namespace CVC4
