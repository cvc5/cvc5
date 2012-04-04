/*********************                                                        */
/*! \file theory_bv.cpp
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/bv/theory_bv.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/valuation.h"

#include "theory/bv/bv_sat.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;
using namespace CVC4::context;

using namespace std;
using namespace CVC4::theory::bv::utils;

TheoryBV::TheoryBV(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation)
  : Theory(THEORY_BV, c, u, out, valuation),
    d_context(c),
    d_assertions(c),
    d_bitblaster(new Bitblaster(c) ),
    d_statistics(),
    d_alreadyPropagatedSet(c)
   {
    d_true = utils::mkTrue();
  }
TheoryBV::~TheoryBV() {
  delete d_bitblaster; 
}
TheoryBV::Statistics::Statistics():
  d_avgConflictSize("theory::bv::AvgBVConflictSize"),
  d_solveSubstitutions("theory::bv::NumberOfSolveSubstitutions", 0),
  d_solveTimer("theory::bv::solveTimer")
{
  StatisticsRegistry::registerStat(&d_avgConflictSize);
  StatisticsRegistry::registerStat(&d_solveSubstitutions);
  StatisticsRegistry::registerStat(&d_solveTimer); 
}

TheoryBV::Statistics::~Statistics() {
  StatisticsRegistry::unregisterStat(&d_avgConflictSize);
  StatisticsRegistry::unregisterStat(&d_solveSubstitutions);
  StatisticsRegistry::unregisterStat(&d_solveTimer); 
}

void TheoryBV::preRegisterTerm(TNode node) {
  BVDebug("bitvector-preregister") << "TheoryBV::preRegister(" << node << ")" << std::endl;
  if (node.getKind() == kind::EQUAL ||
      node.getKind() == kind::BITVECTOR_ULT ||
      node.getKind() == kind::BITVECTOR_ULE ||
      node.getKind() == kind::BITVECTOR_SLT ||
      node.getKind() == kind::BITVECTOR_SLE) {
    d_bitblaster->bitblast(node);
    d_bitblaster->addAtom(node); 
  }
}

void TheoryBV::check(Effort e) {
  if (e == EFFORT_STANDARD) {
    BVDebug("bitvector") << "TheoryBV::check " << e << "\n"; 
    BVDebug("bitvector")<< "TheoryBV::check(" << e << ")" << std::endl;
    while (!done()) {
      TNode assertion = get();
      // make sure we do not assert things we propagated 
      if (!hasBeenPropagated(assertion)) {
        BVDebug("bitvector-assertions") << "TheoryBV::check assertion " << assertion << "\n"; 
        bool ok = d_bitblaster->assertToSat(assertion, true);
        if (!ok) {
          std::vector<TNode> conflictAtoms;
          d_bitblaster->getConflict(conflictAtoms);
          d_statistics.d_avgConflictSize.addEntry(conflictAtoms.size());
          Node conflict = mkConjunction(conflictAtoms);
          d_out->conflict(conflict);
          BVDebug("bitvector") << "TheoryBV::check returns conflict: " <<conflict <<" \n ";
          return;
        }
      }
    }
  }

  if (e == EFFORT_FULL) {
    BVDebug("bitvector") << "TheoryBV::check " << e << "\n";
    // in standard effort we only do boolean constraint propagation 
    bool ok = d_bitblaster->solve(false);
    if (!ok) {
      std::vector<TNode> conflictAtoms;
      d_bitblaster->getConflict(conflictAtoms);
      d_statistics.d_avgConflictSize.addEntry(conflictAtoms.size());
      Node conflict = mkConjunction(conflictAtoms);
      d_out->conflict(conflict);
      BVDebug("bitvector") << "TheoryBV::check returns conflict: " <<conflict <<" \n ";
      return; 
    }
  }

}


Node TheoryBV::getValue(TNode n) {
  //NodeManager* nodeManager = NodeManager::currentNM();

  switch(n.getKind()) {

  case kind::VARIABLE:
    Unhandled(kind::VARIABLE);

  case kind::EQUAL: // 2 args
    Unhandled(kind::VARIABLE);

  default:
    Unhandled(n.getKind());
  }
}

bool TheoryBV::hasBeenPropagated(TNode node) {
  return d_alreadyPropagatedSet.count(node); 
}

void TheoryBV::propagate(Effort e) {
  BVDebug("bitvector") << "TheoryBV::propagate() \n";

  // get new propagations from the sat solver
  std::vector<TNode> propagations; 
  d_bitblaster->getPropagations(propagations);

  // propagate the facts on the propagation queue
  for (unsigned i = 0; i < propagations.size(); ++ i) {
    TNode node = propagations[i];
    BVDebug("bitvector") << "TheoryBV::propagate    " << node <<" \n";
    if (d_valuation.getSatValue(node) == Node::null()) {
      vector<Node> explanation;
      d_bitblaster->explainPropagation(node, explanation);
      if (explanation.size() == 0) {
        d_out->lemma(node);
      } else {
        NodeBuilder<> nb(kind::OR);
        nb << node;
        for (unsigned i = 0; i < explanation.size(); ++ i) {
          nb << explanation[i].notNode();
        }
        Node lemma = nb;
        d_out->lemma(lemma);
      }
      d_alreadyPropagatedSet.insert(node);
    }
  }

}

Node TheoryBV::explain(TNode n) {
  BVDebug("bitvector") << "TheoryBV::explain node " <<  n <<"\n";
  std::vector<Node> explanation;
  d_bitblaster->explainPropagation(n, explanation);
  Node exp;

  if (explanation.size() == 0) {
    return utils::mkTrue(); 
  }
  
  exp = utils::mkAnd(explanation);
  
  BVDebug("bitvector") << "TheoryBV::explain with " <<  exp <<"\n";
  return exp;
}

Theory::PPAssertStatus TheoryBV::ppAssert(TNode in, SubstitutionMap& outSubstitutions) {
  switch(in.getKind()) {
  case kind::EQUAL:
    
    if (in[0].getMetaKind() == kind::metakind::VARIABLE && !in[1].hasSubterm(in[0])) {
      ++(d_statistics.d_solveSubstitutions); 
      outSubstitutions.addSubstitution(in[0], in[1]);
      return PP_ASSERT_STATUS_SOLVED;
    }
    if (in[1].getMetaKind() == kind::metakind::VARIABLE && !in[0].hasSubterm(in[1])) {
      ++(d_statistics.d_solveSubstitutions); 
      outSubstitutions.addSubstitution(in[1], in[0]);
      return PP_ASSERT_STATUS_SOLVED;
    }
    // to do constant propagations

    break;
  case kind::NOT:
    break;
  default:
    // TODO other predicates
    break;
  }
  return PP_ASSERT_STATUS_UNSOLVED;
}
