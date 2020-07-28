/*********************                                                        */
/*! \file lrat_proof_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of the LRAT proof class
 **
 ** In particular, tests LRAT LFSC output.
 **/

#include <cxxtest/TestSuite.h>

#include <iostream>

#include "proof/lrat/lrat_proof.h"
#include "prop/sat_solver_types.h"
#include "utils.h"

using namespace CVC4;
using namespace CVC4::proof::lrat;
using namespace CVC4::prop;

class LratProofBlack : public CxxTest::TestSuite
{
 public:
  void setUp() override {}
  void tearDown() override {}

  void testOutputAsLfsc();
};

void LratProofBlack::testOutputAsLfsc()
{
  std::vector<std::unique_ptr<LratInstruction>> instructions;

  // 6   d 1 2
  std::vector<ClauseIdx> clausesToDelete{1, 2};
  std::unique_ptr<LratDeletion> deletion = std::unique_ptr<LratDeletion>(
      new LratDeletion(6, std::move(clausesToDelete)));
  instructions.push_back(std::move(deletion));

  // 7   1 2 0  5 2 0
  std::vector<SatLiteral> firstAddedClause{SatLiteral(1, false),
                                           SatLiteral(2, false)};
  LratUPTrace firstTrace{5, 2};
  std::vector<std::pair<ClauseIdx, LratUPTrace>> firstHints;
  std::unique_ptr<LratAddition> add1 =
      std::unique_ptr<LratAddition>(new LratAddition(
          7, std::move(firstAddedClause), std::move(firstTrace), firstHints));
  instructions.push_back(std::move(add1));

  // 8   2 0  -1 3  -5 2 0
  std::vector<SatLiteral> secondAddedClause{SatLiteral(2, false)};
  LratUPTrace secondTrace;
  std::vector<std::pair<ClauseIdx, LratUPTrace>> secondHints;
  LratUPTrace secondHints0Trace{3};
  secondHints.emplace_back(1, secondHints0Trace);
  LratUPTrace secondHints1Trace{2};
  secondHints.emplace_back(5, secondHints1Trace);
  std::unique_ptr<LratAddition> add2 = std::unique_ptr<LratAddition>(
      new LratAddition(8,
                       std::move(secondAddedClause),
                       std::move(secondTrace),
                       secondHints));
  instructions.push_back(std::move(add2));

  LratProof proof(std::move(instructions));

  std::ostringstream lfsc;
  proof.outputAsLfsc(lfsc);

  // 6   d 1 2
  // 7   1 2 0  5 2 0
  // 8   2 0  -1 3  -5 2 0
  std::string expectedLfsc =
      "(LRATProofd (CIListc 1 (CIListc 2 CIListn)) "
      "(LRATProofa 7 "
      "  (clc (pos bb.v1) (clc (pos bb.v2) cln))"
      "  (Tracec 5 (Tracec 2 Tracen))"
      "  RATHintsn "
      "(LRATProofa 8 "
      "  (clc (pos bb.v2) cln)"
      "  Tracen "
      "  (RATHintsc 1 (Tracec 3 Tracen)"
      "    (RATHintsc 5 (Tracec 2 Tracen)"
      "    RATHintsn)) "
      "LRATProofn)))";

  TS_ASSERT_EQUALS(filterWhitespace(lfsc.str()),
                   filterWhitespace(expectedLfsc));
}
