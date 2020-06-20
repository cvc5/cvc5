/*********************                                                        */
/*! \file er_proof_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of the ER proof class
 **
 ** In particular, tests TRACECHECK parsing and ER LFSC output.
 **/

#include <cxxtest/TestSuite.h>

#include <algorithm>
#include <cctype>
#include <iostream>
#include <iterator>
#include <string>
#include <unordered_map>
#include <vector>

#include "base/configuration_private.h"
#include "proof/clause_id.h"
#include "proof/er/er_proof.h"
#include "prop/sat_solver_types.h"
#include "utils.h"

#if IS_LFSC_BUILD
#include "lfscc.h"

namespace CVC4 {
namespace proof {
extern const char* const plf_signatures;
}  // namespace proof
}  // namespace CVC4
#endif


using namespace CVC4;
using namespace CVC4::proof::er;
using namespace CVC4::prop;

class ErProofBlack : public CxxTest::TestSuite
{
 public:
  void setUp() override {}
  void tearDown() override {}

  void testTraceCheckParse1Line();
  void testTraceCheckParse5Lines();
  void testErTraceCheckParse();
  void testErTraceCheckOutput();
  void testErTraceCheckOutputMedium();
};

/**
 * @brief Add a new clause to the clause store and list of used clauses
 *
 * @param clauses the clause store
 * @param usedIds the used clauses
 * @param id the id of the new clause
 * @param clause the clause itself
 */
void addClause(std::unordered_map<ClauseId, SatClause>& clauses,
               std::vector<ClauseId>& usedIds,
               ClauseId id,
               SatClause&& clause)
{
  clauses.emplace(id, std::move(clause));
  usedIds.push_back(id);
}

void ErProofBlack::testTraceCheckParse1Line()
{
  std::string tracecheckText = "1 -2 3 0 4 2 0\n";
  std::istringstream stream(tracecheckText);
  TraceCheckProof pf = TraceCheckProof::fromText(stream);
  TS_ASSERT_EQUALS(pf.d_lines.size(), 1);

  TS_ASSERT_EQUALS(pf.d_lines[0].d_idx, 1);
  TS_ASSERT_EQUALS(pf.d_lines[0].d_clause.size(), 2);
  TS_ASSERT_EQUALS(pf.d_lines[0].d_clause[0], SatLiteral(1, true));
  TS_ASSERT_EQUALS(pf.d_lines[0].d_clause[1], SatLiteral(2, false));
  TS_ASSERT_EQUALS(pf.d_lines[0].d_chain.size(), 2);
  TS_ASSERT_EQUALS(pf.d_lines[0].d_chain[0], 4);
  TS_ASSERT_EQUALS(pf.d_lines[0].d_chain[1], 2);
}

void ErProofBlack::testTraceCheckParse5Lines()
{
  std::string tracecheckText =
      "1 1 -2 3 0 0\n"
      "2 -1 0 0\n"
      "3 2 0 0\n"
      "4 -3 0 0\n"
      "5 0 1 2 4 3 0\n";
  std::istringstream stream(tracecheckText);
  TraceCheckProof pf = TraceCheckProof::fromText(stream);
  TS_ASSERT_EQUALS(pf.d_lines.size(), 5);

  TS_ASSERT_EQUALS(pf.d_lines[0].d_idx, 1);
  TS_ASSERT_EQUALS(pf.d_lines[4].d_idx, 5);

  TS_ASSERT_EQUALS(pf.d_lines[0].d_clause.size(), 3);
  TS_ASSERT_EQUALS(pf.d_lines[0].d_clause[0], SatLiteral(0, false));
  TS_ASSERT_EQUALS(pf.d_lines[0].d_clause[1], SatLiteral(1, true));
  TS_ASSERT_EQUALS(pf.d_lines[0].d_clause[2], SatLiteral(2, false));
  TS_ASSERT_EQUALS(pf.d_lines[0].d_chain.size(), 0);

  TS_ASSERT_EQUALS(pf.d_lines[4].d_chain.size(), 4);
  TS_ASSERT_EQUALS(pf.d_lines[4].d_chain[0], 1);
  TS_ASSERT_EQUALS(pf.d_lines[4].d_chain[1], 2);
  TS_ASSERT_EQUALS(pf.d_lines[4].d_chain[2], 4);
  TS_ASSERT_EQUALS(pf.d_lines[4].d_chain[3], 3);
  TS_ASSERT_EQUALS(pf.d_lines[4].d_clause.size(), 0);
}

void ErProofBlack::testErTraceCheckParse()
{
  std::string tracecheckText =
      "1  1  2 -3 0 0\n"
      "2 -1 -2  3 0 0\n"
      "3  2  3 -4 0 0\n"
      "4 -2 -3  4 0 0\n"
      "5 -1 -3 -4 0 0\n"
      "6  1  3  4 0 0\n"
      "7 -1  2  4 0 0\n"
      "8  1 -2 -4 0 0\n"
      "9 5 0 0\n"
      "10 5 1 0 0\n"
      "11 4 5 2 0 10 7 0\n"
      "12 -4 5 -3 0 10 5 0\n"
      "13 3 5 -2 0 10 2 0\n"
      "14 -2 -4 0 2 5 8 0\n"
      "15 4 3 0 7 2 6 0\n"
      "16 2 -3 0 7 5 1 0\n"
      "17 2 0 3 15 16 0\n"
      "18 0 4 15 14 17 0\n";
  std::istringstream stream(tracecheckText);
  TraceCheckProof tc = TraceCheckProof::fromText(stream);

  std::unordered_map<ClauseId, SatClause> clauses;
  std::vector<ClauseId> usedIds;
  addClause(
      clauses,
      usedIds,
      1,
      std::vector<SatLiteral>{
          SatLiteral(0, false), SatLiteral(1, false), SatLiteral(2, true)});
  addClause(
      clauses,
      usedIds,
      2,
      std::vector<SatLiteral>{
          SatLiteral(0, true), SatLiteral(1, true), SatLiteral(2, false)});
  addClause(
      clauses,
      usedIds,
      3,
      std::vector<SatLiteral>{
          SatLiteral(1, false), SatLiteral(2, false), SatLiteral(3, true)});
  addClause(
      clauses,
      usedIds,
      4,
      std::vector<SatLiteral>{
          SatLiteral(1, true), SatLiteral(2, true), SatLiteral(3, false)});
  addClause(clauses,
            usedIds,
            5,
            std::vector<SatLiteral>{
                SatLiteral(0, true), SatLiteral(2, true), SatLiteral(3, true)});
  addClause(
      clauses,
      usedIds,
      6,
      std::vector<SatLiteral>{
          SatLiteral(0, false), SatLiteral(2, false), SatLiteral(3, false)});
  addClause(
      clauses,
      usedIds,
      7,
      std::vector<SatLiteral>{
          SatLiteral(0, true), SatLiteral(1, false), SatLiteral(3, false)});
  addClause(
      clauses,
      usedIds,
      8,
      std::vector<SatLiteral>{
          SatLiteral(0, false), SatLiteral(1, true), SatLiteral(3, true)});
  ErProof pf(clauses, usedIds, std::move(tc));

  TS_ASSERT_EQUALS(pf.getInputClauseIds()[0], 1);
  TS_ASSERT_EQUALS(pf.getInputClauseIds()[7], 8);

  TS_ASSERT_EQUALS(pf.getDefinitions().size(), 1)
  TS_ASSERT_EQUALS(pf.getDefinitions()[0].d_newVariable, SatVariable(4));
  TS_ASSERT_EQUALS(pf.getDefinitions()[0].d_oldLiteral, SatLiteral(0, true));
  TS_ASSERT_EQUALS(pf.getDefinitions()[0].d_otherLiterals.size(), 0);
  TS_ASSERT_EQUALS(pf.getTraceCheckProof().d_lines.size(), 18);

  TS_ASSERT_EQUALS(pf.getTraceCheckProof().d_lines[0].d_idx, 1);
  TS_ASSERT_EQUALS(pf.getTraceCheckProof().d_lines[16].d_idx, 17);

  TS_ASSERT_EQUALS(pf.getTraceCheckProof().d_lines[0].d_clause.size(), 3);
  TS_ASSERT_EQUALS(pf.getTraceCheckProof().d_lines[0].d_clause[0],
                   SatLiteral(0, false));
  TS_ASSERT_EQUALS(pf.getTraceCheckProof().d_lines[0].d_clause[1],
                   SatLiteral(1, false));
  TS_ASSERT_EQUALS(pf.getTraceCheckProof().d_lines[0].d_clause[2],
                   SatLiteral(2, true));
  TS_ASSERT_EQUALS(pf.getTraceCheckProof().d_lines[0].d_chain.size(), 0);

  TS_ASSERT_EQUALS(pf.getTraceCheckProof().d_lines[16].d_clause.size(), 1);
  TS_ASSERT_EQUALS(pf.getTraceCheckProof().d_lines[16].d_clause[0],
                   SatLiteral(1, false));
  TS_ASSERT_EQUALS(pf.getTraceCheckProof().d_lines[16].d_chain.size(), 3);
  TS_ASSERT_EQUALS(pf.getTraceCheckProof().d_lines[16].d_chain[0], 3);
  TS_ASSERT_EQUALS(pf.getTraceCheckProof().d_lines[16].d_chain[1], 15);
  TS_ASSERT_EQUALS(pf.getTraceCheckProof().d_lines[16].d_chain[2], 16);
}

void ErProofBlack::testErTraceCheckOutput()
{
  std::string tracecheckText =
      "1  1  2 -3 0 0\n"
      "2 -1 -2  3 0 0\n"
      "3  2  3 -4 0 0\n"
      "4 -2 -3  4 0 0\n"
      "5 -1 -3 -4 0 0\n"
      "6  1  3  4 0 0\n"
      "7 -1  2  4 0 0\n"
      "8  1 -2 -4 0 0\n"
      "9 5 0 0\n"
      "10 5 1 0 0\n"
      "11 4 5 2 0 10 7 0\n"
      "12 -4 5 -3 0 10 5 0\n"
      "13 3 5 -2 0 10 2 0\n"
      "14 -2 -4 0 2 5 8 0\n"
      "15 4 3 0 7 2 6 0\n"
      "16 2 -3 0 7 5 1 0\n"
      "17 2 0 3 15 16 0\n"
      "18 0 4 15 14 17 0\n";
  std::istringstream stream(tracecheckText);
  TraceCheckProof tc = TraceCheckProof::fromText(stream);

  std::unordered_map<ClauseId, SatClause> clauses;
  std::vector<ClauseId> usedIds;
  addClause(
      clauses,
      usedIds,
      1,
      std::vector<SatLiteral>{
          SatLiteral(0, false), SatLiteral(1, false), SatLiteral(2, true)});
  addClause(
      clauses,
      usedIds,
      2,
      std::vector<SatLiteral>{
          SatLiteral(0, true), SatLiteral(1, true), SatLiteral(2, false)});
  addClause(
      clauses,
      usedIds,
      3,
      std::vector<SatLiteral>{
          SatLiteral(1, false), SatLiteral(2, false), SatLiteral(3, true)});
  addClause(
      clauses,
      usedIds,
      4,
      std::vector<SatLiteral>{
          SatLiteral(1, true), SatLiteral(2, true), SatLiteral(3, false)});
  addClause(clauses,
            usedIds,
            5,
            std::vector<SatLiteral>{
                SatLiteral(0, true), SatLiteral(2, true), SatLiteral(3, true)});
  addClause(
      clauses,
      usedIds,
      6,
      std::vector<SatLiteral>{
          SatLiteral(0, false), SatLiteral(2, false), SatLiteral(3, false)});
  addClause(
      clauses,
      usedIds,
      7,
      std::vector<SatLiteral>{
          SatLiteral(0, true), SatLiteral(1, false), SatLiteral(3, false)});
  addClause(
      clauses,
      usedIds,
      8,
      std::vector<SatLiteral>{
          SatLiteral(0, false), SatLiteral(1, true), SatLiteral(3, true)});
  ErProof pf(clauses, usedIds, std::move(tc));

  std::ostringstream lfsc;
  pf.outputAsLfsc(lfsc);

  std::string out = R"EOF(
    (decl_definition
      (neg bb.v0)
      cln
      (\ er.v4
      (\ er.def4
        (clausify_definition _ _ _ er.def4 _
          (\ er.c9
          (\ er.c10
          (\ er.cnf4
            (satlem_simplify _ _ _
              (R _ _ er.c10 bb.pb7 bb.v0) (\ er.c11
            (satlem_simplify _ _ _
              (R _ _ er.c10 bb.pb5 bb.v0) (\ er.c12
            (satlem_simplify _ _ _
              (R _ _ er.c10 bb.pb2 bb.v0) (\ er.c13
            (satlem_simplify _ _ _
              (Q _ _ (R _ _ bb.pb2 bb.pb5 bb.v2) bb.pb8 bb.v0) (\ er.c14
            (satlem_simplify _ _ _
              (Q _ _ (R _ _ bb.pb7 bb.pb2 bb.v1) bb.pb6 bb.v0) (\ er.c15
            (satlem_simplify _ _ _
              (Q _ _ (R _ _ bb.pb7 bb.pb5 bb.v3) bb.pb1 bb.v0) (\ er.c16
            (satlem_simplify _ _ _
              (R _ _ (Q _ _ bb.pb3 er.c15 bb.v3) er.c16 bb.v2) (\ er.c17
            (satlem_simplify _ _ _
              (Q _ _ (R _ _ (Q _ _ bb.pb4 er.c15 bb.v2) er.c14 bb.v3)
                  er.c17 bb.v1) (\ er.c18
              er.c18 ; (holds cln)
            ))))))))))))))))
          )))
        )
      ))
    )
    )EOF";

  TS_ASSERT_EQUALS(filterWhitespace(lfsc.str()), filterWhitespace(out));
}

/**
 * This proof has been specially constructed to stress-test the proof
 * machinery, while still being short. It's a bit meandering...
 */
void ErProofBlack::testErTraceCheckOutputMedium()
{
  std::string tracecheckText =
      "1  1  2 -3 0 0\n"
      "2 -1 -2  3 0 0\n"
      "3  2  3 -4 0 0\n"
      "4 -2 -3  4 0 0\n"
      "5 -1 -3 -4 0 0\n"
      "6  1  3  4 0 0\n"
      "7 -1  2  4 0 0\n"
      "8  1 -2 -4 0 0\n"

      "9  5  2  4 0 0\n"  // Definition with 2 other variables
      "10 5  1  0 0\n"
      "11 2 -5 -1 0 0\n"
      "12 4 -5 -1 0 0\n"

      "13 6  0 0\n"  // Definition with no other variables
      "14 6  -3  0 0\n"

      "15 -3 4 0 11 1 10 7 4 0\n"  // Chain w/ both def. and input clauses

      "16 -2 -4 0 2 5 8 0\n"  // The useful bit of the proof
      "17 4 3 0 7 2 6 0\n"
      "18 2 -3 0 7 5 1 0\n"
      "19 2 0 3 17 18 0\n"
      "20 0 4 17 16 19 0\n";

  std::istringstream stream(tracecheckText);
  TraceCheckProof tc = TraceCheckProof::fromText(stream);

  std::unordered_map<ClauseId, SatClause> clauses;
  std::vector<ClauseId> usedIds;
  addClause(
      clauses,
      usedIds,
      1,
      std::vector<SatLiteral>{
          SatLiteral(0, false), SatLiteral(1, false), SatLiteral(2, true)});
  addClause(
      clauses,
      usedIds,
      2,
      std::vector<SatLiteral>{
          SatLiteral(0, true), SatLiteral(1, true), SatLiteral(2, false)});
  addClause(
      clauses,
      usedIds,
      3,
      std::vector<SatLiteral>{
          SatLiteral(1, false), SatLiteral(2, false), SatLiteral(3, true)});
  addClause(
      clauses,
      usedIds,
      4,
      std::vector<SatLiteral>{
          SatLiteral(1, true), SatLiteral(2, true), SatLiteral(3, false)});
  addClause(clauses,
            usedIds,
            5,
            std::vector<SatLiteral>{
                SatLiteral(0, true), SatLiteral(2, true), SatLiteral(3, true)});
  addClause(
      clauses,
      usedIds,
      6,
      std::vector<SatLiteral>{
          SatLiteral(0, false), SatLiteral(2, false), SatLiteral(3, false)});
  addClause(
      clauses,
      usedIds,
      7,
      std::vector<SatLiteral>{
          SatLiteral(0, true), SatLiteral(1, false), SatLiteral(3, false)});
  addClause(
      clauses,
      usedIds,
      8,
      std::vector<SatLiteral>{
          SatLiteral(0, false), SatLiteral(1, true), SatLiteral(3, true)});
  ErProof pf(clauses, usedIds, std::move(tc));

  std::ostringstream actual_pf_body;
  pf.outputAsLfsc(actual_pf_body);

#if IS_LFSC_BUILD
  std::string pf_header = R"EOF(
    (check
      (% bb.v0 var
      (% bb.v1 var
      (% bb.v2 var
      (% bb.v3 var
        (% bb.pb1 (holds (clc (pos bb.v0) (clc (pos bb.v1) (clc (neg bb.v2) cln))))
        (% bb.pb2 (holds (clc (neg bb.v0) (clc (neg bb.v1) (clc (pos bb.v2) cln))))
        (% bb.pb3 (holds (clc (pos bb.v1) (clc (pos bb.v2) (clc (neg bb.v3) cln))))
        (% bb.pb4 (holds (clc (neg bb.v1) (clc (neg bb.v2) (clc (pos bb.v3) cln))))
        (% bb.pb5 (holds (clc (neg bb.v0) (clc (neg bb.v2) (clc (neg bb.v3) cln))))
        (% bb.pb6 (holds (clc (pos bb.v0) (clc (pos bb.v2) (clc (pos bb.v3) cln))))
        (% bb.pb7 (holds (clc (neg bb.v0) (clc (pos bb.v1) (clc (pos bb.v3) cln))))
        (% bb.pb8 (holds (clc (pos bb.v0) (clc (neg bb.v1) (clc (neg bb.v3) cln))))
          (: (holds cln)
    )EOF";

  std::string pf_footer = R"EOF(
          )
        ))))))))
      ))))
    )
    )EOF";

  std::stringstream actual_pf;
  actual_pf << proof::plf_signatures << pf_header << actual_pf_body.str() << pf_footer;

  lfscc_init();
  lfscc_check_file(actual_pf, false, false, false, false, false, false, false);
#endif
}
