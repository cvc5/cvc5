/*********************                                                        */
/*! \file lrat_proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief LRAT Proof Format
 **
 ** Declares C++ types that represent a LRAT proof.
 ** Defines serialization for these types.
 **
 ** Represents an **abstract** LRAT proof.
 ** Does **not** represent an LFSC LRAT proof, or an LRAT proof being used to
 ** prove things about bit-vectors.
 **
 ** Paper on LRAT: https://www.cs.utexas.edu/~marijn/publications/lrat.pdf
 **/

#include "cvc4_private.h"

#ifndef CVC4__PROOF__LRAT__LRAT_PROOF_H
#define CVC4__PROOF__LRAT__LRAT_PROOF_H

#include <iosfwd>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "proof/clause_id.h"
// Included because we need operator<< for the SAT types
#include "prop/sat_solver.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace proof {
namespace lrat {

// Refers to clause position within an LRAT proof
using ClauseIdx = size_t;

// This is conceptually an Either<Addition,Deletion>
class LratInstruction
{
 public:
  /**
   * Write this LRAT instruction in textual format
   *
   * @param out the stream to write to
   */
  virtual void outputAsText(std::ostream& out) const = 0;
  /**
   * Write this LRAT instruction as an LFSC value
   *
   * @param out the stream to write to
   * @param closeParen the stream to write any closing parentheses to
   *
   */
  virtual void outputAsLfsc(std::ostream& o,
                            std::ostream& closeParen) const = 0;
  virtual ~LratInstruction() = default;
};

class LratDeletion : public LratInstruction
{
 public:
  LratDeletion(ClauseIdx idxOfClause, std::vector<ClauseIdx>&& clauses)
      : d_idxOfClause(idxOfClause), d_clauses(clauses)
  {
    // Nothing left to do
  }

  LratDeletion() = default;

  void outputAsText(std::ostream& out) const override;
  void outputAsLfsc(std::ostream& o, std::ostream& closeParen) const override;

 private:
  // This idx doesn't really matter, but it's in the format anyway, so we parse
  // it.
  ClauseIdx d_idxOfClause;

  // Clauses to delete
  std::vector<ClauseIdx> d_clauses;
};

// A sequence of locations that will contain unit clauses during unit
// propegation
using LratUPTrace = std::vector<ClauseIdx>;

class LratAddition : public LratInstruction
{
 public:
  LratAddition(ClauseIdx idxOfClause,
               prop::SatClause&& clause,
               LratUPTrace&& atTrace,
               std::vector<std::pair<ClauseIdx, LratUPTrace>> resolvants)
      : d_idxOfClause(idxOfClause),
        d_clause(clause),
        d_atTrace(atTrace),
        d_resolvants(resolvants)
  {
    // Nothing left to do
  }

  void outputAsText(std::ostream& out) const override;
  void outputAsLfsc(std::ostream& o, std::ostream& closeParen) const override;

 private:
  // The idx for the new clause
  ClauseIdx d_idxOfClause;
  // The new clause
  prop::SatClause d_clause;
  // UP trace based on the negation of that clause
  LratUPTrace d_atTrace;

  // Clauses that can resolve with `clause` on its first variable,
  // together with a UP trace after that resolution.
  // Used for RAT checks.
  std::vector<std::pair<ClauseIdx, LratUPTrace>> d_resolvants;
};

class LratProof
{
 public:
  /**
   * @brief Construct an LRAT proof from a DRAT proof, using drat-trim
   *
   * @param clauses A store of clauses that might be in our formula
   * @param usedIds the ids of clauses that are actually in our formula
   * @param dratBinary  The DRAT proof from the SAT solver, as a binary stream.
   *
   * @return an LRAT proof an a timer for how long it took to run drat-trim
   */
  static LratProof fromDratProof(
      const std::unordered_map<ClauseId, prop::SatClause>& clauses,
      const std::vector<ClauseId> usedIds,
      const std::string& dratBinary,
      TimerStat& toolTimer);
  /**
   * @brief Construct an LRAT proof from its textual representation
   *
   * @param textualProof the textual encoding of the LRAT proof. See the paper
   *                     in the file's header comment.
   */
  LratProof(std::istream& textualProof);

  /**
   * Construct a LRAT proof from an explicit instruction list
   *
   * @param instructions
   */
  LratProof(std::vector<std::unique_ptr<LratInstruction>>&& instructions)
      : d_instructions(std::move(instructions))
  {
    // Nothing else
  }

  const std::vector<std::unique_ptr<LratInstruction>>& getInstructions() const
  {
    return d_instructions;
  }

  void outputAsLfsc(std::ostream& o) const;

 private:
  // The instructions in the proof. Each is a deletion or addition.
  std::vector<std::unique_ptr<LratInstruction>> d_instructions;
};

// Prints the LRAT proof in textual format
std::ostream& operator<<(std::ostream& o, const LratProof& p);
std::ostream& operator<<(std::ostream& o, const LratInstruction& i);

}  // namespace lrat
}  // namespace proof
}  // namespace CVC4

#endif
