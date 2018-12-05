/*********************                                                        */
/*! \file lrat_proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
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
 ** prove things about bitvectors.
 **
 ** Paper on LRAT: https://www.cs.utexas.edu/~marijn/publications/lrat.pdf
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PROOF__LRAT__LRAT_PROOF_H
#define __CVC4__PROOF__LRAT__LRAT_PROOF_H 0

#include <vector>
#include <unordered_map>
#include <string>

#include "base/output.h"
#include "proof/clause_id.h"
// Included because we nee operator<< for the SAT types
#include "prop/sat_solver.h"

namespace CVC4 {
namespace proof {
namespace lrat {

// Refers to clause position within an LRAT proof
using ClauseIdx = size_t;

enum LRATInstructionKind
{
  lratDeletion,
  lratAddition,
};

struct LRATDeletionData
{
  // This idx doesn't really matter, but it's in the format anyway, so we parse
  // it.
  ClauseIdx idxOfClause;

  // Clauses to delete
  std::vector<ClauseIdx> clauses;
};

// A sequence of locations that will contain unit clauses during unit
// propegation
using LRATUPTrace = std::vector<ClauseIdx>;

struct LRATAdditionData
{
  // The idx for the new clause
  ClauseIdx idxOfClause;
  // The new clause
  prop::SatClause clause;
  // UP trace based on the negation of that clause
  LRATUPTrace atTrace;

  // Clauses that can resolve with `clause` on its first variable,
  // together with a UP trace after that resolution.
  // Used for RAT checks.
  std::vector<std::pair<ClauseIdx, LRATUPTrace>> resolvants;
};

// This is conceptually an Either<Addition,Deletion>
struct LRATInstruction
{
  LRATInstructionKind kind;
  LRATAdditionData additionData;
  LRATDeletionData deletionData;
};

class LRATProof
{
 public:

   /**
    * @brief Construct an LRAT proof from a DRAT proof, using drat-trim
    *
    * @param usedClauses The CNF formula that we're deriving bottom from.
    *                    It's a map because other parts of the system represent
    *                    it this way.
    * @param clauseOrder A record of the order in which those clauses were
    *                    given to the SAT solver.
    * @param dratBinary  The DRAT proof from the SAT solver, as a binary stream.
    */
  LRATProof(const std::unordered_map<ClauseId, prop::SatClause*>& usedClauses,
            const std::vector<ClauseId>& clauseOrder,
            const std::string& dratBinary);
  /**
   * @brief Construct an LRAT proof from its textual representation
   *
   * @param textualProof the textual encoding of the LRAT proof. See the paper
   *                     in the file's header comment.
   */
  LRATProof(std::istream& textualProof);

  inline const std::vector<LRATInstruction>& getInstructions() const
  {
    return d_instructions;
  }

 private:
  // The instructions in the proof. Each is a deletion or addition.
  std::vector<LRATInstruction> d_instructions;
};

// Prints the literal as a (+) or (-) int
// Not operator<< b/c that represents negation as ~
inline std::ostream& textOut(std::ostream& o, const prop::SatLiteral& l)
{
  if (l.isNegated())
  {
    o << "-";
  }
  return o << l.getSatVariable();
}

// Prints the clause as a space-separated list of ints
// Not operator<< b/c that represents negation as ~
inline std::ostream& textOut(std::ostream& o, const prop::SatClause& c)
{
  for (const auto l : c)
  {
    textOut(o, l) << " ";
  }
  return o << "0";
}

// Prints the trace as a space-separated list of (+) ints with a space at the
// end.
inline std::ostream& operator<<(std::ostream& o, const LRATUPTrace& trace)
{
  for (const auto i : trace)
  {
    o << i << " ";
  }
  return o;
}

// Prints the LRAT addition line in textual format
inline std::ostream& operator<<(std::ostream& o, const LRATAdditionData& add)
{
  o << add.idxOfClause << " ";
  textOut(o, add.clause) << " ";
  o << add.atTrace;  // Inludes a space at the end.
  for (const auto& rat : add.resolvants)
  {
    o << "-" << rat.first << " ";
    o << rat.second;  // Includes a space at the end.
  }
  o << "0\n";
  return o;
}

// Prints the LRAT addition line in textual format
inline std::ostream& operator<<(std::ostream& o, const LRATDeletionData& del)
{
  o << del.idxOfClause << " d ";
  for (const auto& idx : del.clauses)
  {
    o << idx << " ";
  }
  return o << "0\n";
}

// Prints the LRAT line in textual format
inline std::ostream& operator<<(std::ostream& o, const LRATInstruction& i)
{
  switch (i.kind)
  {
    case lratAddition: return o << i.additionData;
    case lratDeletion: return o << i.deletionData;
    default: return o;
  }
}

// Prints the LRAT proof in textual format
inline std::ostream& operator<<(std::ostream& o, const LRATProof& p)
{
  for (const auto& instr : p.getInstructions())
  {
    o << instr;
  }
  return o;
}

}  // namespace lrat
}  // namespace proof
}  // namespace CVC4

#endif
