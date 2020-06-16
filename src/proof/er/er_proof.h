/*********************                                                        */
/*! \file er_proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief ER Proof Format
 **
 ** Declares C++ types that represent an ER/TRACECHECK proof.
 ** Defines serialization for these types.
 **
 ** You can find details about the way ER is encoded in the TRACECHECK
 ** format at these locations:
 **    https://github.com/benjaminkiesl/drat2er
 **    http://www.cs.utexas.edu/users/marijn/publications/ijcar18.pdf
 **
 **/

#include "cvc4_private.h"

#ifndef CVC4__PROOF__ER__ER_PROOF_H
#define CVC4__PROOF__ER__ER_PROOF_H

#include <memory>
#include <unordered_map>
#include <vector>

#include "proof/clause_id.h"
#include "prop/sat_solver_types.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace proof {
namespace er {

/**
 * A definition of the form:
 *    newVar <-> p v (~x_1 ^ ~x_2 ^ ... ^ ~x_n)
 */
struct ErDefinition
{
  ErDefinition(prop::SatVariable newVariable,
               prop::SatLiteral oldLiteral,
               std::vector<prop::SatLiteral>&& otherLiterals)
      : d_newVariable(newVariable),
        d_oldLiteral(oldLiteral),
        d_otherLiterals(otherLiterals)
  {
  }

  // newVar
  prop::SatVariable d_newVariable;
  // p
  prop::SatLiteral d_oldLiteral;
  // A list of the x_i's
  std::vector<prop::SatLiteral> d_otherLiterals;
};

// For representing a clause's index within a TRACECHECK proof.
using TraceCheckIdx = size_t;

/**
 * A single line in a TRACECHECK proof.
 *
 * Consists of the index of a new clause, the literals of that clause, and the
 * indices for preceding clauses which can be combined in a resolution chain to
 * produce this new clause.
 */
struct TraceCheckLine
{
  TraceCheckLine(TraceCheckIdx idx,
                 std::vector<prop::SatLiteral>&& clause,
                 std::vector<TraceCheckIdx>&& chain)
      : d_idx(idx), d_clause(clause), d_chain(chain)
  {
  }

  // The index of the new clause
  TraceCheckIdx d_idx;
  // The new clause
  std::vector<prop::SatLiteral> d_clause;
  /**
   * Indices of clauses which must be resolved to produce this new clause.
   * While the TRACECHECK format does not specify the order, we require them to
   * be in resolution-order.
   */
  std::vector<TraceCheckIdx> d_chain;
};

/**
 * A TRACECHECK proof -- just a list of lines
 */
struct TraceCheckProof
{
  static TraceCheckProof fromText(std::istream& in);
  TraceCheckProof() : d_lines() {}

  // The lines of this proof.
  std::vector<TraceCheckLine> d_lines;
};

/**
 * An extended resolution proof.
 * It supports resolution, along with extensions of the form
 *
 *    newVar <-> p v (~x_1 ^ ~x_2 ^ ... ^ ~x_n)
 */
class ErProof
{
 public:
  /**
   * Construct an ER proof from a DRAT proof, using drat2er
   *
   * @param clauses A store of clauses that might be in our formula
   * @param usedIds the ids of clauses that are actually in our formula
   * @param dratBinary  The DRAT proof from the SAT solver, as a binary stream
   *
   * @return the Er proof and a timer of the execution of drat2er
   */
  static ErProof fromBinaryDratProof(
      const std::unordered_map<ClauseId, prop::SatClause>& clauses,
      const std::vector<ClauseId>& usedIds,
      const std::string& dratBinary,
      TimerStat& toolTimer
      );

  /**
   * Construct an ER proof from a TRACECHECK ER proof
   *
   * This basically just identifies groups of lines which correspond to
   * definitions, and extracts them.
   *
   * @param clauses A store of clauses that might be in our formula
   * @param usedIds the ids of clauses that are actually in our formula
   * @param tracecheck  The TRACECHECK proof, as a stream.
   */
  ErProof(const std::unordered_map<ClauseId, prop::SatClause>& clauses,
          const std::vector<ClauseId>& usedIds,
          TraceCheckProof&& tracecheck);

  /**
   * Write the ER proof as an LFSC value of type (holds cln).
   * The format is from the LFSC signature er.plf
   *
   * Reads the current `ProofManager` to determine what the variables should be
   * named.
   *
   * @param os the stream to write to
   */
  void outputAsLfsc(std::ostream& os) const;

  const std::vector<ClauseId>& getInputClauseIds() const
  {
    return d_inputClauseIds;
  }

  const std::vector<ErDefinition>& getDefinitions() const
  {
    return d_definitions;
  }

  const TraceCheckProof& getTraceCheckProof() const { return d_tracecheck; }

 private:
  /**
   * Creates an empty ErProof.
   */
  ErProof() : d_inputClauseIds(), d_definitions(), d_tracecheck() {}

  /**
   * Computes the pivots on the basis of which an in-order resolution chain is
   * resolved.
   *
   * c0   c1
   *   \ /               Clauses c_i being resolved in a chain around
   *    v1  c2           pivots v_i.
   *     \ /
   *      v2  c3
   *       \ /
   *        v3  c4
   *         \ /
   *          v4
   *
   *
   * @param chain the chain, of N clause indices
   *
   * @return a list of N - 1 variables, the list ( v_i ) from i = 1 to N - 1
   */
  std::vector<prop::SatLiteral> computePivotsForChain(
      const std::vector<TraceCheckIdx>& chain) const;

  /**
   * Write the LFSC identifier for the proof of a clause
   *
   * @param o where to write to
   * @param i the TRACECHECK index for the clause whose proof identifier to
   *        print
   */
  void writeIdForClauseProof(std::ostream& o, TraceCheckIdx i) const;

  // A list of the Ids for the input clauses, in order.
  std::vector<ClauseId> d_inputClauseIds;
  // A list of new variable definitions, in order.
  std::vector<ErDefinition> d_definitions;
  // The underlying TRACECHECK proof.
  TraceCheckProof d_tracecheck;
};

}  // namespace er
}  // namespace proof
}  // namespace CVC4

#endif  // CVC4__PROOF__ER__ER_PROOF_H
