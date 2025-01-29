/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Andrew Reynolds, Dejan Jovanovic
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The proof-producing CNF stream.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP__PROOF_CNF_STREAM_H
#define CVC5__PROP__PROOF_CNF_STREAM_H

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "proof/eager_proof_generator.h"
#include "proof/lazy_proof.h"
#include "proof/proof_node.h"
#include "proof/proof_node_manager.h"
#include "proof/theory_proof_step_buffer.h"
#include "prop/cnf_stream.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace prop {

class PropPfManager;

/**
 * A proof generator for CNF transformation. It is a layer on top of CNF stream,
 * tracking the justifications for clauses added into the underlying SAT solver
 * in a user-context dependent manner in a lazy context-dependent (LazyCDProof)
 * object. The proof is lazy because formulas asserted to this class may also
 * take proof generators (which is the case, for example, for theory lemmas), so
 * that getting the proof of a clausified formula will also extend to its
 * registered proof generator.
 */
class ProofCnfStream : protected EnvObj
{
 public:
  ProofCnfStream(Env& env, CnfStream& cnfStream, PropPfManager* ppm);
  /**
   * Converts a formula into CNF into CNF and asserts the generated clauses into
   * the underlying SAT solver of d_cnfStream. Every transformation the formula
   * goes through is saved as a concrete step in d_proof.
   *
   * The given formula has arbitrary Boolean structure via kinds AND, OR, EQUAL,
   * XOR, IMPLIES. ITE and NOT. The conversion is done polynomially via Tseitin
   * transformation, with the children of non-conjunctive kinds being abstracted
   * as new literals, which are clausified with the respective "handle" methods
   * below.

   * @param node formula to convert and assert
   * @param negated whether we are asserting the node negated
   * @param removable whether the SAT solver can choose to remove the clauses
   * @param input whether the node is from the input
   * @param pg a proof generator for node
   */
  void convertAndAssert(
      TNode node, bool negated, bool removable, bool input, ProofGenerator* pg);

  /**
   * Ensure that the given node will have a designated SAT literal that is
   * definitionally equal to it.  The result of this function is that the Node
   * can be queried via getSatValue(). Essentially, this is like a "convert-but-
   * don't-assert" version of convertAndAssert().
   */
  void ensureLiteral(TNode n);

  /**
   * Returns true iff the node has an assigned literal (it might not be
   * translated).
   */
  bool hasLiteral(TNode node) const;

  /**
   * Returns the literal that represents the given node in the SAT CNF
   * representation.
   */
  SatLiteral getLiteral(TNode node);

  /**
   * Returns the Boolean variables from the input problem.
   */
  void getBooleanVariables(std::vector<TNode>& outputVariables) const;

  /**
   * Dump dimacs of the given clauses to the given output stream.
   * For details, see cnf_stream.h.
   */
  void dumpDimacs(std::ostream& out, const std::vector<Node>& clauses);
  /**
   * Same as above, but also prints additional "auxiliary unit" clauses.
   * For details, see cnf_stream.h.
   */
  void dumpDimacs(std::ostream& out,
                  const std::vector<Node>& clauses,
                  const std::vector<Node>& auxUnits);

 private:
  /**
   * Same as above, except that uses the saved d_removable flag. It calls the
   * dedicated converter for the possible formula kinds.
   */
  void convertAndAssert(TNode node, bool negated);
  /** Specific converters for each formula kind. */
  void convertAndAssertAnd(TNode node, bool negated);
  void convertAndAssertOr(TNode node, bool negated);
  void convertAndAssertXor(TNode node, bool negated);
  void convertAndAssertIff(TNode node, bool negated);
  void convertAndAssertImplies(TNode node, bool negated);
  void convertAndAssertIte(TNode node, bool negated);
  /**
   * Transforms the node into CNF recursively and yields a literal
   * definitionally equal to it.
   *
   * This method also populates caches, kept in d_cnfStream, between formulas
   * and literals to avoid redundant work and to retrieve formulas from literals
   * and vice-versa.
   *
   * @param node the formula to transform
   * @param negated whether the literal is negated
   * @return the literal representing the root of the formula
   */
  SatLiteral toCNF(TNode node, bool negated = false);
  /**
   * Specific clausifiers, based on the formula kinds, that clausify a formula,
   * by calling toCNF into each of the formula's children under the respective
   * kind, and introduce a literal definitionally equal to it. */
  SatLiteral handleXor(TNode node);
  SatLiteral handleImplies(TNode node);
  SatLiteral handleIff(TNode node);
  SatLiteral handleIte(TNode node);
  SatLiteral handleAnd(TNode node);
  SatLiteral handleOr(TNode node);

  /** Reference to the underlying cnf stream. */
  CnfStream& d_cnfStream;

  /** Whether we are we asserting clauses derived from the input. */
  bool d_input;

  /** Pointer to the prop proof manager. */
  PropPfManager* d_ppm;
  /** The proof of d_ppm */
  LazyCDProof* d_proof;
};

}  // namespace prop
}  // namespace cvc5::internal

#endif
