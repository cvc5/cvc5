/*********************                                                        */
/*! \file cnf_stream.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief This class transforms a sequence of formulas into clauses.
 **
 ** This class takes a sequence of formulas.
 ** It outputs a stream of clauses that is propositionally
 ** equi-satisfiable with the conjunction of the formulas.
 ** This stream is maintained in an online fashion.
 **
 ** Unlike other parts of the system it is aware of the PropEngine's
 ** internals such as the representation and translation of [??? -Chris]
 **/

#include "cvc4_private.h"

#ifndef CVC4__PROP__CNF_STREAM_H
#define CVC4__PROP__CNF_STREAM_H

#include "context/cdinsert_hashmap.h"
#include "context/cdlist.h"
#include "expr/node.h"
#include "proof/proof_manager.h"
#include "prop/proof_cnf_stream.h"
#include "prop/registrar.h"
#include "prop/theory_proxy.h"

namespace CVC4 {

class OutputManager;

namespace prop {

class ProofCnfStream;

/**
 * Implements the following recursive algorithm
 * http://people.inf.ethz.ch/daniekro/classes/251-0247-00/f2007/readings/Tseitin70.pdf
 * in a single pass.
 *
 * The general idea is to introduce a new literal that will be equivalent to
 * each subexpression in the constructed equi-satisfiable formula, then
 * substitute the new literal for the formula, and so on, recursively.
 */
class CnfStream {
  friend PropEngine;
  friend ProofCnfStream;

 public:
  /** Cache of what nodes have been registered to a literal. */
  typedef context::CDInsertHashMap<SatLiteral, TNode, SatLiteralHashFunction>
      LiteralToNodeMap;

  /** Cache of what literals have been registered to a node. */
  typedef context::CDInsertHashMap<Node, SatLiteral, NodeHashFunction>
      NodeToLiteralMap;

  /**
   * Constructs a CnfStream that performs equisatisfiable CNF transformations
   * and sends the generated clauses and to the given SAT solver. This does not
   * take ownership of satSolver, registrar, or context.
   *
   * @param satSolver the sat solver to use.
   * @param registrar the entity that takes care of preregistration of Nodes.
   * @param context the context that the CNF should respect.
   * @param outMgr Reference to the output manager of the smt engine. Assertions
   * will not be dumped if outMgr == nullptr.
   * @param rm the resource manager of the CNF stream
   * @param fullLitToNodeMap maintain a full SAT-literal-to-Node mapping.
   * @param name string identifier to distinguish between different instances
   * even for non-theory literals.
   */
  CnfStream(SatSolver* satSolver,
            Registrar* registrar,
            context::Context* context,
            OutputManager* outMgr,
            ResourceManager* rm,
            bool fullLitToNodeMap = false,
            std::string name = "");
  /**
   * Convert a given formula to CNF and assert it to the SAT solver.
   *
   * @param node node to convert and assert
   * @param removable whether the sat solver can choose to remove the clauses
   * @param negated whether we are asserting the node negated
   * @param input whether it is an input assertion (rather than a lemma). This
   * information is only relevant for unsat core tracking.
   */
  void convertAndAssert(TNode node,
                        bool removable,
                        bool negated,
                        bool input = false);
  /**
   * Get the node that is represented by the given SatLiteral.
   * @param literal the literal from the sat solver
   * @return the actual node
   */
  TNode getNode(const SatLiteral& literal);

  /**
   * Returns true iff the node has an assigned literal (it might not be
   * translated).
   * @param node the node
   */
  bool hasLiteral(TNode node) const;

  /**
   * Ensure that the given node will have a designated SAT literal that is
   * definitionally equal to it.  The result of this function is that the Node
   * can be queried via getSatValue(). Essentially, this is like a "convert-but-
   * don't-assert" version of convertAndAssert().
   */
  void ensureLiteral(TNode n, bool noPreregistration = false);

  /**
   * Returns the literal that represents the given node in the SAT CNF
   * representation.
   * @param node [Presumably there are some constraints on the kind of
   * node? E.g., it needs to be a boolean? -Chris]
   */
  SatLiteral getLiteral(TNode node);

  /**
   * Returns the Boolean variables from the input problem.
   */
  void getBooleanVariables(std::vector<TNode>& outputVariables) const;

  /** Retrieves map from nodes to literals. */
  const CnfStream::NodeToLiteralMap& getTranslationCache() const;

  /** Retrieves map from literals to nodes. */
  const CnfStream::LiteralToNodeMap& getNodeCache() const;

  void setProof(CnfProof* proof);

 protected:
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

  /** Specific clausifiers, based on the formula kinds, that clausify a formula,
   * by calling toCNF into each of the formula's children under the respective
   * kind, and introduce a literal definitionally equal to it. */
  SatLiteral handleNot(TNode node);
  SatLiteral handleXor(TNode node);
  SatLiteral handleImplies(TNode node);
  SatLiteral handleIff(TNode node);
  SatLiteral handleIte(TNode node);
  SatLiteral handleAnd(TNode node);
  SatLiteral handleOr(TNode node);

  /** The SAT solver we will be using */
  SatSolver* d_satSolver;

  /** Reference to the output manager of the smt engine */
  OutputManager* d_outMgr;

  /** Boolean variables that we translated */
  context::CDList<TNode> d_booleanVariables;

  /** Map from nodes to literals */
  NodeToLiteralMap d_nodeToLiteralMap;

  /** Map from literals to nodes */
  LiteralToNodeMap d_literalToNodeMap;

  /**
   * True if the lit-to-Node map should be kept for all lits, not just
   * theory lits.  This is true if e.g. replay logging is on, which
   * dumps the Nodes corresponding to decision literals.
   */
  const bool d_fullLitToNodeMap;

  /**
   * Counter for resource limiting that is used to spend a resource
   * every ResourceManager::resourceCounter calls to convertAndAssert.
   */
  unsigned long d_convertAndAssertCounter;

  /** The "registrar" for pre-registration of terms */
  Registrar* d_registrar;

  /** The name of this CNF stream*/
  std::string d_name;

  /** Pointer to the proof corresponding to this CnfStream */
  CnfProof* d_cnfProof;

  /**
   * Are we asserting a removable clause (true) or a permanent clause (false).
   * This is set at the beginning of convertAndAssert so that it doesn't
   * need to be passed on over the stack.  Only pure clauses can be asserted
   * as removable.
   */
  bool d_removable;

  /**
   * Asserts the given clause to the sat solver.
   * @param node the node giving rise to this clause
   * @param clause the clause to assert
   * @return whether the clause was asserted in the SAT solver.
   */
  bool assertClause(TNode node, SatClause& clause);

  /**
   * Asserts the unit clause to the sat solver.
   * @param node the node giving rise to this clause
   * @param a the unit literal of the clause
   * @return whether the clause was asserted in the SAT solver.
   */
  bool assertClause(TNode node, SatLiteral a);

  /**
   * Asserts the binary clause to the sat solver.
   * @param node the node giving rise to this clause
   * @param a the first literal in the clause
   * @param b the second literal in the clause
   * @return whether the clause was asserted in the SAT solver.
   */
  bool assertClause(TNode node, SatLiteral a, SatLiteral b);

  /**
   * Asserts the ternary clause to the sat solver.
   * @param node the node giving rise to this clause
   * @param a the first literal in the clause
   * @param b the second literal in the clause
   * @param c the thirs literal in the clause
   * @return whether the clause was asserted in the SAT solver.
   */
  bool assertClause(TNode node, SatLiteral a, SatLiteral b, SatLiteral c);

  /**
   * Acquires a new variable from the SAT solver to represent the node
   * and inserts the necessary data it into the mapping tables.
   * @param node a formula
   * @param isTheoryAtom is this a theory atom that needs to be asserted to
   * theory.
   * @param preRegister whether to preregister the atom with the theory
   * @param canEliminate whether the sat solver can safely eliminate this
   * variable.
   * @return the literal corresponding to the formula
   */
  SatLiteral newLiteral(TNode node, bool isTheoryAtom = false,
                        bool preRegister = false, bool canEliminate = true);

  /**
   * Constructs a new literal for an atom and returns it.  Calls
   * newLiteral().
   *
   * @param node the node to convert; there should be no boolean
   * structure in this expression.  Assumed to not be in the
   * translation cache.
   */
  SatLiteral convertAtom(TNode node, bool noPreprocessing = false);

  /** Pointer to resource manager for associated SmtEngine */
  ResourceManager* d_resourceManager;
}; /* class CnfStream */

}  // namespace prop
}  // namespace CVC4

#endif /* CVC4__PROP__CNF_STREAM_H */
