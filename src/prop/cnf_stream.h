/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Dejan Jovanovic, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * This class transforms a sequence of formulas into clauses.
 *
 * This class takes a sequence of formulas.
 * It outputs a stream of clauses that is propositionally
 * equi-satisfiable with the conjunction of the formulas.
 * This stream is maintained in an online fashion.
 *
 * Unlike other parts of the system it is aware of the PropEngine's
 * internals such as the representation and translation of [??? -Chris]
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP__CNF_STREAM_H
#define CVC5__PROP__CNF_STREAM_H

#include "context/cdhashset.h"
#include "context/cdinsert_hashmap.h"
#include "context/cdlist.h"
#include "expr/node.h"
#include "prop/registrar.h"
#include "prop/sat_solver_types.h"
#include "smt/env_obj.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {

class Env;

namespace prop {

class ProofCnfStream;
class PropEngine;
class SatSolver;

/** A policy for how literals for formulas are handled in cnf_stream */
enum class FormulaLitPolicy : uint32_t
{
  // literals for formulas are notified
  TRACK_AND_NOTIFY,
  // literals for Boolean variables are notified
  TRACK_AND_NOTIFY_VAR,
  // literals for formulas are added to node map
  TRACK,
  // literals for formulas are kept internal (default)
  INTERNAL,
};

/**
 * Implements the following recursive algorithm
 * http://people.inf.ethz.ch/daniekro/classes/251-0247-00/f2007/readings/Tseitin70.pdf
 * in a single pass.
 *
 * The general idea is to introduce a new literal that will be equivalent to
 * each subexpression in the constructed equi-satisfiable formula, then
 * substitute the new literal for the formula, and so on, recursively.
 */
class CnfStream : protected EnvObj
{
  friend PropEngine;
  friend ProofCnfStream;

 public:
  /** Cache of what nodes have been registered to a literal. */
  typedef context::CDInsertHashMap<SatLiteral, TNode, SatLiteralHashFunction>
      LiteralToNodeMap;

  /** Cache of what literals have been registered to a node. */
  typedef context::CDInsertHashMap<Node, SatLiteral> NodeToLiteralMap;

  /**
   * Constructs a CnfStream that performs equisatisfiable CNF transformations
   * and sends the generated clauses and to the given SAT solver. This does not
   * take ownership of satSolver, registrar, or context.
   *
   * @param env reference to the environment
   * @param satSolver the sat solver to use.
   * @param registrar the entity that takes care of preregistration of Nodes.
   * @param c the context that the CNF should respect.
   * @param flpol policy for literals corresponding to formulas (those that are
   * not-theory literals).
   * @param name string identifier to distinguish between different instances
   * even for non-theory literals.
   */
  CnfStream(Env& env,
            SatSolver* satSolver,
            Registrar* registrar,
            context::Context* c,
            FormulaLitPolicy flpol = FormulaLitPolicy::INTERNAL,
            std::string name = "");
  /**
   * Convert a given formula to CNF and assert it to the SAT solver.
   *
   * @param node node to convert and assert
   * @param removable whether the sat solver can choose to remove the clauses
   * @param negated whether we are asserting the node negated
   */
  void convertAndAssert(TNode node, bool removable, bool negated);
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
  void ensureLiteral(TNode n);

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

  /**
   * For SAT/theory relevancy. Returns true if node is a "notify formula".
   * Returns true if node is formula that we are being notified about that
   * is not a theory atom.
   *
   * Note this is only ever true when the policy passed to this class is
   * FormulaLitPolicy::TRACK_AND_NOTIFY.
   */
  bool isNotifyFormula(TNode node) const;

  /** Retrieves map from nodes to literals. */
  const CnfStream::NodeToLiteralMap& getTranslationCache() const;

  /** Retrieves map from literals to nodes. */
  const CnfStream::LiteralToNodeMap& getNodeCache() const;

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

  /**
   * Specific clausifiers that clausify a formula based on the given formula
   * kind and introduce a literal definitionally equal to it.
   */
  void handleXor(TNode node);
  void handleImplies(TNode node);
  void handleIff(TNode node);
  void handleIte(TNode node);
  void handleAnd(TNode node);
  void handleOr(TNode node);

  /** Stores the literal of the given node in d_literalToNodeMap.
   *
   * Note that n must already have a literal associated to it in
   * d_nodeToLiteralMap.
   */
  void ensureMappingForLiteral(TNode n);

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
   * @param notifyTheory whether to notify the theory of the atom
   * @param canEliminate whether the sat solver can safely eliminate this
   * variable.
   * @return the literal corresponding to the formula
   */
  SatLiteral newLiteral(TNode node,
                        bool isTheoryAtom = false,
                        bool notifyTheory = false,
                        bool canEliminate = true);

  /**
   * Constructs a new literal for an atom and returns it.  Calls
   * newLiteral().
   *
   * @param node the node to convert; there should be no boolean
   * structure in this expression.  Assumed to not be in the
   * translation cache.
   */
  SatLiteral convertAtom(TNode node);

  /** The SAT solver we will be using */
  SatSolver* d_satSolver;

  /** Boolean variables that we translated */
  context::CDList<TNode> d_booleanVariables;

  /** Formulas that we translated that we are notifying */
  context::CDHashSet<Node> d_notifyFormulas;

  /** Map from nodes to literals */
  NodeToLiteralMap d_nodeToLiteralMap;

  /** Map from literals to nodes */
  LiteralToNodeMap d_literalToNodeMap;

  /**
   * True if the lit-to-Node map should be kept for all lits, not just
   * theory lits.  This is true if e.g. replay logging is on, which
   * dumps the Nodes corresponding to decision literals.
   */
  const FormulaLitPolicy d_flitPolicy;

  /** The "registrar" for pre-registration of terms */
  Registrar* d_registrar;

  /** The name of this CNF stream*/
  std::string d_name;

  /**
   * Are we asserting a removable clause (true) or a permanent clause (false).
   * This is set at the beginning of convertAndAssert so that it doesn't
   * need to be passed on over the stack.  Only pure clauses can be asserted
   * as removable.
   */
  bool d_removable;

  /** Pointer to resource manager for associated SolverEngine */
  ResourceManager* d_resourceManager;

 private:
  struct Statistics
  {
    Statistics(StatisticsRegistry& sr, const std::string& name);
    TimerStat d_cnfConversionTime;
  } d_stats;

}; /* class CnfStream */

}  // namespace prop
}  // namespace cvc5::internal

#endif /* CVC5__PROP__CNF_STREAM_H */
