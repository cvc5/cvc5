/*********************                                                        */
/*! \file cnf_stream.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
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

#ifndef __CVC4__PROP__CNF_STREAM_H
#define __CVC4__PROP__CNF_STREAM_H

#include <ext/hash_map>

#include "context/cdinsert_hashmap.h"
#include "context/cdlist.h"
#include "expr/node.h"
#include "proof/proof_manager.h"
#include "prop/registrar.h"
#include "prop/theory_proxy.h"
#include "smt_util/lemma_channels.h"

namespace CVC4 {

namespace prop {

class PropEngine;

/**
 * Comments for the behavior of the whole class... [??? -Chris]
 * @author Tim King <taking@cs.nyu.edu>
 */
class CnfStream {
 public:
  /** Cache of what nodes have been registered to a literal. */
  typedef context::CDInsertHashMap<SatLiteral, TNode, SatLiteralHashFunction>
      LiteralToNodeMap;

  /** Cache of what literals have been registered to a node. */
  typedef context::CDInsertHashMap<Node, SatLiteral, NodeHashFunction>
      NodeToLiteralMap;

 protected:
  /** The SAT solver we will be using */
  SatSolver* d_satSolver;

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
   * How many literals were already mapped at the top-level when we
   * tried to convertAndAssert() something.  This
   * achieves early detection of units and leads to fewer
   * clauses.  It's motivated by the following pattern:
   *
   *   ASSERT  BIG FORMULA => x
   *   (and then later...)
   *   ASSERT  BIG FORMULA
   *
   * With the first assert, BIG FORMULA is clausified, and a literal
   * is assigned for the top level so that the final clause for the
   * implication is "lit => x".  But without "fortunate literal
   * detection," when BIG FORMULA is later asserted, it is clausified
   * separately, and "lit" is never asserted as a unit clause.
   */
  // KEEP_STATISTIC(IntStat, d_fortunateLiterals,
  //               "prop::CnfStream::fortunateLiterals", 0);

  /** Remove nots from the node */
  TNode stripNot(TNode node) {
    while (node.getKind() == kind::NOT) {
      node = node[0];
    }
    return node;
  }

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
   */
  void assertClause(TNode node, SatClause& clause);

  /**
   * Asserts the unit clause to the sat solver.
   * @param node the node giving rise to this clause
   * @param a the unit literal of the clause
   */
  void assertClause(TNode node, SatLiteral a);

  /**
   * Asserts the binary clause to the sat solver.
   * @param node the node giving rise to this clause
   * @param a the first literal in the clause
   * @param b the second literal in the clause
   */
  void assertClause(TNode node, SatLiteral a, SatLiteral b);

  /**
   * Asserts the ternary clause to the sat solver.
   * @param node the node giving rise to this clause
   * @param a the first literal in the clause
   * @param b the second literal in the clause
   * @param c the thirs literal in the clause
   */
  void assertClause(TNode node, SatLiteral a, SatLiteral b, SatLiteral c);

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

 public:
  /**
   * Constructs a CnfStream that sends constructs an equi-satisfiable
   * set of clauses and sends them to the given sat solver. This does not take
   * ownership of satSolver, registrar, or context.
   * @param satSolver the sat solver to use.
   * @param registrar the entity that takes care of preregistration of Nodes.
   * @param context the context that the CNF should respect.
   * @param fullLitToNodeMap maintain a full SAT-literal-to-Node mapping.
   * @param name string identifier to distinguish between different instances
   * even for non-theory literals.
   */
  CnfStream(SatSolver* satSolver, Registrar* registrar,
            context::Context* context, bool fullLitToNodeMap = false,
            std::string name = "");

  /**
   * Destructs a CnfStream.  This implementation does nothing, but we
   * need a virtual destructor for safety in case subclasses have a
   * destructor.
   */
  virtual ~CnfStream() {}

  /**
   * Converts and asserts a formula.
   * @param node node to convert and assert
   * @param removable whether the sat solver can choose to remove the clauses
   * @param negated whether we are asserting the node negated
   */
  virtual void convertAndAssert(TNode node, bool removable, bool negated,
                                ProofRule proof_id,
                                TNode from = TNode::null()) = 0;

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
  virtual void ensureLiteral(TNode n, bool noPreregistration = false) = 0;

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

  const NodeToLiteralMap& getTranslationCache() const {
    return d_nodeToLiteralMap;
  }

  const LiteralToNodeMap& getNodeCache() const { return d_literalToNodeMap; }

  void setProof(CnfProof* proof);
}; /* class CnfStream */

/**
 * TseitinCnfStream is based on the following recursive algorithm
 * http://people.inf.ethz.ch/daniekro/classes/251-0247-00/f2007/readings/Tseitin70.pdf
 * The general idea is to introduce a new literal that
 * will be equivalent to each subexpression in the constructed equi-satisfiable
 * formula, then substitute the new literal for the formula, and so on,
 * recursively.
 *
 * This implementation does this in a single recursive pass. [??? -Chris]
 */
class TseitinCnfStream : public CnfStream {
 public:
  /**
   * Constructs the stream to use the given sat solver.  This does not take
   * ownership of satSolver, registrar, or context.
   * @param satSolver the sat solver to use
   * @param registrar the entity that takes care of pre-registration of Nodes
   * @param context the context that the CNF should respect.
   * @param fullLitToNodeMap maintain a full SAT-literal-to-Node mapping,
   * even for non-theory literals
   */
  TseitinCnfStream(SatSolver* satSolver, Registrar* registrar,
                   context::Context* context, bool fullLitToNodeMap = false,
                   std::string name = "");

  /**
   * Convert a given formula to CNF and assert it to the SAT solver.
   * @param node the formula to assert
   * @param removable is this something that can be erased
   * @param negated true if negated
   */
  void convertAndAssert(TNode node, bool removable, bool negated,
                        ProofRule rule, TNode from = TNode::null());

 private:
  /**
   * Same as above, except that removable is remembered.
   */
  void convertAndAssert(TNode node, bool negated);

  // Each of these formulas handles takes care of a Node of each Kind.
  //
  // Each handleX(Node &n) is responsible for:
  //   - constructing a new literal, l (if necessary)
  //   - calling registerNode(n,l)
  //   - adding clauses assure that l is equivalent to the Node
  //   - calling toCNF on its children (if necessary)
  //   - returning l
  //
  // handleX( n ) can assume that n is not in d_translationCache
  SatLiteral handleNot(TNode node);
  SatLiteral handleXor(TNode node);
  SatLiteral handleImplies(TNode node);
  SatLiteral handleIff(TNode node);
  SatLiteral handleIte(TNode node);
  SatLiteral handleAnd(TNode node);
  SatLiteral handleOr(TNode node);

  void convertAndAssertAnd(TNode node, bool negated);
  void convertAndAssertOr(TNode node, bool negated);
  void convertAndAssertXor(TNode node, bool negated);
  void convertAndAssertIff(TNode node, bool negated);
  void convertAndAssertImplies(TNode node, bool negated);
  void convertAndAssertIte(TNode node, bool negated);

  /**
   * Transforms the node into CNF recursively.
   * @param node the formula to transform
   * @param negated whether the literal is negated
   * @return the literal representing the root of the formula
   */
  SatLiteral toCNF(TNode node, bool negated = false);

  void ensureLiteral(TNode n, bool noPreregistration = false);

}; /* class TseitinCnfStream */

} /* CVC4::prop namespace */
} /* CVC4 namespace */

#endif /* __CVC4__PROP__CNF_STREAM_H */
