/*********************                                                        */
/*! \file solver_state.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sets state object
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__SETS__THEORY_SOLVER_STATE_H
#define CVC4__THEORY__SETS__THEORY_SOLVER_STATE_H

#include <map>
#include <vector>

#include "context/cdhashset.h"
#include "theory/sets/skolem_cache.h"
#include "theory/theory_state.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace sets {

class TheorySetsPrivate;

/** Sets state
 *
 * The purpose of this class is to:
 * (1) Maintain information concerning the current set of assertions during a
 * full effort check,
 * (2) Maintain a database of commonly used terms.
 *
 * During a full effort check, the solver for theory of sets should call:
 *   reset; ( registerEqc | registerTerm )*
 * to initialize the information in this class regarding full effort checks.
 * Other query calls are then valid for the remainder of the full effort check.
 */
class SolverState : public TheoryState
{
  typedef context::CDHashMap<Node, Node, NodeHashFunction> NodeMap;

 public:
  SolverState(context::Context* c, context::UserContext* u, Valuation val);
  //-------------------------------- initialize per check
  /** reset, clears the data structures maintained by this class. */
  void reset();
  /** register term n of type tnn in the equivalence class of r */
  void registerTerm(Node r, TypeNode tnn, Node n);
  //-------------------------------- end initialize per check
  /** add equality to explanation
   *
   * This adds a = b to exp if a and b are syntactically disequal. The equality
   * a = b should hold in the current context.
   */
  void addEqualityToExp(Node a, Node b, std::vector<Node>& exp) const;
  /** Is formula n entailed to have polarity pol in the current context? */
  bool isEntailed(Node n, bool pol) const;
  /**
   * Is the disequality between sets s and t entailed in the current context?
   */
  bool isSetDisequalityEntailed(Node s, Node t) const;
  /** Get (positive) members of the set equivalence class r
   *
   * The members are return as a map, which maps members to their explanation.
   * For example, if x = y, (member 5 y), (member 6 x), then getMembers(x)
   * returns the map [ 5 -> (member 5 y), 6 -> (member 6 x)].
   */
  const std::map<Node, Node>& getMembers(Node r) const;
  /** Get negative members of the set equivalence class r, similar to above */
  const std::map<Node, Node>& getNegativeMembers(Node r) const;
  /** Is the (positive) members list of set equivalence class r non-empty? */
  bool hasMembers(Node r) const;
 private:
  /** constants */
  Node d_true;
  Node d_false;
  /** Pointer to the parent theory of sets */
  TheorySetsPrivate* d_parent;
  /** polarity memberships
   *
   * d_pol_mems[0] maps equivalence class to their positive membership list
   * with explanations (see getMembers), d_pol_mems[1] maps equivalence classes
   * to their negative memberships.
   */
  std::map<Node, std::map<Node, Node> > d_pol_mems[2];
  /** is set disequality entailed internal
   *
   * This returns true if disequality between sets a and b is entailed in the
   * current context. We use an incomplete test based on equality and membership
   * information.
   *
   * re is the representative of the equivalence class of the empty set
   * whose type is the same as a and b.
   */
  bool isSetDisequalityEntailedInternal(Node a, Node b, Node re) const;
  /**
   * Get members internal, returns the positive members if i=0, or negative
   * members if i=1.
   */
  const std::map<Node, Node>& getMembersInternal(Node r, unsigned i) const;
}; /* class TheorySetsPrivate */

}  // namespace sets
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__SETS__THEORY_SOLVER_STATE_H */
