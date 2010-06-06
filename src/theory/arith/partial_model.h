/*********************                                                        */
/*! \file partial_model.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/


#include "context/context.h"
#include "context/cdmap.h"
#include "theory/arith/delta_rational.h"
#include "expr/attribute.h"
#include "expr/node.h"

#include <deque>

#ifndef __CVC4__THEORY__ARITH__PARTIAL_MODEL_H
#define __CVC4__THEORY__ARITH__PARTIAL_MODEL_H

namespace CVC4 {
namespace theory {
namespace arith {

namespace partial_model {
struct DeltaRationalCleanupStrategy{
  static void cleanup(DeltaRational* dq){
    Debug("arithgc") << "cleaning up  " << dq << "\n";
    if(dq != NULL){
      delete dq;
    }
  }
};

struct AssignmentAttrID {};
typedef expr::Attribute<AssignmentAttrID,
                        DeltaRational*,
                        DeltaRationalCleanupStrategy> Assignment;


struct SafeAssignmentAttrID {};
typedef expr::Attribute<SafeAssignmentAttrID,
                        DeltaRational*,
                        DeltaRationalCleanupStrategy> SafeAssignment;

/**
 * This defines a context dependent delta rational map.
 * This is used to keep track of the current lower and upper bounds on
 * each variable.  This information is conext dependent.
 */
typedef context::CDMap<TNode, DeltaRational, TNodeHashFunction> CDDRationalMap;
/* Side disucssion for why new tables are introduced instead of using the
 * attribute framework.
 * It comes down to that the obvious ways to use the current attribute
 * framework do not provide a terribly satisfying answer.
 * - Suppose the type of the attribute is CD and maps to type DeltaRational.
 *   Well it can't map to a DeltaRational, and it thus it will be a
 *   DeltaRational*
 *   However being context dependent means givening up cleanup functions.
 *   So this leaks memory.
 * - Suppose the type of the attribute is CD and the type mapped to
 *   was a Node wrapping a CONST_DELTA_RATIONAL.
 *   This was rejected for inefficiency, and uglyness.
 *   Inefficiency: Every lookup and comparison will require going through the
 *   massaging in between a node and the constant being wrapped. Every update
 *   requires going through the additional expense of creating at least 1 node.
 *   The Uglyness: If this was chosen it would also suggest using comparisons
 *   against DeltaRationals for the tracking the constraints for conflict
 *   analysis. This seems to invite misuse and introducing Nodes that should
 *   probably not escape arith.
 * - Suppose that the of the attribute was not CD and mapped to a
 *   CDO<DeltaRational*> or similarly a ContextObj that wraps a DeltaRational*.
 *   This is currently rejected just because this is difficult to get right,
 *   and maintain. However with enough effort this the best solution is
 *   probably of this form.
 */


/**
 * This is the literal that was asserted in the current context to the theory
 * that asserted the tightest lower bound on a variable.
 * For example: for a variable x this could be the constraint
 *    (>= x 4) or (not (<= x 50))
 * Note the strong correspondence between this and LowerBoundMap.
 * This is used during conflict analysis.
 */
struct LowerConstraintAttrID {};
typedef expr::CDAttribute<LowerConstraintAttrID,TNode> LowerConstraint;

/**
 * See the documentation for LowerConstraint.
 */
struct UpperConstraintAttrID {};
typedef expr::CDAttribute<UpperConstraintAttrID,TNode> UpperConstraint;


}; /*namespace partial_model*/


struct TheoryArithPropagatedID {};
typedef expr::CDAttribute<TheoryArithPropagatedID, bool> TheoryArithPropagated;



class ArithPartialModel {
private:
  partial_model::CDDRationalMap d_LowerBoundMap;
  partial_model::CDDRationalMap d_UpperBoundMap;


  /**
   * List contains all of the variables that have an unsafe assignment.
   */
  typedef std::vector<TNode> HistoryList;
  HistoryList d_history;

public:

  ArithPartialModel(context::Context* c):
    d_LowerBoundMap(c),
    d_UpperBoundMap(c),
    d_history()
  { }

  void setLowerConstraint(TNode x, TNode constraint);
  void setUpperConstraint(TNode x, TNode constraint);
  TNode getLowerConstraint(TNode x);
  TNode getUpperConstraint(TNode x);



  /* Initializes a variable to a safe value.*/
  void initialize(TNode x, const DeltaRational& r);

  /* Gets the last assignment to a variable that is known to be conistent. */
  DeltaRational getSafeAssignment(TNode x) const;

  /* Reverts all variable assignments to their safe values. */
  void revertAssignmentChanges();

  /* Commits all variables assignments as safe.*/
  void commitAssignmentChanges();



  void setUpperBound(TNode x, const DeltaRational& r);
  void setLowerBound(TNode x, const DeltaRational& r);

  /* Sets an unsafe variable assignment */
  void setAssignment(TNode x, const DeltaRational& r);

  /** Must know that the bound exists before calling this! */
  DeltaRational getUpperBound(TNode x) const;
  DeltaRational getLowerBound(TNode x) const;
  const DeltaRational& getAssignment(TNode x) const;


  /**
   * x <= l
   * ? c < l
   */
  bool belowLowerBound(TNode x, const DeltaRational& c, bool strict);

  /**
   * x <= u
   * ? c < u
   */
  bool aboveUpperBound(TNode x, const DeltaRational& c, bool strict);

  bool strictlyBelowUpperBound(TNode x);
  bool strictlyAboveLowerBound(TNode x);
  bool assignmentIsConsistent(TNode x);

  void printModel(TNode x);

private:

  /**
   * This function implements the mostly identical:
   * revertAssignmentChanges() and commitAssignmentChanges().
   */
  void clearSafeAssignments(bool revert);
};




}; /* namesapce arith */
}; /* namespace theory */
}; /* namespace CVC4 */



#endif /* __CVC4__THEORY__ARITH__PARTIAL_MODEL_H */
