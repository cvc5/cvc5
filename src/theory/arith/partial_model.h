
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
    delete dq;
  }
};

struct AssignmentAttrID {};
typedef expr::Attribute<AssignmentAttrID,
                        DeltaRational*,
                        DeltaRationalCleanupStrategy> Assignment;

/**
 * This defines a context dependent delta rational map.
 * This is used to keep track of the current lower and upper bounds on
 * each variable.  This information is conext dependent.
 */
typedef context::CDMap<TNode, DeltaRational, TNodeHashFunction> CDDRationalMap;
/* Side disucssion for why new tables are introduced instead of using the attribute
 * framework.
 * It comes down to that the obvious ways to use the current attribute framework do
 * do not provide a terribly satisfying answer.
 * - Suppose the type of the attribute is CD and maps to type DeltaRational.
 *   Well it can't map to a DeltaRational, and it thus it will be a DeltaRational*
 *   However being context dependent means givening up cleanup functions.
 *   So this leaks memory.
 * - Suppose the type of the attribute is CD and the type mapped to
 *   was a Node wrapping a CONST_DELTA_RATIONAL.
 *   This was rejected for inefficiency, and uglyness.
 *   Inefficiency: Every lookup and comparison will require going through the
 *   massaging in between a node and the constant being wrapped. Every update
 *   requires going through the additional expense of creating at least 1 node.
 *   The Uglyness: If this was chosen it would also suggest using comparisons against
 *   DeltaRationals for the tracking the constraints for conflict analysis.
 *   This seems to invite misuse and introducing Nodes that should probably not escape
 *   arith.
 * - Suppose that the of the attribute was not CD and mapped to a CDO<DeltaRational*>
 *   or similarly a ContextObj that wraps a DeltaRational*.
 *   This is currently rejected just because this is difficult to get right,
 *   and maintain. However with enough effort this the best solution is probably of
 *   this form.
 */


/**
 * This is the literal that was asserted in the current context to the theory
 * that asserted the tightest lower bound on a variable.
 * For example: for a variable x this could be the constraint (>= x 4) or (not (<= x 50))
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

  typedef std::pair<TNode, DeltaRational> HistoryPair;
  typedef std::deque< HistoryPair > HistoryStack;

  HistoryStack d_history;

  bool d_savingAssignments;

public:

  ArithPartialModel(context::Context* c):
    d_LowerBoundMap(c),
    d_UpperBoundMap(c),
    d_history(),
    d_savingAssignments(false)
  { }

  void setLowerConstraint(TNode x, TNode constraint);
  void setUpperConstraint(TNode x, TNode constraint);
  TNode getLowerConstraint(TNode x);
  TNode getUpperConstraint(TNode x);


  void beginRecordingAssignments();

  /* */
  void stopRecordingAssignments(bool revert);
  bool isRecording() { return d_savingAssignments;  }

  void setUpperBound(TNode x, const DeltaRational& r);
  void setLowerBound(TNode x, const DeltaRational& r);
  void setAssignment(TNode x, const DeltaRational& r);

  /** Must know that the bound exists before calling this! */
  DeltaRational getUpperBound(TNode x) const;
  DeltaRational getLowerBound(TNode x) const;
  DeltaRational getAssignment(TNode x) const;


  /**
   * x <= l
   * ? c < l
   */
  bool belowLowerBound(TNode x, DeltaRational& c, bool strict);

  /**
   * x <= u
   * ? c < u
   */
  bool aboveUpperBound(TNode x, DeltaRational& c, bool strict);

  bool strictlyBelowUpperBound(TNode x);
  bool strictlyAboveLowerBound(TNode x);
  bool assignmentIsConsistent(TNode x);

  void printModel(TNode x);

  void initialize(TNode x, const DeltaRational& r);
  
  DeltaRational getSavedAssignment(TNode x) const;

};




}; /* namesapce arith */
}; /* namespace theory */
}; /* namespace CVC4 */



#endif /* __CVC4__THEORY__ARITH__PARTIAL_MODEL_H */
