/*********************                                                        */
/*! \file transition_inference.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utility for inferring whether a synthesis conjecture encodes a
 ** transition system.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__TRANSITION_INFERENCE_H
#define CVC4__THEORY__QUANTIFIERS__TRANSITION_INFERENCE_H

#include <map>
#include <vector>

#include "expr/node.h"

#include "theory/quantifiers/cegqi/inst_strategy_cegqi.h"
#include "theory/quantifiers/inst_match_trie.h"
#include "theory/quantifiers/single_inv_partition.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/**
 * Utility for storing a deterministic trace of a transition system. A trace
 * is stored as a collection of vectors of values that have been taken by
 * the variables of transition system. For example, say we have a transition
 * system with variables x,y,z. Say the precondition constrains these variables
 * to x=1,y=2,z=3, and say that the transition relation admits the single
 * trace: [1,2,3], [2,3,4], [3,4,5]. We store these three vectors of variables
 * in the trie within this class.
 *
 * This utility is used for determining whether a transition system has a
 * deterministic terminating trace and hence a trivial invariant.
 */
class DetTrace
{
 public:
  /** The current value of the trace */
  std::vector<Node> d_curr;
  /**
   * Increment the trace: index the current values, if successful (they are
   * not a duplicate of a previous value), update the current values to vals.
   * Returns true if the increment was successful.
   */
  bool increment(Node loc, std::vector<Node>& vals);
  /**
   * Construct the formula that this trace represents with respect to variables
   * in vars. For details, see DetTraceTrie::constructFormula below.
   */
  Node constructFormula(const std::vector<Node>& vars);
  /** Debug print this trace on trace message c */
  void print(const char* c) const;

 private:
  /**
   * A trie of value vectors for the variables of a transition system. Nodes
   * are stored as data in tries with no children at the leaves of this trie.
   */
  class DetTraceTrie
  {
   public:
    /** the children of this trie */
    std::map<Node, DetTraceTrie> d_children;
    /** Add data loc to this trie, indexed by val. */
    bool add(Node loc, const std::vector<Node>& val);
    /** clear the trie */
    void clear() { d_children.clear(); }
    /**
     * Construct the formula corresponding to this trie with respect to
     * variables in vars. For example, if we have indexed [1,2,3] and [2,3,4]
     * and vars is [x,y,z], then this method returns:
     *   ( x=1 ^ y=2 ^ z=3 ) V ( x=2 ^ y=3 ^ z=4 ).
     */
    Node constructFormula(const std::vector<Node>& vars, unsigned index = 0);
  };
  /** The above trie data structure for this class */
  DetTraceTrie d_trie;
};

/**
 * Trace increment status, used for incrementTrace below.
 */
enum TraceIncStatus
{
  // the trace was successfully incremented to a new value
  TRACE_INC_SUCCESS,
  // the trace terminated
  TRACE_INC_TERMINATE,
  // the trace encountered a bad state (violating the post-condition)
  TRACE_INC_CEX,
  // the trace was invalid
  TRACE_INC_INVALID
};

/**
 * This class is used for inferring that an arbitrary synthesis conjecture
 * corresponds to an invariant synthesis problem for some predicate (d_func).
 *
 * The invariant-to-synthesize can either be explicitly given, via a call
 * to initialize( f, vars ), or otherwise inferred if this method is not called.
 */
class TransitionInference
{
 public:
  TransitionInference() : d_complete(false) {}
  /** Process the conjecture n
   *
   * This initializes this class with information related to viewing it as a
   * transition system. This means we infer a function, the state variables,
   * the pre/post condition and transition relation.
   *
   * The node n should be the inner body of the negated synthesis conjecture,
   * prior to generating the deep embedding. That is, given:
   *   forall f. ~forall x. P( f, x ),
   * this method expects n to be P( f, x ), and the argument f to be the
   * function f above.
   */
  void process(Node n, Node f);
  /**
   * Same as above, without specifying f. This will try to infer a function f
   * based on the body of n.
   */
  void process(Node n);
  /**
   * Get the function that is the subject of the synthesis problem we are
   * analyzing.
   */
  Node getFunction() const;
  /**
   * Get the variables that the function is applied to. These are the free
   * variables of the pre/post condition, and transition relation. These are
   * fresh (Skolem) variables allocated by this class.
   */
  void getVariables(std::vector<Node>& vars) const;
  /**
   * Get the pre/post condition, or transition relation that was inferred by
   * this class.
   */
  Node getPreCondition() const;
  Node getPostCondition() const;
  Node getTransitionRelation() const;
  /**
   * Was the analysis of the conjecture complete?
   *
   * If this is false, then the system we have inferred does not take into
   * account all of the synthesis conjecture. This is the case when process(...)
   * was called on formula that does not have the shape of a transition system.
   */
  bool isComplete() const { return d_complete; }

  /**
   * The following two functions are used for computing whether this transition
   * relation is deterministic and terminating.
   *
   * The argument fwd is whether we are going in the forward direction of the
   * transition system (starting from the precondition).
   *
   * If fwd is true, the initializeTrace method returns TRACE_INC_SUCCESS if the
   * precondition consists of a single conjunct of the form
   *   ( x1 = t1 ^ ... ^ xn = tn )
   * where x1...xn are the state variables of the transition system. Otherwise
   * it returns TRACE_INC_INVALID.
   */
  TraceIncStatus initializeTrace(DetTrace& dt, bool fwd = true);
  /**
   * Increment the trace dt in direction fwd.
   *
   * If fwd is true, the incrementTrace method returns TRACE_INC_INVALID if the
   * transition relation is not of the form
   *   ( x1' = t1[X] ^ ... ^ xn' = tn[X] ^ Q[X] ^ P(x1...xn) ) => P( x1'...xn' )
   * Otherwise, it returns TRACE_INC_TERMINATE if the values of
   * x1' = t1[dt.d_curr] ^ ... ^ xn' = tn[dt.d_curr] have already been executed
   * on trace dt (the trace has looped), or if
   * x1' = t1[dt.d_curr] ^ ... ^ xn' = tn[dt.d_curr] ^ Q[dt.d_curr] is unsat
   * (the trace has terminated). It returns TRACE_INC_CEX if the postcondition
   * is false for the values t1[dt.d_curr] ^ ... ^ tn[dt.d_curr]. Otherwise,
   * it returns TRACE_INC_SUCCESS.
   */
  TraceIncStatus incrementTrace(DetTrace& dt, bool fwd = true);
  /**
   * Constructs the formula corresponding to trace dt with respect to the
   * variables of this class.
   */
  Node constructFormulaTrace(DetTrace& dt) const;

 private:
  /**
   * The function (predicate) that is the subject of the invariant synthesis
   * problem we are inferring.
   */
  Node d_func;
  /** The variables that the function is applied to */
  std::vector<Node> d_vars;
  /**
   * The variables that the function is applied to in the next state of the
   * inferred transition relation.
   */
  std::vector<Node> d_prime_vars;
  /**
   * Was the analysis of the synthesis conjecture passed to the process method
   * of this class complete?
   */
  bool d_complete;

  /** process disjunct
   *
   * The purpose of this function is to infer pre/post/transition conditions
   * for a (possibly unknown) invariant-to-synthesis, given a conjunct from
   * an arbitrary synthesis conjecture.
   *
   * Assume our negated synthesis conjecture is of the form:
   *    forall f. exists x. (and (or F11 ... F1{m_1}) ... (or Fn1 ... Fn{m_n}))
   * This method is called on each (or Fi1 ... Fi{m_i}), where topLevel is true
   * for each of Fi1...F1{m_i} and false otherwise. It adds each of Fi1..Fi{m_i}
   * to disjuncts.
   *
   * If this method returns true, then (1) all applications of free function
   * symbols have operator d_func. Note this function may set d_func to a
   * function symbol in n if d_func was null prior to this call. In other words,
   * this method may infer the subject of the invariant synthesis problem;
   * (2) all occurrences of d_func are "top-level", that is, each Fij may be
   * of the form (not) <d_func>( tj ), but otherwise d_func does not occur in
   * (or Fi1 ... Fi{m_i}); (3) there exists at most one occurrence of
   * <d_func>( tj ), and (not <d_func>( tk )).
   *
   * If the above conditions are met, then terms[true] is set to <d_func>( tj )
   * if Fij is <d_func>( tj ) for some j, and likewise terms[false]
   * is set to <d_func>( tk ) if Fik is (not <d_func>( tk )) for some k.
   *
   * The argument visited caches the results of this function for (topLevel, n).
   */
  bool processDisjunct(Node n,
                       std::map<bool, Node>& terms,
                       std::vector<Node>& disjuncts,
                       std::map<bool, std::map<Node, bool> >& visited,
                       bool topLevel);
  /**
   * This method infers if the conjunction of disjuncts is equivalent to a
   * conjunction of the form
   *   (~) const_var[1] = const_subs[1] ... (~) const_var[n] = const_subs[n]
   * where the above equalities are negated iff reqPol is false, and
   *   const_var[1] ... const_var[n]
   * are distinct members of vars
   */
  void getConstantSubstitution(const std::vector<Node>& vars,
                               const std::vector<Node>& disjuncts,
                               std::vector<Node>& const_var,
                               std::vector<Node>& const_subs,
                               bool reqPol);
  /** get normalized substitution
   *
   * This method takes as input a node curr of the form I( t1, ..., tn ) and
   * a vector of variables pvars, where pvars.size()=n. For each ti that is
   * a variable, it adds ti to vars, and pvars[i] to subs. For each ti that is
   * not a variable, it adds the disequality ti != pvars[i] to disjuncts.
   *
   * This function is used for instance to normalize an arbitrary application of
   * I so that is over arguments pvars. For instance if curr is I(3,5,y) and
   * pvars = { x1,x2,x3 }, then the formula:
   *   I(3,5,y) ^ P(y)
   * is equivalent to:
   *   x1 != 3 V x2 != 5 V I(x1,x2,x3) V P( y ) { y -> x3 }
   * Here, we add y and x3 to vars and subs respectively, and x1!=3 and x2!=5
   * to disjuncts.
   */
  void getNormalizedSubstitution(Node curr,
                                 const std::vector<Node>& pvars,
                                 std::vector<Node>& vars,
                                 std::vector<Node>& subs,
                                 std::vector<Node>& disjuncts);
  /**
   * Stores one of the components of the inferred form of the synthesis
   * conjecture (precondition, postcondition, or transition relation).
   */
  class Component
  {
   public:
    Component() {}
    /** The formula that was inferred for this component */
    Node d_this;
    /** The list of conjuncts of the above formula */
    std::vector<Node> d_conjuncts;
    /**
     * Maps formulas to the constant equality substitution that it entails.
     * For example, the formula (x=4 ^ y=x+5) may map to { x -> 4, y -> 9 }.
     */
    std::map<Node, std::map<Node, Node> > d_const_eq;
    /** Does this component have conjunct c? */
    bool has(Node c) const
    {
      return std::find(d_conjuncts.begin(), d_conjuncts.end(), c)
             != d_conjuncts.end();
    }
  };
  /** Components for the pre/post condition and transition relation. */
  Component d_pre;
  Component d_post;
  Component d_trans;
  /**
   * Initialize trace dt, loc is a node to identify the trace, fwd is whether
   * we are going in the forward direction of the transition system (starting
   * from the precondition).
   *
   * The argument loc is a conjunct of transition relation that entails that the
   * trace dt has executed in its last step to its current value. For example,
   * if the transition relation is ( x'=x+1 ^ P( x ) ) => P(x'), and our trace's
   * current value was last updated [x:=1] -> [x:=2] based on x'=x+1, then loc
   * is the node x'=x+1.
   */
  TraceIncStatus initializeTrace(DetTrace& dt, Node loc, bool fwd = true);
  /** Same as above, for incrementing the trace dt */
  TraceIncStatus incrementTrace(DetTrace& dt, Node loc, bool fwd = true);
};

}  // namespace quantifiers
}  // namespace theory
} /* namespace CVC4 */

#endif
