/*********************                                                        */
/*! \file sygus_unif_io.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner, Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief sygus_unif_io
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__SYGUS_UNIF_IO_H
#define CVC4__THEORY__QUANTIFIERS__SYGUS_UNIF_IO_H

#include <map>
#include "theory/quantifiers/sygus/sygus_unif.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class SygusUnifIo;

/** Unification context
  *
  * This class maintains state information during calls to
  * SygusUnifIo::constructSolution, which implements unification-based
  * approaches for constructing solutions to synthesis conjectures.
  */
class UnifContextIo : public UnifContext
{
 public:
  UnifContextIo();
  /** get current role */
  NodeRole getCurrentRole() override;

  /**
   * This intiializes this context based on information in sui regarding the
   * kinds of examples it contains.
   */
  void initialize(SygusUnifIo* sui);

  //----------for ITE strategy
  /** the value of the context conditional
  *
  * This stores a list of Boolean constants that is the same length of the
  * number of input/output example pairs we are considering. For each i,
  * if d_vals[i] = true, i/o pair #i is active according to this context
  * if d_vals[i] = false, i/o pair #i is inactive according to this context
  */
  std::vector<Node> d_vals;
  /** update the examples
  *
  * if pol=true, this method updates d_vals to d_vals & vals
  * if pol=false, this method updates d_vals to d_vals & ( ~vals )
  */
  bool updateContext(SygusUnifIo* sui, std::vector<Node>& vals, bool pol);
  //----------end for ITE strategy

  //----------for CONCAT strategies
  /** the position in the strings
  *
  * For each i/o example pair, this stores the length of the current solution
  * for the input of the pair, where the solution for that input is a prefix
  * or
  * suffix of the output of the pair. For example, if our i/o pairs are:
  *   f( "abcd" ) = "abcdcd"
  *   f( "aa" ) = "aacd"
  * If the solution we have currently constructed is str.++( x1, "c", ... ),
  * then d_str_pos = ( 5, 3 ), where notice that
  *   str.++( "abc", "c" ) is a prefix of "abcdcd" and
  *   str.++( "aa", "c" ) is a prefix of "aacd".
  */
  std::vector<unsigned> d_str_pos;
  /** update the string examples
  *
  * This method updates d_str_pos to d_str_pos + pos, and updates the current
  * role to nrole.
  */
  bool updateStringPosition(SygusUnifIo* sui,
                            std::vector<size_t>& pos,
                            NodeRole nrole);
  /** get current strings
  *
  * This returns the prefix/suffix of the string constants stored in vals
  * of size d_str_pos, and stores the result in ex_vals. For example, if vals
  * is (abcdcd", "aacde") and d_str_pos = ( 5, 3 ), then we add
  * "d" and "de" to ex_vals.
  */
  void getCurrentStrings(SygusUnifIo* sui,
                         const std::vector<Node>& vals,
                         std::vector<Node>& ex_vals);
  /** get string increment
  *
  * If this method returns true, then inc and tot are updated such that
  *   for all active indices i,
  *      vals[i] is a prefix (or suffix if isPrefix=false) of ex_vals[i], and
  *      inc[i] = str.len(vals[i])
  *   for all inactive indices i, inc[i] = 0
  * We set tot to the sum of inc[i] for i=1,...,n. This indicates the total
  * number of characters incremented across all examples.
  */
  bool getStringIncrement(SygusUnifIo* sui,
                          bool isPrefix,
                          const std::vector<Node>& ex_vals,
                          const std::vector<Node>& vals,
                          std::vector<size_t>& inc,
                          size_t& tot);
  /** returns true if ex_vals[i] = vals[i] for all active indices i. */
  bool isStringSolved(SygusUnifIo* sui,
                      const std::vector<Node>& ex_vals,
                      const std::vector<Node>& vals);
  //----------end for CONCAT strategies

  /** visited role
  *
  * This is the current set of enumerator/node role pairs we are currently
  * visiting. This set is cleared when the context is updated.
  */
  std::map<Node, std::map<NodeRole, bool>> d_visit_role;

 private:
  /** true and false nodes */
  Node d_true;
  Node d_false;
  /** current role (see getCurrentRole). */
  NodeRole d_curr_role;
};

/** Subsumption trie
*
* This class manages a set of terms for a PBE sygus enumerator.
*
* In PBE sygus, we are interested in, for each term t, the set of I/O examples
* that it satisfies, which can be represented by a vector of Booleans.
* For example, given conjecture:
*   f( 1 ) = 2 ^ f( 3 ) = 4 ^ f( -1 ) = 1 ^ f( 5 ) = 5
* If solutions for f are of the form (lambda x. [term]), then:
*   Term x satisfies 0001,
*   Term x+1 satisfies 1100,
*   Term 2 satisfies 0100.
* Above, term 2 is subsumed by term x+1, since the set of I/O examples that
* x+1 satisfies are a superset of those satisfied by 2.
*/
class SubsumeTrie
{
 public:
  SubsumeTrie() {}
  /**
  * Adds term t to the trie, removes all terms that are subsumed by t from the
  * trie and adds them to subsumed. The set of I/O examples that t satisfies
  * is given by (pol ? vals : !vals).
  */
  Node addTerm(Node t,
               const std::vector<Node>& vals,
               bool pol,
               std::vector<Node>& subsumed);
  /**
  * Adds term c to the trie, without calculating/updating based on
  * subsumption. This is useful for using this class to store conditionals
  * in ITE strategies, where any conditional whose set of vals is unique
  * (as opposed to not subsumed) is useful.
  */
  Node addCond(Node c, const std::vector<Node>& vals, bool pol);
  /**
    * Returns the set of terms that are subsumed by (pol ? vals : !vals).
    */
  void getSubsumed(const std::vector<Node>& vals,
                   bool pol,
                   std::vector<Node>& subsumed);
  /**
    * Returns the set of terms that subsume (pol ? vals : !vals). This
    * is for instance useful when determining whether there exists a term
    * that satisfies all active examples in the decision tree learning
    * algorithm.
    */
  void getSubsumedBy(const std::vector<Node>& vals,
                     bool pol,
                     std::vector<Node>& subsumed_by);
  /**
   * Get the leaves of the trie, which we store in the map v. We consider their
   * evaluation on points such that (pol ? vals : !vals) is true.
   *
   * v[-1] stores the children that always evaluate to !pol,
   * v[1] stores the children that always evaluate to pol,
   * v[0] stores the children that both evaluate to true and false for at least
   * one example.
   */
  void getLeaves(const std::vector<Node>& vals,
                 bool pol,
                 std::map<int, std::vector<Node>>& v);
  /** is this trie empty? */
  bool isEmpty() { return d_term.isNull() && d_children.empty(); }
  /** clear this trie */
  void clear()
  {
    d_term = Node::null();
    d_children.clear();
  }

 private:
  /** the term at this node */
  Node d_term;
  /** the children nodes of this trie */
  std::map<Node, SubsumeTrie> d_children;
  /** helper function for above functions */
  Node addTermInternal(Node t,
                       const std::vector<Node>& vals,
                       bool pol,
                       std::vector<Node>& subsumed,
                       bool spol,
                       unsigned index,
                       int status,
                       bool checkExistsOnly,
                       bool checkSubsume);
  /** helper function for above functions
   *
   * This adds to v[-1], v[0], v[1] the children of the trie that occur
   * along paths that contain only false (v[-1]), a mix of true/false (v[0]),
   * and only true (v[1]) values for respectively for relevant points.
   *
   * vals/pol is used to determine the relevant points, which impacts which
   * paths of the trie to traverse on this call.
   * In particular, all points such that (pol ? vals[index] : !vals[index])
   * are relevant.
   *
   * Paths that contain an unknown value for any relevant point are not
   * traversed. In the larger picture, this ensures that terms are not used in a
   * way such that their unknown value is relevant to the overall behavior of
   * a synthesis solution.
   *
   * status holds the current value of v (0,1,-1) that we will be adding to.
   */
  void getLeavesInternal(const std::vector<Node>& vals,
                         bool pol,
                         std::map<int, std::vector<Node>>& v,
                         unsigned index,
                         int status);
};

class SynthConjecture;

/** Sygus unification I/O utility
 *
 * This class implement synthesis-by-unification, where the specification is
 * I/O examples.
 *
 * Since I/O specifications for multiple functions can be fully separated, we
 * assume that this class is used only for a single function to synthesize.
 *
 * In addition to the base class which maintains a strategy tree, this class
 * maintains:
 * (1) A set of input/output examples that are the specification for f.
 * (2) A set of terms that have been enumerated for enumerators (d_ecache). This
 * can be updated via calls to notifyEnumeration.
 */
class SygusUnifIo : public SygusUnif
{
  friend class UnifContextIo;

 public:
  SygusUnifIo(SynthConjecture* p);
  ~SygusUnifIo();

  /** initialize
   *
   * This initializes this class for solving PBE conjectures for
   * function-to-synthesize f.
   *
   * We only initialize for one function f, since I/O specifications across
   * multiple functions can be separated.
   */
  void initializeCandidate(
      QuantifiersEngine* qe,
      Node f,
      std::vector<Node>& enums,
      std::map<Node, std::vector<Node>>& strategy_lemmas) override;
  /** Notify enumeration */
  void notifyEnumeration(Node e, Node v, std::vector<Node>& lemmas) override;

  /** Construct solution */
  bool constructSolution(std::vector<Node>& sols,
                         std::vector<Node>& lemmas) override;
 protected:
  /** The synthesis conjecture */
  SynthConjecture* d_parent;
  /** the function-to-synthesize */
  Node d_candidate;
  /**
   * Whether we will try to construct solution on the next call to
   * constructSolution. This flag is set to true when we successfully
   * register a new value for an enumerator.
   */
  bool d_check_sol;
  /** The number of values we have enumerated for all enumerators. */
  unsigned d_cond_count;
  /** The solution for the function of this class, if one has been found */
  Node d_solution;
  /** the term size of the above solution */
  unsigned d_sol_term_size;
  /** partial solutions
   *
   * Maps indices for I/O points to a list of solutions for that point, for each
   * type. We may have more than one type for solutions, e.g. for grammar:
   *   A -> ite( A, B, C ) | ...
   * where terms of type B and C can both act as solutions.
   */
  std::map<size_t,
           std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>>>
      d_psolutions;
  /**
   * This flag is set to true if the solution construction was
   * non-deterministic with respect to failure/success.
   *
   * The solution construction for the string concatenation strategy is
   * non-deterministic with respect to success/failure. That is, choosing
   * a particular string may lead to being unsolvable in the recursive calls,
   * whereas others may not. For example, if our pool of enumerated strings is:
   *   { "A", x, "B" }
   * and our I/O example is:
   *   f( "AC" ) = "ACB"
   * then choosing to consider a solution of the form ( "A" ++ _ ) leads
   * to a recursive call where we are solving for f' in:
   *   "A" ++ f'("AC") = "ACB"
   * which is unsolvable since we cannot generate a term starting with "C"
   * from the pool above. Whereas if we would have chosen ( x ++ _ ), this
   * leads to a recursive call where we are solving for f' in:
   *   "AC" ++ f'("AC") = "ACB"
   * which can be closed with "B", giving us (x ++ "B") as a solution.
   */
  bool d_sol_cons_nondet;
  /**
   * Whether we are using information gain heuristic during solution
   * construction.
   */
  bool d_solConsUsingInfoGain;
  /** true and false nodes */
  Node d_true;
  Node d_false;
  /** input of I/O examples */
  std::vector<std::vector<Node>> d_examples;
  /** output of I/O examples */
  std::vector<Node> d_examples_out;

  /**
  * This class stores information regarding an enumerator, including:
  * a database of values that have been enumerated for this enumerator.
  */
  class EnumCache
  {
   public:
    EnumCache() {}
    /**
    * Notify this class that the term v has been enumerated for this enumerator.
    * Its evaluation under the set of examples in sui are stored in results.
    */
    void addEnumValue(Node v, std::vector<Node>& results);
    /**
    * Notify this class that slv is the complete solution to the synthesis
    * conjecture. This occurs rarely, for instance, when during an ITE strategy
    * we find that a single enumerated term covers all examples.
    */
    void setSolved(Node slv) { d_enum_solved = slv; }
    /** Have we been notified that a complete solution exists? */
    bool isSolved() { return !d_enum_solved.isNull(); }
    /** Get the complete solution to the synthesis conjecture. */
    Node getSolved() { return d_enum_solved; }
    /** Values that have been enumerated for this enumerator */
    std::vector<Node> d_enum_vals;
    /**
      * This either stores the values of f( I ) for inputs
      * or the value of f( I ) = O if d_role==enum_io
      */
    std::vector<std::vector<Node>> d_enum_vals_res;
    /**
    * The set of values in d_enum_vals that have been "subsumed" by others
    * (see SubsumeTrie for explanation of subsumed).
    */
    std::vector<Node> d_enum_subsume;
    /** Map from values to their index in d_enum_vals. */
    std::map<Node, unsigned> d_enum_val_to_index;
    /**
    * A subsumption trie containing the values in d_enum_vals. Depending on the
    * role of this enumerator, values may either be added to d_term_trie with
    * subsumption (if role=enum_io), or without (if role=enum_ite_condition or
    * enum_concat_term).
    */
    SubsumeTrie d_term_trie;

   private:
    /**
      * Whether an enumerated value for this conjecture has solved the entire
      * conjecture.
      */
    Node d_enum_solved;
  };
  /** maps enumerators to the information above */
  std::map<Node, EnumCache> d_ecache;
  /** Construct solution node
   *
   * This is called for the (single) function-to-synthesize during a call to
   * constructSolution. If this returns a non-null node, then that term is a
   * solution for the function-to-synthesize in the overall conjecture.
   */
  Node constructSolutionNode(std::vector<Node>& lemmas);
  /** domain-specific enumerator exclusion techniques
   *
   * Returns true if the value v for e can be excluded based on a
   * domain-specific exclusion technique like the ones below.
   *
   * results : the values of v under the input examples,
   * exp : if this function returns true, then exp contains a (possibly
   * generalize) explanation for why v can be excluded.
   */
  bool getExplanationForEnumeratorExclude(
      Node e,
      Node v,
      std::vector<Node>& results,
      std::vector<Node>& exp);
  /** returns true if we can exlude values of e based on negative str.contains
   *
   * Values v for e may be excluded if we realize that the value of v under the
   * substitution for some input example will never be contained in some output
   * example. For details on this technique, see NegContainsSygusInvarianceTest
   * in sygus_invariance.h.
   *
   * This function depends on whether e is being used to enumerate values
   * for any node that is conditional in the strategy graph. For example,
   * nodes that are children of ITE strategy nodes are conditional. If any node
   * is conditional, then this function returns false.
   */
  bool useStrContainsEnumeratorExclude(Node e);
  /** cache for the above function */
  std::map<Node, bool> d_use_str_contains_eexc;
  /**
   * cache for the above function, stores whether enumerators e are in
   * a conditional context, e.g. used for enumerating the return values for
   * leaves of ITE trees.
   */
  std::map<Node, bool> d_use_str_contains_eexc_conditional;

  /** the unification context used within constructSolution */
  UnifContextIo d_context;
  /** initialize construct solution */
  void initializeConstructSol() override;
  /** initialize construct solution for */
  void initializeConstructSolFor(Node f) override;
  /** construct solution */
  Node constructSol(Node f,
                    Node e,
                    NodeRole nrole,
                    int ind,
                    std::vector<Node>& lemmas) override;
  /** construct best conditional
   *
   * This returns the condition in conds that maximizes information gain with
   * respect to the current active points in d_context. For example, see
   * Alur et al. TACAS 2017 for an example of information gain.
   */
  Node constructBestConditional(Node ce,
                                const std::vector<Node>& conds) override;
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* CVC4__THEORY__QUANTIFIERS__SYGUS_UNIF_IO_H */
