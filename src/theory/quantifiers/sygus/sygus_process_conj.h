/*********************                                                        */
/*! \file sygus_process_conj.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Techniqures for static preprocessing and analysis of
 ** sygus conjectures.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__SYGUS_PROCESS_CONJ_H
#define CVC4__THEORY__QUANTIFIERS__SYGUS_PROCESS_CONJ_H

#include <map>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "expr/node.h"
#include "expr/type_node.h"

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

namespace quantifiers {

/** This file contains techniques that compute
 * argument relevancy for synthesis functions
 *
 * Let F be a synthesis conjecture of the form:
 *   exists f. forall X. P( f, X )
 *
 * The classes below compute whether certain arguments of
 * the function-to-synthesize f are irrelevant.
 * Assume that f is a binary function, where possible solutions
 * to the above conjecture are of the form:
 *   f -> (lambda (xy) t[x,y])
 * We say e.g. that the 2nd argument of f is irrelevant if we
 * can determine:
 *   F has a solution
 * if and only if
 *   F has a solution of the form f -> (lambda (xy) t[x] )
 * We conclude that arguments are irrelevant using the following
 * techniques.
 *
 *
 * (1) Argument invariance:
 *
 * Let s[z] be a term whose free variables are contained in { z }.
 * If all occurrences of f-applications in F are of the form:
 *   f(t, s[t])
 * then:
 *   f = (lambda (xy) r[x,y])
 * is a solution to F only if:
 *   f = (lambda (xy) r[x,s[x]])
 * is as well.
 * Hence the second argument of f is not relevant.
 *
 *
 * (2) Variable irrelevance:
 *
 * If F is equivalent to:
 *   exists f. forall w z u1...un. C1 ^...^Cm,
 * where for i=1...m, Ci is of the form:
 *   ( w1 = f(tm1[z], u1) ^
 *     ... ^
 *     wn = f(tmn[z], un) ) => Pm(w1...wn, z)
 * then the second argument of f is irrelevant.
 * We call u1...un single occurrence variables
 * (in Ci).
 *
 *
 * TODO (#1210) others, generalize (2)?
 *
 */

/** This structure stores information regarding
 * an argument of a function to synthesize.
 *
 * It is used to store whether the argument
 * position in the function to synthesize is
 * relevant.
 */
class SynthConjectureProcessArg
{
 public:
  SynthConjectureProcessArg() : d_var_single_occ(false), d_relevant(false) {}
  /** template definition
   * This is the term s[z] described
   * under "Argument Invariance" above.
   */
  Node d_template;
  /** single occurrence
   * Whether we are trying to show this argument
   * is irrelevant by "Variable irrelevance"
   * described above.
   */
  bool d_var_single_occ;
  /** whether this argument is relevant
   * An argument is marked as relevant if:
   * (A) it is explicitly marked as relevant
   *     due to a function application containing
   *     a relevant term at this argument position, or
   * (B) if it is given conflicting template definitions.
   */
  bool d_relevant;
};

/** This structure stores information regarding conjecture-specific
* analysis of a single function to synthesize within
* a conjecture to synthesize.
*
* It maintains information about each of the function to
* synthesize's arguments.
*/
struct SynthConjectureProcessFun
{
 public:
  SynthConjectureProcessFun() {}
  ~SynthConjectureProcessFun() {}
  /** initialize this class for function f */
  void init(Node f);
  /** process terms
   *
   * This is called once per conjunction in
   * the synthesis conjecture.
   *
   * ns are the f-applications to process,
   * ks are the variables we introduced to flatten them,
   * nf is the flattened form of our conjecture to process,
   * free_vars maps all subterms of n and nf to the set
   *   of variables (in set synth_fv) they contain.
   *
   * This updates information regarding which arguments
   * of the function-to-synthesize are relevant.
   */
  void processTerms(
      std::vector<Node>& ns,
      std::vector<Node>& ks,
      Node nf,
      std::unordered_set<Node, NodeHashFunction>& synth_fv,
      std::unordered_map<Node,
                         std::unordered_set<Node, NodeHashFunction>,
                         NodeHashFunction>& free_vars);
  /** is the i^th argument of the function-to-synthesize of this class relevant?
   */
  bool isArgRelevant(unsigned i);
  /** get irrelevant arguments for the function-to-synthesize of this class */
  void getIrrelevantArgs(std::unordered_set<unsigned>& args);

 private:
  /** the synth fun associated with this */
  Node d_synth_fun;
  /** properties of each argument */
  std::vector<SynthConjectureProcessArg> d_arg_props;
  /** variables for each argument type of f
   *
   * These are used to express templates for argument
   * invariance, in the data member
   * SynthConjectureProcessArg::d_template.
   */
  std::vector<Node> d_arg_vars;
  /** map from d_arg_vars to the argument #
   * they represent.
   */
  std::unordered_map<Node, unsigned, NodeHashFunction> d_arg_var_num;
  /** check match
   * This function returns true iff we can infer:
   *   cn * { x -> n_arg_map[d_arg_var_num[x]] | x in d_arg_vars } = n
   * In other words, cn and n are equivalent
   * via the substitution mapping argument variables to terms
   * specified by n_arg_map. The rewriter is used for inferring
   * this equivalence.
   *
   * For example, if n_arg_map contains { 1 -> t, 2 -> s }, then
   *   checkMatch( x1+x2, t+s, n_arg_map ) returns true,
   *   checkMatch( x1+1, t+1, n_arg_map ) returns true,
   *   checkMatch( 0, 0, n_arg_map ) returns true,
   *   checkMatch( x1+1, s, n_arg_map ) returns false.
   */
  bool checkMatch(Node cn,
                  Node n,
                  std::unordered_map<unsigned, Node>& n_arg_map);
  /** infer definition
   *
   * In the following, we say a term is a "template
   * definition" if its free variables are a subset of d_arg_vars.
   *
   * If this function returns a non-null node ret, then
   *   checkMatch( ret, n, term_to_arg_carry^-1 ) returns true.
   * and ret is a template definition.
   *
   * The free variables for all subterms of n are stored in
   * free_vars. The map term_to_arg_carry is injective.
   *
   * For example, if term_to_arg_carry contains { t -> 1, s -> 2 } and
   * free_vars is { t -> {y}, r -> {y}, s -> {}, q -> {}, ... -> {} }, then
   *   inferDefinition( 0, term_to_arg_carry, free_vars )
   *     returns 0
   *   inferDefinition( t, term_to_arg_carry, free_vars )
   *     returns x1
   *   inferDefinition( t+s+q, term_to_arg_carry, free_vars )
   *     returns x1+x2+q
   *   inferDefinition( t+r, term_to_arg_carry, free_vars )
   *     returns null
   *
   * Notice that multiple definitions are possible, e.g. above:
   *  inferDefinition( s, term_to_arg_carry, free_vars )
   *    may return either s or x2
   * TODO (#1210) : try multiple definitions?
   */
  Node inferDefinition(
      Node n,
      std::unordered_map<Node, unsigned, NodeHashFunction>& term_to_arg_carry,
      std::unordered_map<Node,
                         std::unordered_set<Node, NodeHashFunction>,
                         NodeHashFunction>& free_vars);
  /** Assign relevant definition
   *
   * If def is non-null,
   * this function assigns def as a template definition
   * for the argument positions in args.
   * This is called when there exists a term of the form
   *   f( t1....tn )
   * in the synthesis conjecture that we are processing,
   * where t_i = def * sigma for all i \in args,
   * for some substitution sigma, where def is a template
   * definition.
   *
   * If def is null, then there exists a term of the form
   *   f( t1....tn )
   * where t_i = s for for all i \in args, and s is not
   * a template definition. In this case, at least one
   * argument in args must be marked as a relevant
   * argument position.
   *
   * Returns a value rid such that:
   * (1) rid occurs in args,
   * (2) if def is null, then argument rid was marked
   *     relevant by this call.
   */
  unsigned assignRelevantDef(Node def, std::vector<unsigned>& args);
  /** returns true if n is in d_arg_vars, updates arg_index
   * to its position in d_arg_vars.
   */
  bool isArgVar(Node n, unsigned& arg_index);
};

/** Ceg Conjecture Process
 *
 * This class implements static techniques for preprocessing and analysis of
 * sygus conjectures.
 *
 * It is used as a back-end to SynthConjecture, which calls it using the
 * following interface: (1) When a sygus conjecture is asserted, we call
 * SynthConjectureProcess::simplify( q ),
 *     where q is the sygus conjecture in original form.
 *
 * (2) After a sygus conjecture is simplified and converted to deep
 * embedding form, we call SynthConjectureProcess::initialize( n, candidates ).
 *
 * (3) During enumerative SyGuS search, calls may be made by
 * the extension of the quantifier-free datatypes decision procedure for
 * sygus to SynthConjectureProcess::getSymmetryBreakingPredicate(...), which are
 * used for pruning search space based on conjecture-specific analysis.
 */
class SynthConjectureProcess
{
 public:
  SynthConjectureProcess(QuantifiersEngine* qe);
  ~SynthConjectureProcess();
  /** simplify the synthesis conjecture q
   * Returns a formula that is equivalent to q.
   * This simplification pass is called before all others
   * in SynthConjecture::assign.
   *
   * This function is intended for simplifications that
   * impact whether or not the synthesis conjecture is
   * single-invocation.
   */
  Node preSimplify(Node q);
  /** simplify the synthesis conjecture q
   * Returns a formula that is equivalent to q.
   * This simplification pass is called after all others
   * in SynthConjecture::assign.
   */
  Node postSimplify(Node q);
  /** initialize
   *
   * n is the "base instantiation" of the deep-embedding version of
   *   the synthesis conjecture under "candidates".
   *   (see SynthConjecture::d_base_inst)
   */
  void initialize(Node n, std::vector<Node>& candidates);
  /** is the i^th argument of the function-to-synthesize f relevant? */
  bool isArgRelevant(Node f, unsigned i);
  /** get irrelevant arguments for function-to-synthesize f
   * returns true if f is a function-to-synthesize.
   */
  bool getIrrelevantArgs(Node f, std::unordered_set<unsigned>& args);
  /** get symmetry breaking predicate
  *
  * Returns a formula that restricts the enumerative search space (for a given
  * depth) for a term x of sygus type tn whose top symbol is the tindex^{th}
  * constructor, where x is a subterm of enumerator e.
  */
  Node getSymmetryBreakingPredicate(
      Node x, Node e, TypeNode tn, unsigned tindex, unsigned depth);
  /** print out debug information about this conjecture */
  void debugPrint(const char* c);
 private:
  /** process conjunct
   *
   * This sets up initial information about functions to synthesize
   * where n is a conjunct of the synthesis conjecture, and synth_fv
   * is the set of (inner) universal variables in the synthesis
   * conjecture.
   */
  void processConjunct(Node n,
                       Node f,
                       std::unordered_set<Node, NodeHashFunction>& synth_fv);
  /** flatten
   *
   * Flattens all applications of f in term n.
   * This may add new variables to synth_fv, which
   * are introduced at all positions of functions
   * to synthesize in a bottom-up fashion. For each
   * variable k introduced for a function application
   * f(t), we add ( k -> f(t) ) to defs and ( f -> k )
   * to fun_to_defs.
   */
  Node flatten(Node n,
               Node f,
               std::unordered_set<Node, NodeHashFunction>& synth_fv,
               std::unordered_map<Node, Node, NodeHashFunction>& defs);
  /** get free variables
   * Constructs a map of all free variables that occur in n
   * from synth_fv and stores them in the map free_vars.
   */
  void getFreeVariables(
      Node n,
      std::unordered_set<Node, NodeHashFunction>& synth_fv,
      std::unordered_map<Node,
                         std::unordered_set<Node, NodeHashFunction>,
                         NodeHashFunction>& free_vars);
  /** for each synth-fun, information that is specific to this conjecture */
  std::map<Node, SynthConjectureProcessFun> d_sf_info;

  /** get component vector */
  void getComponentVector(Kind k, Node n, std::vector<Node>& args);
};

} /* namespace CVC4::theory::quantifiers */
} /* namespace CVC4::theory */
} /* namespace CVC4 */

#endif
