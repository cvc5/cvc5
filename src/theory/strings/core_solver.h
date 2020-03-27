/*********************                                                        */
/*! \file theory_strings.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Core solver for the theory of strings, responsible for reasoning
 ** string concatenation plus length constraints.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__STRINGS__CORE_SOLVER_H
#define CVC4__THEORY__STRINGS__CORE_SOLVER_H

#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "theory/strings/base_solver.h"
#include "theory/strings/infer_info.h"
#include "theory/strings/inference_manager.h"
#include "theory/strings/normal_form.h"
#include "theory/strings/skolem_cache.h"
#include "theory/strings/solver_state.h"

namespace CVC4 {
namespace theory {
namespace strings {

/** The core solver for the theory of strings
 *
 * This implements techniques for handling (dis)equalities involving
 * string concatenation terms based on the procedure by Liang et al CAV 2014.
 */
class CoreSolver
{
  friend class InferenceManager;
  typedef context::CDHashMap<Node, int, NodeHashFunction> NodeIntMap;

 public:
  CoreSolver(context::Context* c,
             context::UserContext* u,
             SolverState& s,
             InferenceManager& im,
             SkolemCache& skc,
             BaseSolver& bs);
  ~CoreSolver();

  //-----------------------inference steps
  /** check cycles
   *
   * This inference schema ensures that a containment ordering < over the
   * string equivalence classes is acyclic. We define this ordering < such that
   * for equivalence classes e1 = { t1...tn } and e2 = { s1...sm }, e1 < e2
   * if there exists a ti whose flat form (see below) is [w1...sj...wk] for
   * some i,j. If e1 < ... < en < e1 for some chain, we infer that the flat
   * form components that do not constitute this chain, e.g. (w1...wk) \ sj
   * in the flat form above, must be empty.
   *
   * For more details, see the inference S-Cycle in Liang et al CAV 2014.
   */
  void checkCycles();
  /** check flat forms
   *
   * This applies an inference schema based on "flat forms". The flat form of a
   * string term t is a vector of representative terms [r1, ..., rn] such that
   * t is of the form t1 ++ ... ++ tm and r1 ++ ... ++ rn is equivalent to
   * rewrite( [t1] ++ ... ++ [tm] ), where [t1] denotes the representative of
   * the equivalence class containing t1. For example, if t is y ++ z ++ z,
   * E is { y = "", w = z }, and w is the representative of the equivalence
   * class { w, z }, then the flat form of t is [w, w]. Say t1 and t2 are terms
   * in the same equivalence classes with flat forms [r1...rn] and [s1...sm].
   * We may infer various facts based on this pair of terms. For example:
   *   ri = si, if ri != si, rj == sj for each j < i, and len(ri)=len(si),
   *   rn = sn, if n=m and rj == sj for each j < n,
   *   ri = empty, if n=m+1 and ri == rj for each i=1,...,m.
   * We refer to these as "unify", "endpoint-eq" and "endpoint-emp" inferences
   * respectively.
   *
   * Notice that this inference scheme is an optimization and not needed for
   * model-soundness. The motivation for this schema is that it is simpler than
   * checkNormalFormsEq, which can be seen as a recursive version of this
   * schema (see difference of "normal form" vs "flat form" below), and
   * checkNormalFormsEq is complete, in the sense that if it passes with no
   * inferences, we are ensured that all string equalities in the current
   * context are satisfied.
   *
   * Must call checkCycles before this function in a strategy.
   */
  void checkFlatForms();
  /** check normal forms equalities
   *
   * This applies an inference schema based on "normal forms". The normal form
   * of an equivalence class of string terms e = {t1, ..., tn} union {x1....xn},
   * where t1...tn are concatenation terms is a vector of representative terms
   * [r1, ..., rm] such that:
   * (1) if n=0, then m=1 and r1 is the representative of e,
   * (2) if n>0, say
   *   t1 = t^1_1 ++ ... ++ t^1_m_1
   *   ...
   *   tn = t^1_n ++ ... ++ t^_m_n
   * for *each* i=1, ..., n, the result of concenating the normal forms of
   * t^1_1 ++ ... ++ t^1_m_1 is equal to [r1, ..., rm]. If an equivalence class
   * can be assigned a normal form, then all equalities between ti and tj are
   * satisfied by all models that correspond to extensions of the current
   * assignment. For further detail on this terminology, see Liang et al
   * CAV 2014.
   *
   * Notice that all constant words are implicitly considered concatentation
   * of their characters, e.g. "abc" is treated as "a" ++ "b" ++ "c".
   *
   * At a high level, we build normal forms for equivalence classes bottom-up,
   * starting with equivalence classes that are minimal with respect to the
   * containment ordering < computed during checkCycles. While computing a
   * normal form for an equivalence class, we may infer equalities between
   * components of strings that must be equal (e.g. x=y when x++z == y++w when
   * len(x)==len(y) is asserted), derive conflicts if two strings have disequal
   * prefixes/suffixes (e.g. "a" ++ x == "b" ++ y is a conflict), or split
   * string terms into smaller components using fresh skolem variables (see
   * Inference values with names "SPLIT"). We also may introduce regular
   * expression constraints in this method for looping word equations (see
   * the Inference INFER_FLOOP).
   *
   * If this inference schema returns no facts, lemmas, or conflicts, then
   * we have successfully assigned normal forms for all equivalence classes, as
   * stored in d_normal_forms. Otherwise, this method may add a fact, lemma, or
   * conflict based on inferences in the Inference enumeration above.
   */
  void checkNormalFormsEq();
  /** check normal forms disequalities
   *
   * This inference schema can be seen as the converse of the above schema. In
   * particular, it ensures that each pair of distinct equivalence classes
   * e1 and e2 have distinct normal forms.
   *
   * This method considers all pairs of distinct equivalence classes (e1,e2)
   * such that len(x1)==len(x2) is asserted for some x1 in e1 and x2 in e2. It
   * then traverses the normal forms of x1 and x2, say they are [r1, ..., rn]
   * and [s1, ..., sm]. For the minimial i such that ri!=si, if ri and si are
   * disequal and have the same length, then x1 and x2 have distinct normal
   * forms. Otherwise, we may add splitting lemmas on the length of ri and si,
   * or split on an equality between ri and si.
   *
   * If this inference schema returns no facts, lemmas, or conflicts, then all
   * disequalities between string terms are satisfied by all models that are
   * extensions of the current assignment.
   */
  void checkNormalFormsDeq();
  /** check lengths for equivalence classes
   *
   * This inference schema adds lemmas of the form:
   *   E => len( x ) = rewrite( len( r1 ++ ... ++ rn ) )
   * where [r1, ..., rn] is the normal form of the equivalence class containing
   * x. This schema is not required for correctness but experimentally has
   * shown to be helpful.
   */
  void checkLengthsEqc();
  //-----------------------end inference steps

  //--------------------------- query functions
  /**
   * Get normal form for string term n. For details on this data structure,
   * see theory/strings/normal_form.h.
   *
   * This query is valid after a successful call to checkNormalFormsEq, e.g.
   * a call where the inference manager was not given any lemmas or inferences.
   */
  NormalForm& getNormalForm(Node n);
  /** get normal string
   *
   * This method returns the node that is equivalent to the normal form of x,
   * and adds the corresponding explanation to nf_exp.
   *
   * For example, if x = y ++ z is an assertion in the current context, then
   * this method returns the term y ++ z and adds x = y ++ z to nf_exp.
   */
  Node getNormalString(Node x, std::vector<Node>& nf_exp);
  //-------------------------- end query functions
 private:
  /**
   * This processes the infer info ii as an inference. In more detail, it calls
   * the inference manager to process the inference, it introduces Skolems, and
   * updates the set of normal form pairs.
   */
  void doInferInfo(const InferInfo& ii);
  /** Add that (n1,n2) is a normal form pair in the current context. */
  void addNormalFormPair(Node n1, Node n2);
  /** Is (n1,n2) a normal form pair in the current context? */
  bool isNormalFormPair(Node n1, Node n2);

  //--------------------------for checkFlatForm
  /**
   * This checks whether there are flat form inferences between eqc[start] and
   * eqc[j] for some j>start. If the flag isRev is true, we check for flat form
   * interferences in the reverse direction of the flat forms (note:
   * `d_flat_form` and `d_flat_form_index` must be in reverse order if `isRev`
   * is true). For more details, see checkFlatForms below.
   */
  void checkFlatForm(std::vector<Node>& eqc, size_t start, bool isRev);
  /** debug print current flat forms on trace tc */
  void debugPrintFlatForms(const char* tc);
  //--------------------------end for checkFlatForm

  //--------------------------for checkCycles
  Node checkCycles(Node eqc, std::vector<Node>& curr, std::vector<Node>& exp);
  //--------------------------end for checkCycles

  //--------------------------for checkNormalFormsEq
  /** normalize equivalence class
   *
   * This method attempts to build a "normal form" for the equivalence class
   * of string term n (for more details on normal forms, see normal_form.h
   * or see Liang et al CAV 2014). In particular, this method checks whether the
   * current normal form for each term in this equivalence class is identical.
   * If it is not, then we add an inference via sendInference and abort the
   * call.
   *
   * stype is the string-like type of the equivalence class we are processing.
   */
  void normalizeEquivalenceClass(Node n, TypeNode stype);
  /**
   * For each term in the equivalence class of eqc, this adds data regarding its
   * normal form to normal_forms. The map term_to_nf_index maps terms to the
   * index in normal_forms where their normal form data is located.
   *
   * stype is the string-like type of the equivalence class we are processing.
   */
  void getNormalForms(Node eqc,
                      std::vector<NormalForm>& normal_forms,
                      std::map<Node, unsigned>& term_to_nf_index,
                      TypeNode stype);
  /** process normalize equivalence class
   *
   * This is called when an equivalence class contains a set of terms that
   * have normal forms given by the argument normal_forms. It either
   * verifies that all normal forms in this vector are identical, or otherwise
   * adds a conflict, lemma, or inference via the sendInference method.
   *
   * To prioritize one inference versus another, it builds a set of possible
   * inferences, at most two for each pair of distinct normal forms,
   * corresponding to processing the normal form pair in the (forward, reverse)
   * directions. Once all possible inferences are recorded, it executes the
   * one with highest priority based on the enumeration type Inference.
   *
   * stype is the string-like type of the equivalence class we are processing.
   */
  void processNEqc(std::vector<NormalForm>& normal_forms, TypeNode stype);
  /** process simple normal equality
   *
   * This method is called when two equal terms have normal forms nfi and nfj.
   * It adds (typically at most one) possible inference to the vector pinfer.
   * This inference is in the form of an InferInfo object, which stores the
   * necessary information regarding how to process the inference.
   *
   * index: The index in the normal form vectors (nfi.d_nf and nfj.d_nf) that
   *   we are currently checking. This method will increment this index until
   *   it finds an index where these vectors differ, or until it reaches the
   *   end of these vectors.
   * isRev: Whether we are processing the normal forms in reverse direction.
   *   Notice in this case the normal form vectors have been reversed, hence,
   *   many operations are identical to the forward case, e.g. index is
   *   incremented not decremented, while others require special care, e.g.
   *   constant strings "ABC" in the normal form vectors are not reversed to
   *   "CBA" and hence all operations should assume a flipped semantics for
   *   constants when isRev is true,
   * rproc: the number of string components on the suffix of the normal form of
   *   nfi and nfj that were already processed. This is used when using
   *   fowards/backwards traversals of normal forms to ensure that duplicate
   *   inferences are not processed.
   * pinfer: the set of possible inferences we add to.
   *
   * stype is the string-like type of the equivalence class we are processing.
   */
  void processSimpleNEq(NormalForm& nfi,
                        NormalForm& nfj,
                        unsigned& index,
                        bool isRev,
                        unsigned rproc,
                        std::vector<InferInfo>& pinfer,
                        TypeNode stype);
  //--------------------------end for checkNormalFormsEq

  //--------------------------for checkNormalFormsEq with loops
  bool detectLoop(NormalForm& nfi,
                  NormalForm& nfj,
                  int index,
                  int& loop_in_i,
                  int& loop_in_j,
                  unsigned rproc);

  /**
   * Result of processLoop() below.
   */
  enum class ProcessLoopResult
  {
    /** Loop processing made an inference */
    INFERENCE,
    /** Loop processing detected a conflict */
    CONFLICT,
    /** Loop not processed or no loop detected */
    SKIPPED,
  };

  ProcessLoopResult processLoop(NormalForm& nfi,
                                NormalForm& nfj,
                                int loop_index,
                                int index,
                                InferInfo& info);
  //--------------------------end for checkNormalFormsEq with loops

  //--------------------------for checkNormalFormsDeq
  void processDeq(Node n1, Node n2);
  int processReverseDeq(std::vector<Node>& nfi,
                        std::vector<Node>& nfj,
                        Node ni,
                        Node nj);
  int processSimpleDeq(std::vector<Node>& nfi,
                       std::vector<Node>& nfj,
                       Node ni,
                       Node nj,
                       unsigned& index,
                       bool isRev);
  //--------------------------end for checkNormalFormsDeq

  /** The solver state object */
  SolverState& d_state;
  /** The (custom) output channel of the theory of strings */
  InferenceManager& d_im;
  /** cache of all skolems */
  SkolemCache& d_skCache;
  /** reference to the base solver, used for certain queries */
  BaseSolver& d_bsolver;
  /** Commonly used constants */
  Node d_true;
  Node d_false;
  Node d_zero;
  Node d_one;
  Node d_neg_one;
  /** empty vector (used for trivial explanations) */
  std::vector<Node> d_emptyVec;
  /**
   * The list of equivalence classes of type string. These are ordered based
   * on the ordering described in checkCycles.
   */
  std::vector<Node> d_strings_eqc;
  /** map from terms to their normal forms */
  std::map<Node, NormalForm> d_normal_form;
  /**
   * In certain cases, we know that two terms are equivalent despite
   * not having to verify their normal forms are identical. For example,
   * after applying the R-Loop rule to two terms a and b, we know they
   * are entailed to be equal in the current context without having
   * to look at their normal forms. We call (a,b) a normal form pair.
   *
   * We map representative terms a to a list of nodes b1,...,bn such that
   * (a,b1) ... (a, bn) are normal form pairs. This list is SAT-context
   * dependent. We use a context-dependent integer along with a context
   * indepedent map from nodes to lists of nodes to model this, given by
   * the two data members below.
   */
  NodeIntMap d_nf_pairs;
  std::map<Node, std::vector<Node> > d_nf_pairs_data;
  /** list of non-congruent concat terms in each equivalence class */
  std::map<Node, std::vector<Node> > d_eqc;
  /**
   * The flat form for each equivalence class. For a term (str.++ t1 ... tn),
   * this is a list of the form (r_{i1} ... r_{im}) where each empty t1...tn
   * is dropped and the others are replaced in order with their representative.
   */
  std::map<Node, std::vector<Node> > d_flat_form;
  /**
   * For each component r_{i1} ... r_{im} in a flat form, this stores
   * the argument number of the t1 ... tn they were generated from.
   */
  std::map<Node, std::vector<int> > d_flat_form_index;
}; /* class CoreSolver */

}  // namespace strings
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__STRINGS__CORE_SOLVER_H */
