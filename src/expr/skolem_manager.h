/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Skolem manager utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__EXPR__SKOLEM_MANAGER_H
#define CVC5__EXPR__SKOLEM_MANAGER_H

#include <string>

#include "expr/node.h"

namespace cvc5 {

class ProofGenerator;

/** Skolem function identifier */
enum class SkolemFunId
{
  NONE,
  /** an uninterpreted function f s.t. f(x) = x / 0.0 (real division) */
  DIV_BY_ZERO,
  /** an uninterpreted function f s.t. f(x) = x / 0 (integer division) */
  INT_DIV_BY_ZERO,
  /** an uninterpreted function f s.t. f(x) = x mod 0 */
  MOD_BY_ZERO,
  /** an uninterpreted function f s.t. f(x) = sqrt(x) */
  SQRT,
  /** a wrongly applied selector */
  SELECTOR_WRONG,
  /** a shared selector */
  SHARED_SELECTOR,
  /** an application of seq.nth that is out of bounds */
  SEQ_NTH_OOB,
  //----- string skolems are cached based on two strings (a, b)
  /** exists k. ( b occurs k times in a ) */
  STRINGS_NUM_OCCUR,
  /** For function k: Int -> Int
   *   exists k.
   *     forall 0 <= x <= n,
   *       k(x) is the end index of the x^th occurrence of b in a
   *   where n is the number of occurrences of b in a, and k(0)=0.
   */
  STRINGS_OCCUR_INDEX,
  /**
   * For function k: Int -> Int
   *   exists k.
   *     forall 0 <= x < n,
   *       k(x) is the length of the x^th occurrence of b in a (excluding
   *       matches of empty strings)
   *   where b is a regular expression, n is the number of occurrences of b
   *   in a, and k(0)=0.
   */
  STRINGS_OCCUR_LEN,
  /**
   * Diff index for disequalities a != b => substr(a,k,1) != substr(b,k,1)
   */
  STRINGS_DEQ_DIFF,
  //-----
  /**
   * A function used to define intermediate results of str.replace_all and
   * str.replace_re_all applications.
   */
  STRINGS_REPLACE_ALL_RESULT,
  /**
   * A function used to define intermediate results of str.from_int
   * applications.
   */
  STRINGS_ITOS_RESULT,
  /**
   * A function used to define intermediate results of str.to_int
   * applications.
   */
  STRINGS_STOI_RESULT,
  /**
   * An index containing a non-digit in a string, used when (str.to_int a) = -1.
   */
  STRINGS_STOI_NON_DIGIT,
  /**
   * For sequence a and regular expression b,
   * in_re(a, re.++(_*, b, _*)) =>
   *    exists k_pre, k_match, k_post.
   *       a = k_pre ++ k_match ++ k_post ^
   *       len(k_pre) = indexof_re(x, y, 0) ^
   *       (forall l. 0 < l < len(k_match) =>
   *         ~in_re(substr(k_match, 0, l), r)) ^
   *       in_re(k_match, b)
   *
   * k_pre is the prefix before the first, shortest match of b in a. k_match
   * is the substring of a matched by b. It is either empty or there is no
   * shorter string that matches b.
   */
  SK_FIRST_MATCH_PRE,
  SK_FIRST_MATCH,
  SK_FIRST_MATCH_POST,
  /**
   * Regular expression unfold component: if (str.in_re t R), where R is
   * (re.++ r0 ... rn), then the RE_UNFOLD_POS_COMPONENT{t,R,i} is a string
   * skolem ki such that t = (str.++ k0 ... kn) and (str.in_re k0 r0) for
   * i = 0, ..., n.
   */
  RE_UNFOLD_POS_COMPONENT,
  /** An interpreted function for bag.choose operator:
   * (bag.choose A) is expanded as
   * (witness ((x elementType))
   *    (ite
   *      (= A (as emptybag (Bag E)))
   *      (= x (uf A))
   *      (and (>= (bag.count x A) 1) (= x (uf A)))
   * where uf: (Bag E) -> E is a skolem function, and E is the type of elements
   * of A
   */
  BAGS_CHOOSE,
  /** An uninterpreted function for bag.map operator:
   * To compute (bag.count y (map f A)), we need to find the distinct
   * elements in A that are mapped to y by function f (i.e., preimage of {y}).
   * If n is the cardinality of this preimage, then
   * the preimage is the set {uf(1), ..., uf(n)}
   * where uf: Int -> E is a skolem function, and E is the type of elements of A
   */
  BAGS_MAP_PREIMAGE,
  /** An uninterpreted function for bag.map operator:
   * If the preimage of {y} in A is {uf(1), ..., uf(n)} (see BAGS_MAP_PREIMAGE},
   * then the multiplicity of an element y in a bag (map f A) is sum(n),
   * where sum: Int -> Int is a skolem function such that:
   * sum(0) = 0
   * sum(i) = sum (i-1) + (bag.count (uf i) A)
   */
  BAGS_MAP_SUM,
  /** An interpreted function for bag.choose operator:
   * (choose A) is expanded as
   * (witness ((x elementType))
   *    (ite
   *      (= A (as emptyset (Set E)))
   *      (= x (uf A))
   *      (and (member x A) (= x uf(A)))
   * where uf: (Set E) -> E is a skolem function, and E is the type of elements
   * of A
   */
  SETS_CHOOSE,
  /** Higher-order type match predicate, see HoTermDb */
  HO_TYPE_MATCH_PRED,
};
/** Converts a skolem function name to a string. */
const char* toString(SkolemFunId id);
/** Writes a skolem function name to a stream. */
std::ostream& operator<<(std::ostream& out, SkolemFunId id);

/**
 * A manager for skolems that can be used in proofs. This is designed to be
 * a trusted interface to NodeManager::mkSkolem, where one
 * must provide a definition for the skolem they create in terms of a
 * predicate that the introduced variable is intended to witness.
 *
 * It is implemented by mapping terms to an attribute corresponding to their
 * "original form" and "witness form" as described below. Hence, this class does
 * not impact the reference counting of skolem variables which may be deleted if
 * they are not used.
 *
 * We distinguish two kinds of mappings between terms and skolems:
 *
 * (1) "Original form", which associates skolems with the terms they purify.
 * This is used in mkPurifySkolem below.
 *
 * (2) "Witness form", which associates skolems with their formal definition
 * as a witness term. This is used in mkSkolem below.
 *
 * It is possible to unify these so that purification skolems for t are skolems
 * whose witness form is (witness ((x T)) (= x t)). However, there are
 * motivations not to do so. In particular, witness terms in most contexts
 * should be seen as black boxes, converting something to witness form may have
 * unintended consequences e.g. variable shadowing. In contrast, converting to
 * original form does not have these complications. Furthermore, having original
 * form greatly simplifies reasoning in the proof, in particular, it avoids the
 * need to reason about identifiers for introduced variables x.
 *
 * Furthermore, note that original form and witness form may share skolems
 * in the rare case that a witness term is purified. This is currently only the
 * case for algorithms that introduce witness, e.g. BV/set instantiation.
 *
 * Additionally, we consider a third class of skolems (mkSkolemFunction) which
 * are for convenience associated with an identifier, and not a witness term.
 */
class SkolemManager
{
 public:
  SkolemManager();
  ~SkolemManager() {}

  /**
   * Optional flags used to control behavior of skolem creation.
   * They should be composed with a bitwise OR (e.g.,
   * "SKOLEM_BOOL_TERM_VAR | SKOLEM_EXACT_NAME").  Of course, SKOLEM_DEFAULT
   * cannot be composed in such a manner.
   */
  enum SkolemFlags
  {
    SKOLEM_DEFAULT = 0,    /**< default behavior */
    SKOLEM_EXACT_NAME = 1, /**< do not make the name unique by adding the id */
    SKOLEM_BOOL_TERM_VAR = 2 /**< vars requiring kind BOOLEAN_TERM_VARIABLE */
  };
  /**
   * This makes a skolem of same type as bound variable v, (say its type is T),
   * whose definition is (witness ((v T)) pred). This definition is maintained
   * by this class.
   *
   * Notice that (exists ((v T)) pred) should be a valid formula. This fact
   * captures the reason for why the returned Skolem was introduced.
   *
   * Take as an example extensionality in arrays:
   *
   * (declare-fun a () (Array Int Int))
   * (declare-fun b () (Array Int Int))
   * (assert (not (= a b)))
   *
   * To witness the index where the arrays a and b are disequal, it is intended
   * we call this method on:
   *   Node k = mkSkolem( x, F )
   * where F is:
   *   (=> (not (= a b)) (not (= (select a x) (select b x))))
   * and x is a fresh bound variable of integer type. Internally, this will map
   * k to the term:
   *   (witness ((x Int)) (=> (not (= a b))
   *                          (not (= (select a x) (select b x)))))
   * A lemma generated by the array solver for extensionality may safely use
   * the skolem k in the standard way:
   *   (=> (not (= a b)) (not (= (select a k) (select b k))))
   * Furthermore, notice that the following lemma does not involve fresh
   * skolem variables and is valid according to the theory of arrays extended
   * with support for witness:
   *   (let ((w (witness ((x Int)) (=> (not (= a b))
   *                                   (not (= (select a x) (select b x)))))))
   *     (=> (not (= a b)) (not (= (select a w) (select b w)))))
   * This version of the lemma, which requires no explicit tracking of free
   * Skolem variables, can be obtained by a call to getWitnessForm(...)
   * below. We call this the "witness form" of the lemma above.
   *
   * @param v The bound variable of the same type of the Skolem to create.
   * @param pred The desired property of the Skolem to create, in terms of bound
   * variable v.
   * @param prefix The prefix of the name of the Skolem
   * @param comment Debug information about the Skolem
   * @param flags The flags for the Skolem (see SkolemFlags)
   * @param pg The proof generator for this skolem. If non-null, this proof
   * generator must respond to a call to getProofFor(exists v. pred) during
   * the lifetime of the current node manager.
   * @return The skolem whose witness form is registered by this class.
   */
  Node mkSkolem(Node v,
                Node pred,
                const std::string& prefix,
                const std::string& comment = "",
                int flags = SKOLEM_DEFAULT,
                ProofGenerator* pg = nullptr);
  /**
   * Make skolemized form of existentially quantified formula q, and store its
   * Skolems into the argument skolems.
   *
   * For example, calling this method on:
   *   (exists ((x Int) (y Int)) (P x y))
   * returns:
   *   (P w1 w2)
   * where w1 and w2 are skolems with witness forms:
   *   (witness ((x Int)) (exists ((y Int)) (P x y)))
   *   (witness ((y Int)) (P w1 y))
   * respectively. Additionally, this method will add { w1, w2 } to skolems.
   * Notice that y is *not* renamed in the witness form of w1. This is not
   * necessary since w1 is skolem. Although its witness form contains
   * quantification on y, we never construct a term where the witness form
   * of w1 is expanded in the witness form of w2. This avoids variable
   * shadowing.
   *
   * In contrast to mkSkolem, the proof generator is for the *entire*
   * existentially quantified formula q, which may have multiple variables in
   * its prefix.
   *
   * @param q The existentially quantified formula to skolemize,
   * @param skolems Vector to add Skolems of q to,
   * @param prefix The prefix of the name of each of the Skolems
   * @param comment Debug information about each of the Skolems
   * @param flags The flags for the Skolem (see SkolemFlags)
   * @param pg The proof generator for this skolem. If non-null, this proof
   * generator must respond to a call to getProofFor(q) during
   * the lifetime of the current node manager.
   * @return The skolemized form of q.
   */
  Node mkSkolemize(Node q,
                   std::vector<Node>& skolems,
                   const std::string& prefix,
                   const std::string& comment = "",
                   int flags = SKOLEM_DEFAULT,
                   ProofGenerator* pg = nullptr);
  /**
   * Same as above, but for special case of (witness ((x T)) (= x t))
   * where T is the type of t. This skolem is unique for each t, which we
   * implement via an attribute on t. This attribute is used to ensure to
   * associate a unique skolem for each t.
   *
   * Notice that a purification skolem is trivial to justify, and hence it
   * does not require a proof generator.
   *
   * Notice that in very rare cases, two different terms may have the
   * same purification skolem. For example, let k be the skolem introduced to
   * eliminate (ite A B C). Then, the pair of terms:
   *  (ite (ite A B C) D E) and (ite k D E)
   * have the same purification skolem. In the implementation, this is a result
   * of the fact that the above terms have the same original form. It is sound
   * to use the same skolem to purify these two terms, since they are
   * definitionally equivalent.
   */
  Node mkPurifySkolem(Node t,
                      const std::string& prefix,
                      const std::string& comment = "",
                      int flags = SKOLEM_DEFAULT);
  /**
   * Make skolem function. This method should be used for creating fixed
   * skolem functions of the forms described in SkolemFunId. The user of this
   * method is responsible for providing a proper type for the identifier that
   * matches the description of id. Skolem functions are useful for modelling
   * the behavior of partial functions, or for theory-specific inferences that
   * introduce fresh variables.
   *
   * A skolem function is not given a formal semantics in terms of a witness
   * term, nor is it a purification skolem, thus it does not fall into the two
   * categories of skolems above. This method is motivated by convenience, as
   * the user of this method does not require constructing canonical variables
   * for witness terms.
   *
   * The returned skolem is an ordinary skolem variable that can be used
   * e.g. in APPLY_UF terms when tn is a function type.
   *
   * Notice that we do not insist that tn is a function type. A user of this
   * method may construct a canonical (first-order) skolem using this method
   * as well.
   *
   * @param id The identifier of the skolem function
   * @param tn The type of the returned skolem function
   * @param cacheVal A cache value. The returned skolem function will be
   * unique to the pair (id, cacheVal). This value is required, for instance,
   * for skolem functions that are in fact families of skolem functions,
   * e.g. the wrongly applied case of selectors.
   * @return The skolem function.
   */
  Node mkSkolemFunction(SkolemFunId id,
                        TypeNode tn,
                        Node cacheVal = Node::null(),
                        int flags = SKOLEM_DEFAULT);
  /** Same as above, with multiple cache values */
  Node mkSkolemFunction(SkolemFunId id,
                        TypeNode tn,
                        const std::vector<Node>& cacheVals,
                        int flags = SKOLEM_DEFAULT);
  /**
   * Is k a skolem function? Returns true if k was generated by the above call.
   * Updates the arguments to the values used when constructing it.
   */
  bool isSkolemFunction(Node k, SkolemFunId& id, Node& cacheVal) const;
  /**
   * Create a skolem constant with the given name, type, and comment. This
   * should only be used if the definition of the skolem does not matter.
   * The definition of a skolem matters e.g. when the skolem is used in a
   * proof.
   *
   * @param prefix the name of the new skolem variable is the prefix
   * appended with a unique ID.  This way a family of skolem variables
   * can be made with unique identifiers, used in dump, tracing, and
   * debugging output.  Use SKOLEM_EXACT_NAME flag if you don't want
   * a unique ID appended and use prefix as the name.
   * @param type the type of the skolem variable to create
   * @param comment a comment for dumping output; if declarations are
   * being dumped, this is included in a comment before the declaration
   * and can be quite useful for debugging
   * @param flags an optional mask of bits from SkolemFlags to control
   * skolem behavior
   */
  Node mkDummySkolem(const std::string& prefix,
                     const TypeNode& type,
                     const std::string& comment = "",
                     int flags = SKOLEM_DEFAULT);
  /**
   * Get proof generator for existentially quantified formula q. This returns
   * the proof generator that was provided in a call to mkSkolem above.
   */
  ProofGenerator* getProofGenerator(Node q) const;
  /**
   * Convert to witness form, which gets the witness form of a skolem k.
   * Notice this method is *not* recursive, instead, it is a simple attribute
   * lookup.
   *
   * @param k The variable to convert to witness form described above
   * @return k in witness form.
   */
  static Node getWitnessForm(Node k);
  /**
   * Convert to original form, which recursively replaces all skolems terms in n
   * by the term they purify.
   *
   * @param n The term or formula to convert to original form described above
   * @return n in original form.
   */
  static Node getOriginalForm(Node n);

 private:
  /** Cache of skolem functions for mkSkolemFunction above. */
  std::map<std::tuple<SkolemFunId, TypeNode, Node>, Node> d_skolemFuns;
  /** Backwards mapping of above */
  std::map<Node, std::tuple<SkolemFunId, TypeNode, Node>> d_skolemFunMap;
  /**
   * Mapping from witness terms to proof generators.
   */
  std::map<Node, ProofGenerator*> d_gens;

  /**
   * A counter used to produce unique skolem names.
   *
   * Note that it is NOT incremented when skolems are created using
   * SKOLEM_EXACT_NAME, so it is NOT a count of the skolems produced
   * by this node manager.
   */
  size_t d_skolemCounter;
  /** Get or make skolem attribute for term w, which may be a witness term */
  Node mkSkolemInternal(Node w,
                        const std::string& prefix,
                        const std::string& comment,
                        int flags);
  /**
   * Skolemize the first variable of existentially quantified formula q.
   * For example, calling this method on:
   *   (exists ((x Int) (y Int)) (P x y))
   * will return:
   *   (witness ((x Int)) (exists ((y Int)) (P x y)))
   * If q is not an existentially quantified formula, then null is
   * returned and an assertion failure is thrown.
   *
   * This method additionally updates qskolem to be the skolemized form of q.
   * In the above example, this is set to:
   *   (exists ((y Int)) (P (witness ((x Int)) (exists ((y' Int)) (P x y'))) y))
   */
  Node skolemize(Node q,
                 Node& qskolem,
                 const std::string& prefix,
                 const std::string& comment = "",
                 int flags = SKOLEM_DEFAULT);
  /**
   * Create a skolem constant with the given name, type, and comment.
   *
   * This method is intentionally private. To create skolems, one should
   * call a public method from SkolemManager for allocating a skolem in a
   * proper way, or otherwise use SkolemManager::mkDummySkolem.
   */
  Node mkSkolemNode(const std::string& prefix,
                    const TypeNode& type,
                    const std::string& comment = "",
                    int flags = SKOLEM_DEFAULT);
};

}  // namespace cvc5

#endif /* CVC5__EXPR__PROOF_SKOLEM_CACHE_H */
