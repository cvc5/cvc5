/*********************                                                        */
/*! \file normal_form.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Normal form datastructure for the theory of strings.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__STRINGS__NORMAL_FORM_H
#define CVC4__THEORY__STRINGS__NORMAL_FORM_H

#include <map>
#include <vector>
#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace strings {

/** normal forms
 *
 * Stores information regarding the "normal form" of terms t in the current
 * context. Normal forms can be associated with terms, or with string
 * equivalence classes. For the latter, the normal form of an equivalence class
 * exists if exactly one unique normal form is associated to a subset of its
 * terms.
 *
 * In the following we use example where assertions are:
 *   { x = y, y = z, y = u ++ v, u = u1 ++ u2 }
 * and equivalence class [x] = { x, y, z, u ++ v }, whose normal form is
 *   (u1, u2, v)
 */
class NormalForm
{
 public:
  NormalForm() : d_isRev(false) {}
  /**
   * The "base" of the normal form. This is some term in the equivalence
   * class of t that the normal form is based on. This is an arbitrary term
   * which is used as the reference point for explanations. In the above
   * running example, let us assume the base of [x] is y.
   */
  Node d_base;
  /** the normal form, (u1, u2, v), in the above example */
  std::vector<Node> d_nf;
  /** is the normal form d_nf stored in reverse order? */
  bool d_isRev;
  /**
   * The explanation for the normal form, this is a set of literals such that
   *   d_exp => d_base = d_nf
   * In the above example, this is the set of equalities
   *   { y = u ++ v, u = u1 ++ u2 }
   * If u ++ v was chosen as the base, then the first literal could be omitted.
   */
  std::vector<Node> d_exp;
  /**
   * Map from literals in the vector d_exp to integers indicating indices in
   * d_nf for which that literal L is relevant for explaining d_base = d_nf.
   *
   * In particular:
   * - false maps to an (ideally maximal) index relative to the start of d_nf
   * such that L is required for explaining why d_base has a prefix that
   * includes the term at that index,
   * - true maps to an (ideally maximal) index relative to the end of d_nf
   * such that L is required for explaining why d_base has a suffix that
   * includes the term at that index.
   * We call these the forward and backwards dependency indices.
   *
   * In the above example:
   *   y = u ++ v   : false -> 0, true -> 0
   *   u = u1 ++ u2 : false -> 0, true -> 1
   * When explaining y = u1 ++ u2 ++ v, the equality y = u ++ v is required
   * for explaining any prefix/suffix of y and its normal form. More
   * interestingly, the equality u = u1 ++ u2 is not required for explaining
   * that v is a suffix of y, since its reverse index in this map is 1,
   * indicating that "u2" is the first position in u1 ++ u2 ++ v that it is
   * required for explaining.
   *
   * This information is used to minimize explanations when conflicts arise,
   * thereby strengthening conflict clauses and lemmas.
   *
   * For example, say u ++ v = y = x = u ++ w and w and v are distinct
   * constants, using this dependency information, we could construct a
   * conflict:
   *   x = y ^ y = u ++ v ^ x = u ++ w
   * that does not include u = u1 ++ u2, because the conflict only pertains
   * to the last position in the normal form of y.
   */
  std::map<Node, std::map<bool, unsigned> > d_expDep;
  /** initialize
   *
   * Initialize the normal form with base node base. If base is not the empty
   * string, then d_nf is set to the singleton list containing base, otherwise
   * d_nf is empty.
   */
  void init(Node base);
  /** reverse the content of normal form d_nf
   *
   * This operation is done in contexts where the normal form is being scanned
   * in reverse order.
   */
  void reverse();
  /** split constant
   *
   * Splits the constant in d_nf at index to constants c1 and c2.
   *
   * Notice this function depends on whether the normal form has been reversed
   * d_isRev, as this impacts how the dependency indices are updated.
   */
  void splitConstant(unsigned index, Node c1, Node c2);
  /** add to explanation
   *
   * This adds exp to the explanation vector d_exp with new forward and
   * backwards dependency indices new_val and new_rev_val.
   *
   * If exp already has dependencies, we update the forward dependency
   * index to the minimum of the previous value and the new value, and
   * similarly update the backwards dependency index to the maximum.
   */
  void addToExplanation(Node exp, unsigned new_val, unsigned new_rev_val);
  /** get explanation
   *
   * This gets the explanation for the prefix (resp. suffix) of the normal
   * form up to index when d_isRev is false (resp. true). In particular;
   *
   * If index is -1, then this method adds all literals in d_exp to curr_exp.
   *
   * If index>=0, this method adds all literals in d_exp to curr_exp whose
   * forward (resp. backwards) dependency index is less than index
   * when isRev is false (resp. true).
   */
  void getExplanation(int index, std::vector<Node>& curr_exp);

  /**
   * Collects the constant string starting at a given index, i.e. concatenates
   * all the consecutive constant strings. If the normal form is reverse order,
   * this function searches backwards but the result will be in the original
   * order.
   *
   * @param index The index to start at, updated to point to the first
   *              non-constant component of the normal form or set equal to the
   *              size of the normal form if the remainder is all constants
   * @return The combined string constants
   */
  Node collectConstantStringAt(size_t& index);

  /** get explanation for prefix equality
   *
   * This adds to curr_exp the reason why the prefix of nfi up to index index_i
   * is equivalent to the prefix of nfj up to index_j. The values of
   * nfi.d_isRev and nfj.d_isRev affect how dependency indices are updated
   * during this call.
   */
  static void getExplanationForPrefixEq(NormalForm& nfi,
                                        NormalForm& nfj,
                                        int index_i,
                                        int index_j,
                                        std::vector<Node>& curr_exp);
};

}  // namespace strings
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__STRINGS__NORMAL_FORM_H */
