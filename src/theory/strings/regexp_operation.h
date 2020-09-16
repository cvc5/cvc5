/*********************                                                        */
/*! \file regexp_operation.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tianyi Liang, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Symbolic Regular Expresion Operations
 **
 ** Symbolic Regular Expression Operations
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__STRINGS__REGEXP__OPERATION_H
#define CVC4__THEORY__STRINGS__REGEXP__OPERATION_H

#include <map>
#include <set>
#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "theory/strings/skolem_cache.h"
#include "util/string.h"

namespace CVC4 {
namespace theory {
namespace strings {

/**
 * Information on whether regular expressions contain constants or re.allchar.
 *
 * The order of this enumeration matters: the larger the value, the more
 * possible regular expressions could fit the description.
 */
enum RegExpConstType
{
  // the regular expression doesn't contain variables or re.comp,
  // re.allchar or re.range (call these three operators "non-concrete
  // operators"). Notice that re.comp is a non-concrete operator
  // since it can be seen as indirectly defined in terms of re.allchar.
  RE_C_CONRETE_CONSTANT,
  // the regular expression doesn't contain variables, but may contain
  // re.comp, re.allchar or re.range
  RE_C_CONSTANT,
  // the regular expression may contain variables
  RE_C_VARIABLE,
  // the status of the regular expression is unknown (used internally)
  RE_C_UNKNOWN,
};

class RegExpOpr {
  typedef std::pair< Node, CVC4::String > PairNodeStr;
  typedef std::set< Node > SetNodes;
  typedef std::pair< Node, Node > PairNodes;

 private:
  /** the code point of the last character in the alphabet we are using */
  uint32_t d_lastchar;
  Node d_emptyString;
  Node d_true;
  Node d_false;
  Node d_emptySingleton;
  Node d_emptyRegexp;
  Node d_zero;
  Node d_one;

  Node d_sigma;
  Node d_sigma_star;

  /** A cache for simplify */
  std::map<Node, Node> d_simpCache;
  std::map<Node, std::pair<int, Node> > d_delta_cache;
  std::map<PairNodeStr, Node> d_dv_cache;
  std::map<PairNodeStr, std::pair<Node, int> > d_deriv_cache;
  /** cache mapping regular expressions to whether they contain constants */
  std::unordered_map<Node, RegExpConstType, NodeHashFunction> d_constCache;
  std::map<Node, std::pair<std::set<unsigned>, std::set<Node> > > d_fset_cache;
  std::map<PairNodes, Node> d_inter_cache;
  std::map<Node, std::vector<PairNodes> > d_split_cache;
  std::map<PairNodes, bool> d_inclusionCache;
  /**
   * Helper function for mkString, pretty prints constant or variable regular
   * expression r.
   */
  static std::string niceChar(Node r);
  Node mkAllExceptOne(unsigned c);
  bool isPairNodesInSet(std::set<PairNodes> &s, Node n1, Node n2);

  bool containC2(unsigned cnt, Node n);
  Node convert1(unsigned cnt, Node n);
  void convert2(unsigned cnt, Node n, Node &r1, Node &r2);
  Node intersectInternal(Node r1,
                         Node r2,
                         std::map<PairNodes, Node> cache,
                         unsigned cnt);
  /**
   * Given a regular expression r, this returns an equivalent regular expression
   * that contains no applications of intersection.
   */
  Node removeIntersection(Node r);
  void firstChars(Node r, std::set<unsigned> &pcset, SetNodes &pvset);

 public:
  RegExpOpr(SkolemCache* sc);
  ~RegExpOpr();

  /**
   * Returns true if r is a "constant" regular expression, that is, a set
   * of regular expression operators whose subterms of the form (str.to.re t)
   * are such that t is a constant (or rewrites to one).
   */
  bool checkConstRegExp( Node r );
  /** get the constant type for regular expression r */
  RegExpConstType getRegExpConstType(Node r);
  /** Simplify
   *
   * This is the main method to simplify (unfold) a regular expression
   * membership. It is called where t is of the form (str.in_re s r),
   * and t (or (not t), when polarity=false) holds in the current context.
   * It returns the unfolded form of t.
   */
  Node simplify(Node t, bool polarity);
  /**
   * Given regular expression of the form
   *   (re.++ r_0 ... r_{n-1})
   * This returns a non-null node reLen and updates index such that
   *   RegExpEntail::getFixedLengthForRegexp(r_index) = reLen
   * where index is set to either 0 or n-1.
   */
  static Node getRegExpConcatFixed(Node r, size_t& index);
  //------------------------ trusted reductions
  /**
   * Return the unfolded form of mem of the form (str.in_re s r).
   */
  static Node reduceRegExpPos(Node mem,
                              SkolemCache* sc,
                              std::vector<Node>& newSkolems);
  /**
   * Return the unfolded form of mem of the form (not (str.in_re s r)).
   */
  static Node reduceRegExpNeg(Node mem);
  /**
   * Return the unfolded form of mem of the form
   *   (not (str.in_re s (re.++ r_0 ... r_{n-1})))
   * Called when RegExpEntail::getFixedLengthForRegexp(r_index) = reLen
   * where index is either 0 or n-1.
   *
   * This uses reLen as an optimization to improve the reduction. If reLen
   * is null, then this optimization is not applied.
   */
  static Node reduceRegExpNegConcatFixed(Node mem, Node reLen, size_t index);
  //------------------------ end trusted reductions
  /**
   * This method returns 1 if the empty string is in r, 2 if the empty string
   * is not in r, or 0 if it is unknown whether the empty string is in r.
   * TODO (project #2): refactor the return value of this function.
   *
   * If this method returns 0, then exp is updated to an explanation that
   * would imply that the empty string is in r.
   *
   * For example,
   * - delta( (re.inter (str.to.re x) (re.* "A")) ) returns 0 and sets exp to
   * x = "",
   * - delta( (re.++ (str.to.re "A") R) ) returns 2,
   * - delta( (re.union (re.* "A") R) ) returns 1.
   */
  int delta( Node r, Node &exp );
  int derivativeS( Node r, CVC4::String c, Node &retNode );
  Node derivativeSingle( Node r, CVC4::String c );
  /**
   * Returns the regular expression intersection of r1 and r2. If r1 or r2 is
   * not constant, then this method returns null.
   */
  Node intersect(Node r1, Node r2);
  /** Get the pretty printed version of the regular expression r */
  static std::string mkString(Node r);

  /**
   * Returns true if we can show that the regular expression `r1` includes
   * the regular expression `r2` (i.e. `r1` matches a superset of sequences
   * that `r2` matches). See documentation in RegExpEntail::regExpIncludes for
   * more details. This call caches the result (which is context-independent),
   * for performance reasons.
   */
  bool regExpIncludes(Node r1, Node r2);

 private:
  /**
   * Given a regular expression membership of the form:
   *   (str.in_re x (re.++ R1 ... Rn))
   * This returns the valid existentially quantified formula:
   *   (exists ((x1 String) ... (xn String))
   *      (=> (str.in_re x (re.++ R1 ... Rn))
   *      (and (= x (str.++ x1 ... xn))
   *           (str.in_re x1 R1) ... (str.in_re xn Rn))))
   * Moreover, this formula is cached per regular expression membership via
   * an attribute, meaning it is always the same for a given membership mem.
   */
  static Node getExistsForRegExpConcatMem(Node mem);
  /** pointer to the skolem cache used by this class */
  SkolemCache* d_sc;
};

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__STRINGS__REGEXP__OPERATION_H */
