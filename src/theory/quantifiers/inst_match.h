/*********************                                                        */
/*! \file inst_match.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief inst match class
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__INST_MATCH_H
#define CVC4__THEORY__QUANTIFIERS__INST_MATCH_H

#include <vector>

#include "expr/node.h"

namespace CVC4 {
namespace theory {

class EqualityQuery;

namespace inst {

/** Inst match
 *
 * This is the basic class specifying an instantiation. Its domain size (the
 * size of d_vals) is the number of bound variables of the quantified formula
 * that is passed to its constructor.
 *
 * The values of d_vals may be null, which indicate that the field has
 * yet to be initialized.
 */
class InstMatch {
public:
  InstMatch(){}
  explicit InstMatch(TNode q);
  InstMatch( InstMatch* m );
  /* map from variable to ground terms */
  std::vector<Node> d_vals;
  /** add match m
   *
   * This adds the initialized fields of m to this match for each field that is
   * not already initialized in this match.
   */
  void add(InstMatch& m);
  /** merge with match m
   *
   * This method returns true if the merge was successful, that is, all jointly
   * initialized fields of this class and m are equivalent modulo the equalities
   * given by q.
   */
  bool merge( EqualityQuery* q, InstMatch& m );
  /** is this complete, i.e. are all fields non-null? */
  bool isComplete();
  /** is this empty, i.e. are all fields the null node? */
  bool empty();
  /** clear the instantiation, i.e. set all fields to the null node */
  void clear();
  /** debug print method */
  void debugPrint(const char* c);
  /** to stream */
  inline void toStream(std::ostream& out) const {
    out << "INST_MATCH( ";
    bool printed = false;
    for( unsigned i=0; i<d_vals.size(); i++ ){
      if( !d_vals[i].isNull() ){
        if( printed ){ out << ", "; }
        out << i << " -> " << d_vals[i];
        printed = true;
      }
    }
    out << " )";
  }
  /** get the i^th term in the instantiation */
  Node get(size_t i) const;
  /** set/overwrites the i^th field in the instantiation with n */
  void setValue(size_t i, TNode n);
  /** set the i^th term in the instantiation to n
   *
   * This method returns true if the i^th field was previously uninitialized,
   * or is equivalent to n modulo the equalities given by q.
   */
  bool set(EqualityQuery* q, size_t i, TNode n);
};

inline std::ostream& operator<<(std::ostream& out, const InstMatch& m) {
  m.toStream(out);
  return out;
}

}/* CVC4::theory::inst namespace */

typedef CVC4::theory::inst::InstMatch InstMatch;

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__QUANTIFIERS__INST_MATCH_H */
