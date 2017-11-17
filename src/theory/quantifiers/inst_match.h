/*********************                                                        */
/*! \file inst_match.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Francois Bobot
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief inst match class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__INST_MATCH_H
#define __CVC4__THEORY__QUANTIFIERS__INST_MATCH_H

#include <vector>

#include "expr/node.h"

namespace CVC4 {
namespace theory {

class QuantifiersEngine;
class EqualityQuery;

namespace inst {

/** basic class defining an instantiation */
class InstMatch {
public:
  /* map from variable to ground terms */
  std::vector< Node > d_vals;
public:
  InstMatch(){}
  explicit InstMatch( TNode f );
  InstMatch( InstMatch* m );

  /** fill all unfilled values with m */
  bool add( InstMatch& m );
  /** if compatible, fill all unfilled values with m and return true
      return false otherwise */
  bool merge( EqualityQuery* q, InstMatch& m );
  /** debug print method */
  void debugPrint( const char* c );
  /** is complete? */
  bool isComplete();
  /** make representative */
  void makeRepresentative( QuantifiersEngine* qe );
  /** empty */
  bool empty();
  /** clear */
  void clear();
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
  /** apply rewrite */
  void applyRewrite();
  /** get */
  Node get( int i );
  void getTerms( Node f, std::vector< Node >& inst );
  /** set */
  void setValue( int i, TNode n );
  bool set( QuantifiersEngine* qe, int i, TNode n );
};/* class InstMatch */

inline std::ostream& operator<<(std::ostream& out, const InstMatch& m) {
  m.toStream(out);
  return out;
}

}/* CVC4::theory::inst namespace */

typedef CVC4::theory::inst::InstMatch InstMatch;

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__INST_MATCH_H */
