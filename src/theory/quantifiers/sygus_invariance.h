/*********************                                                        */
/*! \file sygus_invariance.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief sygus invariance test
 **/

#include "cvc4_private.h"

#ifndef __CVC4__SYGUS_INVARIANCE_H
#define __CVC4__SYGUS_INVARIANCE_H

#include <vector>

#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** Recursive term builder 
 *
 * This is a utility used for generalizing 
 * the shape of terms.
 */
class TermRecBuild {
public:
  TermRecBuild(){}
  void init( Node n );
  void push( unsigned p );
  void pop();
  void replaceChild( unsigned i, Node n );
  Node getChild( unsigned i );
  Node build( unsigned p=0 );
private:
  std::vector< Node > d_term;
  std::vector< std::vector< Node > > d_children;
  std::vector< Kind > d_kind;
  std::vector< bool > d_has_op;
  std::vector< unsigned > d_pos;
  void addTerm( Node n );
};

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__SYGUS_INVARIANCE_H */
