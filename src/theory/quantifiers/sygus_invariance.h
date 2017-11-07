/*********************                                                        */
/*! \file sygus_explain.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief sygus invariance tests
 **/

#include "cvc4_private.h"

#ifndef __CVC4__SYGUS_INVARIANCE_H
#define __CVC4__SYGUS_INVARIANCE_H

#include <vector>
#include <unordered_map>

#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class TermDbSygus;

// TODO
class SygusInvarianceTest {
public:
  bool is_invariant( TermDbSygus * tds, Node nvn, Node x ){
    if( invariant( tds, nvn, x ) ){
      d_update_nvn = nvn;
      return true;
    }else{
      return false;
    }
  }
  // TODO : make protected
  /** result of the node after invariant replacements */
  Node d_update_nvn;
protected:
  /** check whether nvn[ x ] is invariant */
  virtual bool invariant( TermDbSygus * tds, Node nvn, Node x ) = 0;
};

// TODO
class EvalSygusInvarianceTest : public SygusInvarianceTest {
public:
  Node d_conj;
  TNode d_var;
  std::unordered_map< Node, Node, NodeHashFunction > d_visited;
  Node d_result;
protected:
  bool invariant( quantifiers::TermDbSygus * tds, Node nvn, Node x );
};


} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__SYGUS_INVARIANCE_H */
