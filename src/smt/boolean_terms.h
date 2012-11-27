/*********************                                                        */
/*! \file boolean_terms.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#pragma once

#include "expr/attribute.h"
#include "expr/node.h"
#include "util/hash.h"
#include <utility>

namespace CVC4 {
namespace smt {

namespace attr {
  struct BooleanTermAttrTag { };
}/* CVC4::smt::attr namespace */

typedef expr::Attribute<attr::BooleanTermAttrTag, Node> BooleanTermAttr;

class BooleanTermConverter {
  /** The type of the Boolean term conversion cache */
  typedef std::hash_map< std::pair<Node, bool>, Node,
                         PairHashFunction< Node, bool,
                                           NodeHashFunction, std::hash<int> > > BooleanTermCache;

  /** The cache used during Boolean term conversion */
  BooleanTermCache d_booleanTermCache;

  /**
   * Scan a datatype for and convert as necessary.
   */
  const Datatype& booleanTermsConvertDatatype(const Datatype& dt) throw();

public:

  /**
   * We rewrite Boolean terms in assertions as bitvectors of length 1.
   */
  Node rewriteBooleanTerms(TNode n, bool boolParent = true) throw();

};/* class BooleanTermConverter */

}/* CVC4::smt namespace */
}/* CVC4 namespace */
