/*********************                                                        */
/*! \file term_enumeration.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief utilities for skolemization
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__TERM_ENUMERATION_H
#define __CVC4__THEORY__QUANTIFIERS__TERM_ENUMERATION_H

#include <map>
#include <vector>

#include "expr/node.h"
#include "expr/type_node.h"
#include "theory/type_enumerator.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class TermEnumeration
{
 public:
  TermEnumeration(){}
  ~TermEnumeration(){}
  //get nth term for type
  Node getEnumerateTerm( TypeNode tn, unsigned index );
  //does this type have an enumerator that produces constants that are handled by ground theory solvers
  bool isClosedEnumerableType( TypeNode tn );
  // may complete
  bool mayComplete( TypeNode tn );
 private:
  /** ground terms enumerated for types */
  std::map< TypeNode, std::vector< Node > > d_enum_terms;
  //type enumerators
  std::map< TypeNode, unsigned > d_typ_enum_map;
  std::vector< TypeEnumerator > d_typ_enum;
  // closed enumerable type cache
  std::map< TypeNode, bool > d_typ_closed_enum;
  /** may complete */
  std::map< TypeNode, bool > d_may_complete;
};
  
}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__TERM_ENUMERATION_H */
