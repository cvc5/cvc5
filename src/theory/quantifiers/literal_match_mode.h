/*********************                                                        */
/*! \file literal_match_mode.h
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

#ifndef __CVC4__THEORY__QUANTIFIERS__LITERAL_MATCH_MODE_H
#define __CVC4__THEORY__QUANTIFIERS__LITERAL_MATCH_MODE_H

#include <iostream>

namespace CVC4 {
namespace theory {
namespace quantifiers {

typedef enum {
  /** Do not consider polarity of patterns */
  LITERAL_MATCH_NONE,
  /** Consider polarity of boolean predicates only */
  LITERAL_MATCH_PREDICATE,
  /** Consider polarity of boolean predicates, as well as equalities */
  LITERAL_MATCH_EQUALITY,
} LiteralMatchMode;

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */

std::ostream& operator<<(std::ostream& out, theory::quantifiers::LiteralMatchMode mode) CVC4_PUBLIC;

}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__LITERAL_MATCH_MODE_H */
