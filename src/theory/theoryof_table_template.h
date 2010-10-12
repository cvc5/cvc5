/*********************                                                        */
/*! \file theoryof_table_template.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The template for the automatically-generated theoryOf table.
 **
 ** The template for the automatically-generated theoryOf table.
 ** See the mktheoryof script.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__THEORYOF_TABLE_H
#define __CVC4__THEORY__THEORYOF_TABLE_H

#include "expr/kind.h"
#include "util/Assert.h"

${theoryof_table_forwards}

namespace CVC4 {
namespace theory {

class Theory;

class TheoryOfTable {

  Theory** d_table;

public:

  TheoryOfTable() :
    d_table(new Theory*[::CVC4::kind::LAST_KIND]) {
  }

  ~TheoryOfTable() {
    delete [] d_table;
  }

  Theory* operator[](TNode n) {
    Assert(n.getKind() >= 0 && n.getKind() < ::CVC4::kind::LAST_KIND,
           "illegal to inquire theoryOf(UNDEFINED_KIND or out-of-range)");
    return d_table[n.getKind()];
  }

  Theory* operator[](::CVC4::Kind k) {
    Assert(k >= 0 && k < ::CVC4::kind::LAST_KIND,
           "illegal to inquire theoryOf(UNDEFINED_KIND or out-of-range)");
    return d_table[k];
  }
${theoryof_table_registers}
};/* class TheoryOfTable */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__THEORYOF_TABLE_H */
