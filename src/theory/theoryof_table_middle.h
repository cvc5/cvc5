/*********************                                                        */
/** theoryof_table_middle.h
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** The middle section for the automatically-generated theoryOf table.
 ** See the mktheoryof script.
 **/

namespace CVC4 {
namespace theory {

class Theory;

class TheoryOfTable {

  Theory** d_table;

public:

  TheoryOfTable() :
    d_table(new Theory*[::CVC4::kind::LAST_KIND]) {
  }

  Theory* operator[](TNode n) {
    Assert(n.getKind() >= 0 && n.getKind() < ::CVC4::kind::LAST_KIND,
           "illegal to inquire theoryOf(UNDEFINED_KIND or out-of-range)");
    return d_table[n.getKind()];
  }
