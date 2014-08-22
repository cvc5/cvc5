/*********************                                                        */
/*! \file unsat_core.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_public.h"

#ifndef __CVC4__UNSAT_CORE_H
#define __CVC4__UNSAT_CORE_H

#include <iostream>
#include <vector>
#include "expr/expr.h"

namespace CVC4 {

class CVC4_PUBLIC UnsatCore {
  std::vector<Expr> d_core;

public:
  UnsatCore() {}

  template <class T>
  UnsatCore(T begin, T end) : d_core(begin, end) {}

  ~UnsatCore() {}

  typedef std::vector<Expr>::const_iterator iterator;
  typedef std::vector<Expr>::const_iterator const_iterator;

  const_iterator begin() const;
  const_iterator end() const;

  void toStream(std::ostream& out) const;

};/* class UnsatCore */

std::ostream& operator<<(std::ostream& out, const UnsatCore& core) CVC4_PUBLIC;

}/* CVC4 namespace */

#endif /* __CVC4__UNSAT_CORE_H */
