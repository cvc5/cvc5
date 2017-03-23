/*********************                                                        */
/*! \file unsat_core.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Liana Hadarean
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_public.h"

#ifndef __CVC4__UNSAT_CORE_H
#define __CVC4__UNSAT_CORE_H

#include <iosfwd>
#include <vector>

#include "expr/expr.h"

namespace CVC4 {

class SmtEngine;
class UnsatCore;

std::ostream& operator<<(std::ostream& out, const UnsatCore& core) CVC4_PUBLIC;

class CVC4_PUBLIC UnsatCore {
  friend std::ostream& operator<<(std::ostream&, const UnsatCore&);

  /** The SmtEngine we're associated with */
  SmtEngine* d_smt;

  std::vector<Expr> d_core;

  void initMessage() const;

public:
  UnsatCore() : d_smt(NULL) {}

  UnsatCore(SmtEngine* smt, std::vector<Expr> core) : d_smt(smt), d_core(core) {
    initMessage();
  }

  ~UnsatCore() {}

  /** get the smt engine that this unsat core is hooked up to */
  SmtEngine* getSmtEngine() { return d_smt; }

  size_t size() const { return d_core.size(); }

  typedef std::vector<Expr>::const_iterator iterator;
  typedef std::vector<Expr>::const_iterator const_iterator;

  const_iterator begin() const;
  const_iterator end() const;

  void toStream(std::ostream& out) const;
  void toStream(std::ostream& out, const std::map<Expr, std::string>& names) const;

};/* class UnsatCore */

}/* CVC4 namespace */

#endif /* __CVC4__UNSAT_CORE_H */
