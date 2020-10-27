/*********************                                                        */
/*! \file unsat_core.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#ifndef CVC4__UNSAT_CORE_H
#define CVC4__UNSAT_CORE_H

#include <iosfwd>
#include <vector>

#include "expr/node.h"

namespace CVC4 {

class SmtEngine;

class UnsatCore
{
  /** The SmtEngine we're associated with */
  SmtEngine* d_smt;

  std::vector<Node> d_core;

  void initMessage() const;

public:
  UnsatCore() : d_smt(NULL) {}

  UnsatCore(SmtEngine* smt, const std::vector<Node>& core)
      : d_smt(smt), d_core(core)
  {
    initMessage();
  }

  ~UnsatCore() {}

  /** get the smt engine that this unsat core is hooked up to */
  SmtEngine* getSmtEngine() const { return d_smt; }

  size_t size() const { return d_core.size(); }

  typedef std::vector<Node>::const_iterator iterator;
  typedef std::vector<Node>::const_iterator const_iterator;

  const_iterator begin() const;
  const_iterator end() const;
  
  /** prints this UnsatCore object to the stream out.
  * We use the expression names stored in the SmtEngine d_smt
  */
  void toStream(std::ostream& out) const;

};/* class UnsatCore */

/** Print the unsat core to stream out */
std::ostream& operator<<(std::ostream& out, const UnsatCore& core);

}/* CVC4 namespace */

#endif /* CVC4__UNSAT_CORE_H */
