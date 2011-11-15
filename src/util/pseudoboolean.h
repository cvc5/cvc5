/*********************                                                        */
/*! \file pseudoboolean.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A pseudoboolean constant
 **
 ** A pseudoboolean constant.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__PSEUDOBOOLEAN_H
#define __CVC4__PSEUDOBOOLEAN_H

#include "util/integer.h"

namespace CVC4 {

class Pseudoboolean {
  bool d_value;

public:
  Pseudoboolean(bool b);
  Pseudoboolean(int i);
  Pseudoboolean(const CVC4::Integer& i);

  operator bool() const;
  operator int() const;
  operator CVC4::Integer() const;

};/* class Pseudoboolean */

struct PseudobooleanHashStrategy {
  static inline size_t hash(CVC4::Pseudoboolean pb) {
    return int(pb);
  }
};/* struct PseudobooleanHashStrategy */

inline std::ostream& operator<<(std::ostream& os, CVC4::Pseudoboolean pb) {
  return os << int(pb);
}

}/* CVC4 namespace */

#endif /* __CVC4__PSEUDOBOOLEAN_H */
