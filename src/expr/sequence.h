/*********************                                                        */
/*! \file emptyset.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
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

#pragma once

#include <iosfwd>
#include <vector>
#include <memory>

namespace CVC4 {
  // messy; Expr needs Sequence (because it's the payload of a
  // CONSTANT-kinded expression), Sequence needs SequenceType, and
  // SequenceType needs Expr. Using a forward declaration here in
  // order to break the build cycle.
  // Uses of SequenceType need to be as an incomplete type throughout
  // this header.
  class SequenceType;
  class Expr;
}/* CVC4 namespace */

namespace CVC4 {
class CVC4_PUBLIC Sequence {
 public:
  /**
   * Constructs an emptyset of the specified type. Note that the argument
   * is the type of the set itself, NOT the type of the elements.
   */
  Sequence(const SequenceType& seqType);
  ~Sequence();
  Sequence(const Sequence& other);
  Sequence& operator=(const Sequence& other);

  const SequenceType& getType() const;
  bool operator==(const Sequence& es) const;
  bool operator!=(const Sequence& es) const;
  bool operator<(const Sequence& es) const;
  bool operator<=(const Sequence& es) const;
  bool operator>(const Sequence& es) const;
  bool operator>=(const Sequence& es) const;

 private:
  /** Pointer to the SequenceType node. This is never NULL. */
  SequenceType * d_type;
  
  Sequence();

};/* class Sequence */

std::ostream& operator<<(std::ostream& out, const Sequence& es) CVC4_PUBLIC;

struct CVC4_PUBLIC SequenceHashFunction {
  size_t operator()(const Sequence& es) const;
};/* struct SequenceHashFunction */

}/* CVC4 namespace */
