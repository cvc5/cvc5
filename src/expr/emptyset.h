/*********************                                                        */
/*! \file emptyset.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Kshitij Bansal, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
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

namespace CVC4 {
  // messy; Expr needs EmptySet (because it's the payload of a
  // CONSTANT-kinded expression), EmptySet needs SetType, and
  // SetType needs Expr. Using a forward declaration here in
  // order to break the build cycle.
  // Uses of SetType need to be as an incomplete type throughout
  // this header.
  class SetType;
}/* CVC4 namespace */

namespace CVC4 {
class CVC4_PUBLIC EmptySet {
 public:
  /**
   * Constructs an emptyset of the specified type. Note that the argument
   * is the type of the set itself, NOT the type of the elements.
   */
  EmptySet(const SetType& setType);
  ~EmptySet();
  EmptySet(const EmptySet& other);
  EmptySet& operator=(const EmptySet& other);

  const SetType& getType() const;
  bool operator==(const EmptySet& es) const;
  bool operator!=(const EmptySet& es) const;
  bool operator<(const EmptySet& es) const;
  bool operator<=(const EmptySet& es) const;
  bool operator>(const EmptySet& es) const;
  bool operator>=(const EmptySet& es) const;

 private:
  /** Pointer to the SetType node. This is never NULL. */
  SetType* d_type;

  EmptySet();

};/* class EmptySet */

std::ostream& operator<<(std::ostream& out, const EmptySet& es) CVC4_PUBLIC;

struct CVC4_PUBLIC EmptySetHashFunction {
  size_t operator()(const EmptySet& es) const;
};/* struct EmptySetHashFunction */

}/* CVC4 namespace */
