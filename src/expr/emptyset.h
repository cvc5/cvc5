/*********************                                                        */
/*! \file emptyset.h
 ** \verbatim
 ** Original author: Kshitij Bansal
 ** Major contributors: Morgan Deters
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

#pragma once

#include <iosfwd>

namespace CVC4 {
  // messy; Expr needs EmptySet (because it's the payload of a
  // CONSTANT-kinded expression), EmptySet needs SetType, and
  // SetType needs Expr. Using a forward declaration here in
  // order to break the build cycle.
  // Uses of SetType need to be as an incomplete type throughout
  // this header.
  class CVC4_PUBLIC SetType;
}/* CVC4 namespace */

namespace CVC4 {
class CVC4_PUBLIC EmptySet {
public:
  /**
   * Constructs an emptyset of the specified type. Note that the argument
   * is the type of the set itself, NOT the type of the elements.
   */
  EmptySet(const SetType& setType);
  ~EmptySet() throw();
  EmptySet(const EmptySet& other);
  EmptySet& operator=(const EmptySet& other);

  const SetType& getType() const;
  bool operator==(const EmptySet& es) const throw();
  bool operator!=(const EmptySet& es) const throw();
  bool operator<(const EmptySet& es) const throw();
  bool operator<=(const EmptySet& es) const throw();
  bool operator>(const EmptySet& es) const throw() ;
  bool operator>=(const EmptySet& es) const throw();

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
