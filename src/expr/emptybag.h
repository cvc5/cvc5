/*********************                                                        */
/*! \file emptybag.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief a class for empty bags
 **/

#include "cvc4_public.h"

#ifndef CVC4__EMPTY_BAG_H
#define CVC4__EMPTY_BAG_H

#include <iosfwd>
#include <memory>

namespace CVC4 {

class TypeNode;

class CVC4_PUBLIC EmptyBag
{
 public:
  /**
   * Constructs an emptybag of the specified type. Note that the argument
   * is the type of the bag itself, NOT the type of the elements.
   */
  EmptyBag(const TypeNode& bagType);
  ~EmptyBag();
  EmptyBag(const EmptyBag& other);
  EmptyBag& operator=(const EmptyBag& other);

  const TypeNode& getType() const;
  bool operator==(const EmptyBag& es) const;
  bool operator!=(const EmptyBag& es) const;
  bool operator<(const EmptyBag& es) const;
  bool operator<=(const EmptyBag& es) const;
  bool operator>(const EmptyBag& es) const;
  bool operator>=(const EmptyBag& es) const;

 private:
  EmptyBag();

  /** the type of the empty bag itself (not the type of the elements)*/
  std::unique_ptr<TypeNode> d_type;
}; /* class EmptyBag */

std::ostream& operator<<(std::ostream& out, const EmptyBag& es) CVC4_PUBLIC;

struct CVC4_PUBLIC EmptyBagHashFunction
{
  size_t operator()(const EmptyBag& es) const;
}; /* struct EmptyBagHashFunction */

}  // namespace CVC4

#endif /* CVC4__EMPTY_BAG_H */
