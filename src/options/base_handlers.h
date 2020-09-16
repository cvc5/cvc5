/*********************                                                        */
/*! \file base_handlers.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Mathias Preiner
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

#include "cvc4_private.h"

#ifndef CVC4__BASE_HANDLERS_H
#define CVC4__BASE_HANDLERS_H

#include <iostream>
#include <string>
#include <sstream>

#include "options/option_exception.h"

namespace CVC4 {
namespace options {

template <template <class U> class Cmp>
class comparator {
  long d_lbound;
  double d_dbound;
  bool d_hasLbound;

 public:
  comparator(int i) : d_lbound(i), d_dbound(0.0), d_hasLbound(true) {}
  comparator(long l) : d_lbound(l), d_dbound(0.0), d_hasLbound(true) {}
  comparator(double d) : d_lbound(0), d_dbound(d), d_hasLbound(false) {}
  template <class T>
  void operator()(std::string option, const T& value) {
    if((d_hasLbound && !(Cmp<T>()(value, T(d_lbound)))) ||
       (!d_hasLbound && !(Cmp<T>()(value, T(d_dbound))))) {
      std::stringstream ss;
      ss << option << ": " << value << " is not a legal setting";
      throw OptionException(ss.str());
    }
  }
};/* class comparator */

struct greater : public comparator<std::greater> {
  greater(int i) : comparator<std::greater>(i) {}
  greater(long l) : comparator<std::greater>(l) {}
  greater(double d) : comparator<std::greater>(d) {}
};/* struct greater */

struct greater_equal : public comparator<std::greater_equal> {
  greater_equal(int i) : comparator<std::greater_equal>(i) {}
  greater_equal(long l) : comparator<std::greater_equal>(l) {}
  greater_equal(double d) : comparator<std::greater_equal>(d) {}
};/* struct greater_equal */

struct less : public comparator<std::less> {
  less(int i) : comparator<std::less>(i) {}
  less(long l) : comparator<std::less>(l) {}
  less(double d) : comparator<std::less>(d) {}
};/* struct less */

struct less_equal : public comparator<std::less_equal> {
  less_equal(int i) : comparator<std::less_equal>(i) {}
  less_equal(long l) : comparator<std::less_equal>(l) {}
  less_equal(double d) : comparator<std::less_equal>(d) {}
};/* struct less_equal */

struct not_equal : public comparator<std::not_equal_to> {
  not_equal(int i) : comparator<std::not_equal_to>(i) {}
  not_equal(long l) : comparator<std::not_equal_to>(l) {}
  not_equal(double d) : comparator<std::not_equal_to>(d) {}
};/* struct not_equal_to */

}/* CVC4::options namespace */
}/* CVC4 namespace */

#endif /* CVC4__BASE_HANDLERS_H */
