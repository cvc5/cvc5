/*********************                                                        */
/*! \file preempt_get_option.h
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Utility function for extending commandline options.
 **
 ** Utility function for extending commandline options.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__OPTIONS__PREMPT_GET_OPTION_H
#define __CVC4__OPTIONS__PREMPT_GET_OPTION_H

#include <cstddef>
#include <vector>

namespace CVC4 {
namespace options {


class ArgumentExtender {
 public:
  /**
   * Preconditions:
   *  additional >= 1
   *  length >= 1
   */
  ArgumentExtender(unsigned additional, size_t length);
  ~ArgumentExtender();

  /**
   * This purpose of this function is to massage argc and argv upon the event
   * of parsing during Options::parseOptions of an option with the :link or
   * :link-alternative attributes. The purpose of the function is to extend argv
   * with another commandline argument.
   *
   * Preconditions:
   *  opt is '\0' terminated, non-null and non-empty c-string.
   *  strlen(opt) <= getLength()
   *
   * Let P be the first position in argv that is >= 1 and is either NULL or
   * empty:
   *   argv[P] == NULL || argv[P] == '\0'
   *
   * This has a very specific set of side effects:
   * - argc is incremented by one.
   * - If argv[P] == NULL, this reallocates argv to have (P+additional)
   *   elements.
   * - The 0 through P-1 elements of argv are the same.
   * - The P element of argv is a copy of the first len-1 characters of opt.
   *   This is a newly allocated '\0' terminated c string of length len.
   * - The P+1 through (P+additional-2) elements of argv are newly allocated
   *   empty '\0' terminated c strings of size len.
   * - The last element at (P+additional-1) of argv is NULL.
   * - All allocations are pushed back onto allocated.
   */
  void extend(int& argc, char**& argv, const char* opt,
              std::vector<char*>& allocated);

  unsigned getIncrease() const;
  size_t getLength() const;

 private:
  unsigned d_additional;
  size_t d_length;
};

}/* CVC4::options namespace */
}/* CVC4 namespace */

#endif /* __CVC4__OPTIONS__PREMPT_GET_OPTION_H */
