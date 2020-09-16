/*********************                                                        */
/*! \file output_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Abdalrhman Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The output manager for the SmtEngine.
 **
 ** The output manager provides helper functions for printing commands
 ** internally.
 **/

#ifndef CVC4__SMT__OUTPUT_MANAGER_H
#define CVC4__SMT__OUTPUT_MANAGER_H

#include <ostream>

namespace CVC4 {

class Printer;
class SmtEngine;

/** This utility class provides helper functions for printing commands
 * internally */
class OutputManager
{
 public:
  /** Constructor
   *
   * @param smt SMT engine to manage output for
   */
  explicit OutputManager(SmtEngine* smt);

  /** Get the current printer based on the current options
   *
   * @return the current printer
   */
  const Printer& getPrinter() const;

  /** Get the output stream that --dump=X should print to
   *
   * @return the output stream
   */
  std::ostream& getDumpOut() const;

 private:
  SmtEngine* d_smt;
};

}  // namespace CVC4

#endif  // CVC4__SMT__OUTPUT_MANAGER_H
