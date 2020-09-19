/*********************                                                        */
/*! \file output_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Abdalrhman Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of OutputManager functions.
 **
 ** Implementation of OutputManager functions.
 **/

#include "smt/output_manager.h"

#include "smt/smt_engine.h"

namespace CVC4 {

OutputManager::OutputManager(SmtEngine* smt) : d_smt(smt) {}

const Printer& OutputManager::getPrinter() const
{
  return *d_smt->getPrinter();
}

std::ostream& OutputManager::getDumpOut() const
{
  return *d_smt->getOptions().getOut();
}

}  // namespace CVC4
