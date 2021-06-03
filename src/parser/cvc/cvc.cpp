/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The parser class for the CVC language.
 */

#include "parser/cvc/cvc.h"
#include "smt/command.h"

namespace cvc5 {
namespace parser {

void Cvc::forceLogic(const std::string& logic)
{
  Parser::forceLogic(logic);
  preemptCommand(new SetBenchmarkLogicCommand(logic));
}

bool Cvc::getTesterName(api::Term cons, std::string& name)
{
  std::stringstream ss;
  ss << "is_" << cons;
  name = ss.str();
  return true;
}

}  // namespace parser
}  // namespace cvc5
