/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli, Andrew Reynolds
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

#include "cvc5parser_private.h"

#ifndef CVC5__PARSER__CVC_H
#define CVC5__PARSER__CVC_H

#include "api/cpp/cvc5.h"
#include "parser/parser.h"

namespace cvc5 {

namespace parser {

class Cvc : public Parser
{
  friend class ParserBuilder;

 public:
  void forceLogic(const std::string& logic) override;

  /** Updates name to the tester name of cons, e.g. "is_cons" */
  bool getTesterName(api::Term cons, std::string& name) override;

 protected:
  Cvc(api::Solver* solver,
      SymbolManager* sm,
      Input* input,
      bool strictMode = false,
      bool parseOnly = false)
      : Parser(solver, sm, input, strictMode, parseOnly)
  {
  }
};

}  // namespace parser
}  // namespace cvc5

#endif /* CVC5__PARSER__CVC_H */
