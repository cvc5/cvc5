/*********************                                                        */
/*! \file cvc.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The parser class for the CVC language.
 **
 ** The parser class for the CVC language.
 **/

#include "cvc4parser_private.h"

#ifndef CVC4__PARSER__CVC_H
#define CVC4__PARSER__CVC_H

#include "api/cvc4cpp.h"
#include "parser/parser.h"
#include "smt/command.h"

namespace CVC4 {

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
      Input* input,
      bool strictMode = false,
      bool parseOnly = false)
      : Parser(solver, input, strictMode, parseOnly)
  {
  }
};

}  // namespace parser
}  // namespace CVC4

#endif /* CVC4__PARSER__CVC_H */
