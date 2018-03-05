/*********************                                                        */
/*! \file theory_idl.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Morgan Deters, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#pragma once

#include "cvc4_private.h"

#include "theory/theory.h"
#include "theory/idl/idl_model.h"
#include "theory/idl/idl_assertion_db.h"

namespace CVC4 {
namespace theory {
namespace idl {

/**
 * Handles integer difference logic (IDL) constraints.
 */
class TheoryIdl : public Theory {

  /** The current model */
  IDLModel d_model;

  /** The asserted constraints, organized by variable */
  IDLAssertionDB d_assertionsDB;

  /** Process a new assertion, returns false if in conflict */
  bool processAssertion(const IDLAssertion& assertion);

public:

  /** Theory constructor. */
  TheoryIdl(context::Context* c, context::UserContext* u, OutputChannel& out,
            Valuation valuation, const LogicInfo& logicInfo);

  /** Pre-processing of input atoms */
  Node ppRewrite(TNode atom) override;

  /** Check the assertions for satisfiability */
  void check(Effort effort) override;

  /** Identity string */
  std::string identify() const override { return "THEORY_IDL"; }

};/* class TheoryIdl */

}/* CVC4::theory::idl namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
