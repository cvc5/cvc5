/*********************                                                        */
/*! \file proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Morgan Deters, Mathias Preiner
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

#include "cvc4_public.h"

#ifndef CVC4__PROOF_H
#define CVC4__PROOF_H

#include <iosfwd>
#include <unordered_map>

namespace CVC4 {

class Expr;
class ProofLetCount;
struct ExprHashFunction;

typedef std::unordered_map<Expr, ProofLetCount, ExprHashFunction> ProofLetMap;

class CVC4_PUBLIC Proof
{
 public:
  virtual ~Proof() {}
  virtual void toStream(std::ostream& out) const = 0;
  virtual void toStream(std::ostream& out, const ProofLetMap& map) const = 0;
};/* class Proof */

}/* CVC4 namespace */

#endif /* CVC4__PROOF_H */
