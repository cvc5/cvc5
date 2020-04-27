/*********************                                                        */
/*! \file proof_to_sexpr.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Conversion from ProofNode to s-expressions
 **/

#include "cvc4_private.h"

#ifndef CVC4__EXPR__PROOF_NODE_TO_SEXPR_H
#define CVC4__EXPR__PROOF_NODE_TO_SEXPR_H

#include <map>

#include "expr/node.h"
#include "expr/proof_node.h"

namespace CVC4 {

class ProofToSExpr
{
public:
  ProofToSExpr();
  ~ProofToSExpr(){}
  /** Convert the given proof node to an s-expression */
  Node convertToSExpr(std::shared_ptr<ProofNode> pn);  
private:
  /** map proof rules to a variable */
  std::map<PfRule, Node > d_pfrMap;
  /** Dummy ":args" marker */
  Node d_argsMarker;
  /** map proof nodes to their s-expression */
  std::map< std::shared_ptr<ProofNode>, Node > d_pnMap;
  /** get or make pf rule variable */
  Node getOrMkPfRuleVariable(PfRule r);
};

}  // namespace CVC4

#endif /* CVC4__EXPR__PROOF_RULE_H */
