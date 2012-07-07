/*********************                                                        */
/*! \file arithvar.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): dejan, mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Defines ArithVar which is the internal representation of variables in arithmetic
 **
 ** This defines ArithVar which is the internal representation of variables in
 ** arithmetic. This is a typedef from Index to ArithVar.
 ** This file also provides utilities for ArithVars.
 **/


#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__ARITHVAR_H
#define __CVC4__THEORY__ARITH__ARITHVAR_H

#include <limits>
#include <ext/hash_map>
#include "expr/node.h"
#include "context/cdhashset.h"
#include "context/cdhashset.h"

#include "util/index.h"

namespace CVC4 {
namespace theory {
namespace arith {

typedef Index ArithVar;
const ArithVar ARITHVAR_SENTINEL = std::numeric_limits<ArithVar>::max();

//Maps from Nodes -> ArithVars, and vice versa
typedef __gnu_cxx::hash_map<Node, ArithVar, NodeHashFunction> NodeToArithVarMap;
typedef __gnu_cxx::hash_map<ArithVar, Node> ArithVarToNodeMap;

/**
 * ArithVarCallBack provides a mechanism for agreeing on callbacks while
 * breaking mutual recursion inclusion order problems.
 */
class ArithVarCallBack {
public:
  virtual void operator()(ArithVar x) = 0;
};

class TNodeCallBack {
public:
  virtual void operator()(TNode n) = 0;
};

class NodeCallBack {
public:
  virtual void operator()(Node n) = 0;
};

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__ARITHVAR_H */
