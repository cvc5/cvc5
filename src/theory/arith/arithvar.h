/*********************                                                        */
/*! \file arithvar.h
 ** \verbatim
 ** Original author: Tim King <taking@cs.nyu.edu>
 ** Major contributors: none
 ** Minor contributors (to current version): Morgan Deters <mdeters@cs.nyu.edu>
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
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

#include <ext/hash_map>
#include "expr/node.h"
#include "context/cdhashset.h"

#include "util/index.h"
#include "util/dense_map.h"

namespace CVC4 {
namespace theory {
namespace arith {

typedef Index ArithVar;
extern const ArithVar ARITHVAR_SENTINEL;

//Maps from Nodes -> ArithVars, and vice versa
typedef __gnu_cxx::hash_map<Node, ArithVar, NodeHashFunction> NodeToArithVarMap;
typedef DenseMap<Node> ArithVarToNodeMap;

/**
 * ArithVarCallBack provides a mechanism for agreeing on callbacks while
 * breaking mutual recursion inclusion order problems.
 */
class ArithVarCallBack {
public:
  virtual void operator()(ArithVar x) = 0;
};

/**
 * Requests arithmetic variables for internal use,
 * and releases arithmetic variables that are no longer being used.
 */
class ArithVarMalloc {
public:
  virtual ArithVar request() = 0;
  virtual void release(ArithVar v) = 0;
};

class TNodeCallBack {
public:
  virtual void operator()(TNode n) = 0;
};

class NodeCallBack {
public:
  virtual void operator()(Node n) = 0;
};

class RationalCallBack {
public:
  virtual Rational operator()() const = 0;
};

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__ARITHVAR_H */
