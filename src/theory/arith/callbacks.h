/*********************                                                        */
/*! \file callbacks.h
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/


#pragma once

#include "expr/node.h"
#include "util/rational.h"

#include "theory/arith/theory_arith_private_forward.h"
#include "theory/arith/arithvar.h"
#include "theory/arith/bound_counts.h"

namespace CVC4 {
namespace theory {
namespace arith {

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

class SetupLiteralCallBack : public TNodeCallBack {
private:
  TheoryArithPrivate& d_arith;
public:
  SetupLiteralCallBack(TheoryArithPrivate& ta) : d_arith(ta){}
  void operator()(TNode lit);
};

class DeltaComputeCallback : public RationalCallBack {
private:
  const TheoryArithPrivate& d_ta;
public:
  DeltaComputeCallback(const TheoryArithPrivate& ta) : d_ta(ta){}
  Rational operator()() const;
};

class BasicVarModelUpdateCallBack : public ArithVarCallBack{
private:
  TheoryArithPrivate& d_ta;
public:
  BasicVarModelUpdateCallBack(TheoryArithPrivate& ta) : d_ta(ta) {}
  void operator()(ArithVar x);
};

class TempVarMalloc : public ArithVarMalloc {
private:
  TheoryArithPrivate& d_ta;
public:
  TempVarMalloc(TheoryArithPrivate& ta) : d_ta(ta) {}
  ArithVar request();
  void release(ArithVar v);
};

class RaiseConflict : public NodeCallBack {
private:
  TheoryArithPrivate& d_ta;
public:
  RaiseConflict(TheoryArithPrivate& ta) : d_ta(ta) {}
  void operator()(Node n);
};

class BoundCountingLookup {
private:
  TheoryArithPrivate& d_ta;
public:
  BoundCountingLookup(TheoryArithPrivate& ta) : d_ta(ta) {}
  const BoundsInfo& boundsInfo(ArithVar basic) const;
  BoundCounts atBounds(ArithVar basic) const{
    return boundsInfo(basic).atBounds();
  }
  BoundCounts hasBounds(ArithVar basic) const {
    return boundsInfo(basic).hasBounds();
  }
};

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
