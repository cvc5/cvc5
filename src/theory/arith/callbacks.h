/*********************                                                        */
/*! \file callbacks.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Morgan Deters, Paul Meng
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

#include "expr/node.h"
#include "theory/arith/arithvar.h"
#include "theory/arith/bound_counts.h"
#include "theory/arith/constraint_forward.h"
#include "theory/arith/theory_arith_private_forward.h"
#include "util/rational.h"

namespace CVC4 {
namespace theory {
namespace arith {

/**
 * ArithVarCallBack provides a mechanism for agreeing on callbacks while
 * breaking mutual recursion inclusion order problems.
 */
class ArithVarCallBack {
public:
  virtual ~ArithVarCallBack() {}
  virtual void operator()(ArithVar x) = 0;
};

/**
 * Requests arithmetic variables for internal use,
 * and releases arithmetic variables that are no longer being used.
 */
class ArithVarMalloc {
public:
  virtual ~ArithVarMalloc() {}
  virtual ArithVar request() = 0;
  virtual void release(ArithVar v) = 0;
};

class TNodeCallBack {
public:
  virtual ~TNodeCallBack() {}
  virtual void operator()(TNode n) = 0;
};

class NodeCallBack {
public:
  virtual ~NodeCallBack() {}
  virtual void operator()(Node n) = 0;
};

class RationalCallBack {
public:
  virtual ~RationalCallBack() {}
  virtual Rational operator()() const = 0;
};

class SetupLiteralCallBack : public TNodeCallBack {
private:
  TheoryArithPrivate& d_arith;
public:
  SetupLiteralCallBack(TheoryArithPrivate& ta);
  void operator()(TNode lit) override;
};

class DeltaComputeCallback : public RationalCallBack {
private:
  const TheoryArithPrivate& d_ta;
public:
  DeltaComputeCallback(const TheoryArithPrivate& ta);
  Rational operator()() const override;
};

class BasicVarModelUpdateCallBack : public ArithVarCallBack{
private:
  TheoryArithPrivate& d_ta;
public:
  BasicVarModelUpdateCallBack(TheoryArithPrivate& ta);
  void operator()(ArithVar x) override;
};

class TempVarMalloc : public ArithVarMalloc {
private:
  TheoryArithPrivate& d_ta;
public:
  TempVarMalloc(TheoryArithPrivate& ta);
  ArithVar request() override;
  void release(ArithVar v) override;
};

class RaiseConflict {
private:
  TheoryArithPrivate& d_ta;
public:
  RaiseConflict(TheoryArithPrivate& ta);

  /** Calls d_ta.raiseConflict(c) */
  void raiseConflict(ConstraintCP c) const;
};

class FarkasConflictBuilder {
private:
  RationalVector d_farkas;
  ConstraintCPVec d_constraints;
  ConstraintCP d_consequent;
  bool d_consequentSet;
public:

  /**
   * Constructs a new FarkasConflictBuilder.
   */
  FarkasConflictBuilder();

  /**
   * Adds an antecedent constraint to the conflict under construction
   * with the farkas coefficient fc * mult.
   *
   * The value mult is either 1 or -1.
   */
  void addConstraint(ConstraintCP c, const Rational& fc, const Rational& mult);

  /**
   * Adds an antecedent constraint to the conflict under construction
   * with the farkas coefficient fc.
   */
  void addConstraint(ConstraintCP c, const Rational& fc);
  
  /**
   * Makes the last constraint added the consequent.
   * Can be done exactly once per reset().
   */
  void makeLastConsequent();
  
  /**
   * Turns the antecendents into a proof of the negation of one of the
   * antecedents.
   *
   * The buffer is no longer underConstruction afterwards.
   *
   * precondition:
   * - At least two constraints have been asserted.
   * - makeLastConsequent() has been called.
   *
   * postcondition: The returned constraint is in conflict.
   */
  ConstraintCP commitConflict();

  /** Returns true if a conflict has been pushed back since the last reset. */
  bool underConstruction() const;
  
  /** Returns true if the consequent has been set since the last reset. */
  bool consequentIsSet() const;

  /** Resets the state of the buffer. */
  void reset();
};


class RaiseEqualityEngineConflict {
private:
  TheoryArithPrivate& d_ta;
  
public:
  RaiseEqualityEngineConflict(TheoryArithPrivate& ta);

  /* If you are not an equality engine, don't use this! */
  void raiseEEConflict(Node n) const;
};

class BoundCountingLookup {
private:
  TheoryArithPrivate& d_ta;
public:
  BoundCountingLookup(TheoryArithPrivate& ta);
  const BoundsInfo& boundsInfo(ArithVar basic) const;
  BoundCounts atBounds(ArithVar basic) const;
  BoundCounts hasBounds(ArithVar basic) const;
};

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
