
#include "context/cdlist.h"
#include "context/context.h"
#include "theory/arith/delta_rational.h"
#include "expr/node.h"


#ifndef __CVC4__THEORY__ARITH__PARTIAL_MODEL_H
#define __CVC4__THEORY__ARITH__PARTIAL_MODEL_H

namespace CVC4 {
namespace theory {
namespace arith {

typedef CVC4::context::CDList<TNode> BoundsList;

namespace partial_model {
struct DeltaRationalCleanupStrategy{
  static void cleanup(DeltaRational* dq){
    Debug("arithgc") << "cleaning up  " << dq << "\n";
    delete dq;
  }
};

struct AssignmentAttrID;
typedef expr::Attribute<AssignmentAttrID,DeltaRational*,DeltaRationalCleanupStrategy> Assignment;

// TODO should have a cleanup see bug #110
struct LowerBoundAttrID;
typedef expr::CDAttribute<LowerBoundAttrID,DeltaRational*> LowerBound;

// TODO should have a cleanup see bug #110
struct UpperBoundAttrID;
typedef expr::CDAttribute<UpperBoundAttrID,DeltaRational*> UpperBound;

struct LowerConstraintAttrID;
typedef expr::CDAttribute<LowerConstraintAttrID,TNode> LowerConstraint;

struct UpperConstraintAttrID;
typedef expr::CDAttribute<UpperConstraintAttrID,TNode> UpperConstraint;

typedef CVC4::context::CDList<TNode> BoundsList;

struct BoundsListCleanupStrategy{
  static void cleanup(BoundsList* bl){
    Debug("arithgc") << "cleaning up  " << bl << "\n";
    bl->deleteSelf();
  }
};


/** Unique name to use for constructing ECAttr. */
struct BoundsListID;

/**
 * BoundsListAttr is the attribute that maps a node to atoms .
 */
typedef expr::Attribute<BoundsListID,
                        BoundsList*,
                        BoundsListCleanupStrategy> BoundsListAttr;

}; /*namespace partial_model*/

struct TheoryArithPropagatedID;
typedef expr::CDAttribute<TheoryArithPropagatedID, bool> TheoryArithPropagated;

/**
 * Validates that a node constraint has the following form:
 *   constraint: x |><| c
 * where |><| is either <, <=, ==, >=, LT and c is a constant rational.
 */
bool validateConstraint(TNode constraint){
  using namespace CVC4::kind;
  switch(constraint.getKind()){
  case LT:case LEQ: case EQUAL: case GEQ: case GT: break;
  default: return false;
  }

  if(constraint[0].getMetaKind() != metakind::VARIABLE) return false;
  return constraint[1].getKind() == CONST_RATIONAL;
}

void addBound(TNode constraint){
  Assert(validateConstraint(constraint));
  TNode x = constraint[0];

  BoundsList* bl;
  if(!x.getAttribute(partial_model::BoundsListAttr(), bl)){
    //TODO
    context::Context* context = NULL;
    bl = new (true) BoundsList(context);
    x.setAttribute(partial_model::BoundsListAttr(), bl);
  }
  bl->push_back(constraint);
}

inline int deltaCoeff(Kind k){
  switch(k){
  case kind::LT:
    return -1;
  case kind::GT:
    return 1;
  default:
    return 0;
  }
}


inline bool negateBoundPropogation(CVC4::Kind k, bool isLowerBound){
  /* !isLowerBound
   * [x <= u && u < c] \=> x <  c
   * [x <= u && u < c] \=> x <= c
   * [x <= u && u < c] \=> !(x == c)
   * [x <= u && u < c] \=> !(x >= c)
   * [x <= u && u < c] \=> !(x >  c)
   */
  /* isLowerBound
   * [x >= l && l > c] \=> x > c
   * [x >= l && l > c] \=> x >= c
   * [x >= l && l > c] \=> !(x == c)
   * [x >= l && l > c] \=> !(x <= c)
   * [x >= l && l > c] \=> !(x < c)
   */
  using namespace CVC4::kind;
  switch(k){
  case LT:
  case LEQ:
    return isLowerBound;
  case EQUAL:
    return true;
  case GEQ:
  case GT:
    return !isLowerBound;
  default:
    Unreachable();
    return false;
  }
}

void propogateBound(TNode constraint, OutputChannel& oc, bool isLower){
  constraint.setAttribute(TheoryArithPropagated(),true);
  bool neg = negateBoundPropogation(constraint.getKind(), isLower);

  if(neg){
    oc.propagate(constraint.notNode(),false);
  }else{
    oc.propagate(constraint,false);
  }
}

void propagateBoundConstraints(TNode x, OutputChannel& oc){
  Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

  DeltaRational* l;
  DeltaRational* u;
  bool hasLowerBound = x.getAttribute(partial_model::LowerBound(), l);
  bool hasUpperBound = x.getAttribute(partial_model::UpperBound(), u);

  if(!(hasLowerBound || hasUpperBound)) return;
  BoundsList* bl;

  if(!x.getAttribute(partial_model::BoundsListAttr(), bl)) return;

  for(BoundsList::const_iterator iter = bl->begin(); iter != bl->end(); ++iter){
    TNode constraint = *iter;
    if(constraint.hasAttribute(TheoryArithPropagated())){
      continue;
    }
    //TODO improve efficiency Rational&
    Rational c = constraint[1].getConst<Rational>();
    Rational k(Integer(deltaCoeff(constraint.getKind())));
    DeltaRational ec(c, k);
    if(hasUpperBound && (*u) < ec ){
      propogateBound(constraint, oc, false);
    }
    if(hasLowerBound && (*l) > ec ){
      propogateBound(constraint, oc, true);
    }
  }
}

void setUpperBound(TNode x, DeltaRational& r){
  Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);
  DeltaRational* c;
  if(x.getAttribute(partial_model::UpperBound(), c)){
    *c = r;
  }else{
    c = new DeltaRational(r);
    x.setAttribute(partial_model::UpperBound(), c);
  }
}

void setLowerBound(TNode x, DeltaRational& r){
  Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);
  DeltaRational* c;
  if(x.getAttribute(partial_model::LowerBound(), c)){
    *c = r;
  }else{
    c = new DeltaRational(r);
    x.setAttribute(partial_model::LowerBound(), c);
  }
}
void setAssignment(TNode x, DeltaRational& r){
  Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);
  DeltaRational* c;
  if(x.getAttribute(partial_model::Assignment(), c)){
    *c = r;
  }else{
    c = new DeltaRational(r);
    x.setAttribute(partial_model::Assignment(), c);
  }
}

/** Must know that the bound exists both calling this! */
DeltaRational getUpperBound(TNode x){
  Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

  DeltaRational* assign;
  AlwaysAssert(x.getAttribute(partial_model::UpperBound(),assign));
  return *assign;
}


DeltaRational getLowerBound(TNode x){
  Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

  DeltaRational* assign;
  AlwaysAssert(x.getAttribute(partial_model::LowerBound(),assign));
  return *assign;
}

DeltaRational getAssignment(TNode x){
  Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

  DeltaRational* assign;
  AlwaysAssert(x.getAttribute(partial_model::Assignment(),assign));
  return *assign;
}

void setLowerConstraint(TNode constraint){
  TNode x = constraint[0];
  Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

  x.setAttribute(partial_model::LowerConstraint(),constraint);
}

void setUpperConstraint(TNode constraint){
  TNode x = constraint[0];
  Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

  x.setAttribute(partial_model::UpperConstraint(),constraint);
}
TNode getLowerConstraint(TNode x){
  Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

  TNode ret;
  AlwaysAssert(x.getAttribute(partial_model::LowerConstraint(),ret));
  return ret;
}

TNode getUpperConstraint(TNode x){
  Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

  TNode ret;
  AlwaysAssert(x.getAttribute(partial_model::UpperConstraint(),ret));
  return ret;
}

/**
 * x <= l
 * ? c < l
 */
bool belowLowerBound(TNode x, DeltaRational& c, bool strict){
  DeltaRational* l;
  if(!x.getAttribute(partial_model::LowerBound(), l)){
    // l = -\intfy
    // ? c < -\infty |-  _|_
    return false;
  }

  if(strict){
    return c < *l;
  }else{
    return c <= *l;
  }
}

/**
 * x <= u
 * ? c < u
 */
bool aboveUpperBound(TNode x, DeltaRational& c, bool strict){
  DeltaRational* u;
  if(!x.getAttribute(partial_model::UpperBound(), u)){
    // c = \intfy
    // ? c > \infty |-  _|_
    return false;
  }

  if(strict){
    return c > *u;
  }else{
    return c >= *u;
  }
}

bool strictlyBelowUpperBound(TNode x){
  DeltaRational* assign;
  AlwaysAssert(x.getAttribute(partial_model::Assignment(),assign));

  DeltaRational* u;
  if(!x.getAttribute(partial_model::UpperBound(), u)){ // u = \infty
    return true;
  }
  return *assign < *u;
}

bool strictlyAboveLowerBound(TNode x){
  DeltaRational* assign;
  AlwaysAssert(x.getAttribute(partial_model::Assignment(),assign));

  DeltaRational* l;
  if(!x.getAttribute(partial_model::LowerBound(), l)){ // l = -\infty
    return true;
  }
  return *l < *assign;
}

bool assignmentIsConsistent(TNode x){
  DeltaRational beta = getAssignment(x);

  //l_i <= beta(x_i) <= u_i
  return !aboveUpperBound(x,beta, true) && !belowLowerBound(x,beta,true);
}

}; /* namesapce arith */
}; /* namespace theory */
}; /* namespace CVC4 */



#endif /* __CVC4__THEORY__ARITH__PARTIAL_MODEL_H */
