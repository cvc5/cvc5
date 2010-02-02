/*********************                                           -*- C++ -*-  */
/** cnf_stream.cpp
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** A CNF converter that takes in asserts and has the side effect
 ** of given an equisatisfiable stream of assertions to PropEngine.
 **/

#include "prop/cnf_stream.h"
#include "prop/prop_engine.h"
#include "expr/node.h"
#include "util/Assert.h"

#include <queue>

using namespace CVC4::prop::minisat;
using namespace std;

namespace CVC4 {
namespace prop {

CnfStream::CnfStream(PropEngine *pe) :
  d_propEngine(pe) {
}

TseitinCnfStream::TseitinCnfStream(PropEngine *pe) :
  CnfStream(pe) {
}

void CnfStream::insertClauseIntoStream(vec<Lit> & c) {
  d_propEngine->assertClause(c);
}

void CnfStream::insertClauseIntoStream(minisat::Lit a) {
  vec<Lit> clause(1);
  clause[0] = a;
  insertClauseIntoStream(clause);
}
void CnfStream::insertClauseIntoStream(minisat::Lit a, minisat::Lit b) {
  vec<Lit> clause(2);
  clause[0] = a;
  clause[1] = b;
  insertClauseIntoStream(clause);
}
void CnfStream::insertClauseIntoStream(minisat::Lit a, minisat::Lit b,
                                       minisat::Lit c) {
  vec<Lit> clause(3);
  clause[0] = a;
  clause[1] = b;
  clause[2] = c;
  insertClauseIntoStream(clause);
}

bool CnfStream::isCached(const Node & n) const {
  return d_translationCache.find(n) != d_translationCache.end();
}

Lit CnfStream::lookupInCache(const Node & n) const {
  Assert(isCached(n));
  return d_translationCache.find(n)->second;
}

void CnfStream::flushCache() {
  d_translationCache.clear();
}

void CnfStream::registerMapping(const Node & node, Lit lit, bool atom) {
  //Prop engine does not need to know this mapping
  d_translationCache.insert(make_pair(node, lit));
  if(atom)
    d_propEngine->registerAtom(node, lit);
}

Lit CnfStream::acquireFreshLit(const Node & n) {
  return d_propEngine->requestFreshLit();
}

Lit CnfStream::aquireAndRegister(const Node & node, bool atom) {
  Lit l = acquireFreshLit(node);
  registerMapping(node, l, atom);
  return l;
}

/***********************************************/
/***********************************************/
/************ End of CnfStream *****************/
/***********************************************/
/***********************************************/

Lit TseitinCnfStream::handleAtom(const Node & n) {
  Lit l = aquireAndRegister(n, true);
  switch(n.getKind()) { /* TRUE and FALSE are handled specially. */
  case TRUE:
    insertClauseIntoStream(l);
    break;
  case FALSE:
    insertClauseIntoStream(~l);
    break;
  default: //Does nothing else
    break;
  }
  return l;
}

Lit TseitinCnfStream::handleXor(const Node & n) {
  // n: a XOR b

  Lit a = recTransform(n[0]);
  Lit b = recTransform(n[1]);

  Lit l = aquireAndRegister(n);

  insertClauseIntoStream(a, b, ~l);
  insertClauseIntoStream(a, ~b, l);
  insertClauseIntoStream(~a, b, l);
  insertClauseIntoStream(~a, ~b, ~l);

  return l;
}

/* For a small efficiency boost target needs to already be allocated to have
 size of the number of children of n.
 */
void TseitinCnfStream::mapRecTransformOverChildren(const Node& n,
                                                   vec<Lit> & target) {
  Assert(target.size() == n.getNumChildren());

  int i = 0;
  Node::iterator subExprIter = n.begin();

  while(subExprIter != n.end()) {
    Lit equivalentLit = recTransform(*subExprIter);
    target[i] = equivalentLit;
    ++subExprIter;
    ++i;
  }
}

Lit TseitinCnfStream::handleOr(const Node& n) {
  //child_literals
  vec<Lit> lits(n.getNumChildren());
  mapRecTransformOverChildren(n, lits);

  Lit e = aquireAndRegister(n);

  /* e <-> (a1 | a2 | a3 | ...)
   *: e -> (a1 | a2 | a3 | ...)
   * : ~e | (
   * : ~e | a1 | a2 | a3 | ...
   * e <- (a1 | a2 | a3 | ...)
   * : e <- (a1 | a2 | a3 |...)
   * : e | ~(a1 | a2 | a3 |...)
   * : 
   * : (e | ~a1) & (e |~a2) & (e & ~a3) & ...
   */

  vec<Lit> c;
  c.push(~e);

  for(int index = 0; index < lits.size(); ++index) {
    Lit a = lits[index];
    c.push(a);
    insertClauseIntoStream(e, ~a);
  }
  insertClauseIntoStream(c);

  return e;
}

/* TODO: this only supports 2-ary <=> nodes atm.
 * Should this be changed?
 */
Lit TseitinCnfStream::handleIff(const Node& n) {
  Assert(n.getKind() == IFF); Assert(n.getNumChildren() == 2);
  // n: a <=> b;

  Lit a = recTransform(n[0]);
  Lit b = recTransform(n[1]);

  Lit l = aquireAndRegister(n);

  /* l <-> (a<->b)
   * : l -> ((a-> b) & (b->a))
   * : ~l | ((~a | b) & (~b |a))
   * : (~a | b | ~l ) & (~b | a | ~l)
   * 
   * : (a<->b) -> l
   * : ~((a & b) | (~a & ~b)) | l
   * : (~(a & b)) & (~(~a & ~b)) | l
   * : ((~a | ~b) & (a | b)) | l
   * : (~a | ~b | l) & (a | b | l)
   */

  insertClauseIntoStream(~a, b, ~l);
  insertClauseIntoStream(a, ~b, ~l);
  insertClauseIntoStream(~a, ~b, l);
  insertClauseIntoStream(a, b, l);

  return l;
}

Lit TseitinCnfStream::handleAnd(const Node& n) {
  //TODO: we know the exact size of the this.
  //Dynamically allocated array would have less overhead no?
  vec<Lit> lits(n.getNumChildren());
  mapRecTransformOverChildren(n, lits);

  Lit e = aquireAndRegister(n);

  /* e <-> (a1 & a2 & a3 & ...)
   * : e -> (a1 & a2 & a3 & ...)
   * : ~e | (a1 & a2 & a3 & ...)
   * : (~e | a1) & (~e | a2) & ...
   * e <- (a1 & a2 & a3 & ...)
   * : e <- (a1 & a2 & a3 & ...)
   * : e | ~(a1 & a2 & a3 & ...)
   * : e | (~a1 | ~a2 | ~a3 | ...)
   * : e | ~a1 | ~a2 | ~a3 | ...
   */

  vec<Lit> c;
  c.push(e);
  for(int index = 0; index < lits.size(); ++index) {
    Lit a = lits[index];
    c.push(~a);
    insertClauseIntoStream(~e, a);
  }
  insertClauseIntoStream(c);

  return e;
}

Lit TseitinCnfStream::handleImplies(const Node & n) {
  Assert(n.getKind() == IMPLIES);
  // n: a => b;

  Lit a = recTransform(n[0]);
  Lit b = recTransform(n[1]);

  Lit l = aquireAndRegister(n);

  /* l <-> (a->b)
   * (l -> (a->b)) & (l <- (a->b))
   *  : l -> (a -> b)
   *  : ~l | (~ a | b)
   *  : (~l | ~a | b)
   * (~l | ~a | b) & (l<- (a->b))
   *  : (a->b) -> l
   *  : ~(~a | b) | l
   *  : (a & ~b) | l
   *  : (a | l) & (~b | l)
   * (~l | ~a | b) & (a | l) & (~b | l)
   */

  insertClauseIntoStream(a, l);
  insertClauseIntoStream(~b, l);
  insertClauseIntoStream(~l, ~a, b);

  return l;
}

Lit TseitinCnfStream::handleNot(const Node & n) {
  Assert(n.getKind() == NOT);

  // n : NOT m
  Node m = n[0];
  Lit equivM = recTransform(m);

  registerMapping(n, ~equivM, false);

  return equivM;
}

//FIXME: This function is a major hack! Should be changed ASAP
//Assumes binary no else if branchs, and that ITEs 
Lit TseitinCnfStream::handleIte(const Node & n) {
  Assert(n.getKind() == ITE);

  // n : IF c THEN t ELSE f ENDIF;
  Lit c = recTransform(n[0]);
  Lit t = recTransform(n[1]);
  Lit f = recTransform(n[2]);

  // d <-> IF c THEN tB ELSE fb
  // : d -> (c & tB) | (~c & fB)
  // : ~d | ( (c & tB) | (~c & fB) )
  // :          x | (y & z) = (x | y) & (x | z)
  // : ~d | ( ((c & t) | ~c ) & ((c & t) | f ) )
  // : ~d | ( (((c | ~c) & (~c | t))) & ((c | f) & (f | t)) )
  // : ~d | ( (~c | t) & (c | f) & (f | t) )
  // : (~d | ~c | t) & (~d | c | f) & (~d | f | t)

  // : ~d | (c & t & f)
  // : (~d | c)  & (~d | t) & (~d | f)
  // ( IF c THEN tB ELSE fb) -> d
  // :~((c & tB) | (~c & fB)) | d
  // : ((~c | ~t)& ( c |~fb)) | d
  // : (~c | ~ t | d) & (c | ~f | d)

  Lit d = aquireAndRegister(n);

  insertClauseIntoStream(~d, ~c, t);
  insertClauseIntoStream(~d, c, f);
  insertClauseIntoStream(~d, f, t);
  insertClauseIntoStream(~c, ~t, d);
  insertClauseIntoStream(c, ~f, d);

  return d;
}

//FIXME: This function is a major hack! Should be changed ASAP
//TODO: Should be moved. Not sure where...
//TODO: Should use positive definition, i.e. what kinds are atomic.
bool atomic(const Node & n) {
  switch(n.getKind()) {
  case NOT:
  case XOR:
  case ITE:
  case IFF:
  case OR:
  case AND:
    return false;
  default:
    return true;
  }
}

//TODO: The following code assumes everthing is either
// an atom or is a logical connective. This ignores quantifiers and lambdas.
Lit TseitinCnfStream::recTransform(const Node & n) {
  if(isCached(n)) {
    return lookupInCache(n);
  }

  if(atomic(n)) {
    return handleAtom(n);
  } else {
    //Assume n is a logical connective
    switch(n.getKind()) {
    case NOT:
      return handleNot(n);
    case XOR:
      return handleXor(n);
    case ITE:
      return handleIte(n);
    case IFF:
      return handleIff(n);
    case OR:
      return handleOr(n);
    case AND:
      return handleAnd(n);
    default:
      Unreachable();
    }
  }
}

void TseitinCnfStream::convertAndAssert(const Node & n) {
  //n has already been mapped so use the previous result
  if(isCached(n)) {
    Lit l = lookupInCache(n);
    insertClauseIntoStream(l);
    return;
  }

  Lit e = recTransform(n);
  insertClauseIntoStream(e);

  //I've commented the following section out because it uses a bit too much intelligence.

  /*
   if(n.getKind() == AND){
   // this code is required to efficiently flatten and
   // assert each part of the node.
   // This would be rendered unnessecary if the input was given differently
   queue<Node> and_queue;
   and_queue.push(n);

   //This was changed to use a queue due to pressure on the C stack.

   //TODO: this does no cacheing of what has been asserted.
   //Low hanging fruit
   while(!and_queue.empty()){
   Node curr = and_queue.front();
   and_queue.pop();
   if(curr.getKind() == AND){
   for(Node::iterator i = curr.begin(); i != curr.end(); ++i){
   and_queue.push(*i);
   }
   }else{
   convertAndAssert(curr);
   }
   }
   }else if(n.getKind() == OR){
   //This is special cased so minimal translation is done for things that
   //are already in CNF so minimal work is done on clauses.
   vec<Lit> c;
   for(Node::iterator i = n.begin(); i != n.end(); ++i){
   Lit cl = recTransform(*i);
   c.push(cl);
   }
   insertClauseIntoStream(c);
   }else{
   Lit e = recTransform(n);
   insertClauseIntoStream( e );
   }
   */
}

}/* CVC4::prop namespace */
}/* CVC4 namespace */
