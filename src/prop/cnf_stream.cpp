/*********************                                           -*- C++ -*-  */
/** cnf_stream.cpp
 ** Original author: taking
 ** Major contributors: dejan
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
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
#include "util/output.h"

#include <queue>

using namespace CVC4::prop::minisat;
using namespace std;

namespace CVC4 {
namespace prop {

bool atomic(const Node & n);


static void printVar(ostream & out, Var v){
  out << v;
}

static void printLit(ostream & out, Lit l) {
  const char * s = (sign(l))?"~":" ";
  out << s << var(l);
}


static void printClause(ostream & out, vec<Lit> & c) {
  out << "clause:";  
  for(int i=0;i<c.size();i++){
    out << " ";
    printLit(out, c[i]) ;
  }
  out << ";" << endl;
}



CnfStream::CnfStream(PropEngine *pe) :
  d_propEngine(pe) {
}

TseitinCnfStream::TseitinCnfStream(PropEngine *pe) :
  CnfStream(pe) {
}



void CnfStream::insertClauseIntoStream(vec<Lit> & c) {
  Debug("cnf") << "Inserting into stream ";
  printClause(Debug("cnf"),c);

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
  Assert(isCached(n),
	 "Node is not in cnf translation cache");
  return d_translationCache.find(n)->second;
}

void CnfStream::flushCache() {
  Debug("cnf") << "flushing the translation cache" << endl;
  d_translationCache.clear();
}

void CnfStream::cacheTranslation(const Node & node, Lit lit) {
  Debug("cnf") << "cacheing translation "<< node << " to ";
  printLit(Debug("cnf"),lit);
  Debug("cnf") << endl;
  
  d_translationCache.insert(make_pair(node, lit));
}

Lit CnfStream::aquireAndRegister(const Node & node, bool atom) {
  Var v = atom ?
      d_propEngine->registerAtom(node)
    : d_propEngine->requestFreshVar();
  Lit l(v);
  cacheTranslation(node, l);
  return l;
}

bool CnfStream::isAtomMapped(const Node & n) const{
  return d_propEngine->isAtomMapped(n);
}
  
Var CnfStream::lookupAtom(const Node & n) const{
  return d_propEngine->lookupAtom(n);
}

/***********************************************/
/***********************************************/
/************ End of CnfStream *****************/
/***********************************************/
/***********************************************/

Lit TseitinCnfStream::handleAtom(const Node & n) {
  Assert(atomic(n), "handleAtom(n) expects n to be an atom");

  Debug("cnf") << "handling atom" << endl;

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
  Assert(target.size() == n.getNumChildren(),
	 "Size of the children must be the same the constructed clause");

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

  vec<Lit> c(1 + lits.size());


  for(int index = 0; index < lits.size(); ++index) {
    Lit a = lits[index];
    c[index] = a;
    insertClauseIntoStream(e, ~a);
  }
  c[lits.size()] = ~e;
  insertClauseIntoStream(c);

  return e;
}

/* TODO: this only supports 2-ary <=> nodes atm.
 * Should this be changed?
 */
Lit TseitinCnfStream::handleIff(const Node& n) {
  Assert(n.getKind() == IFF); 
  Assert(n.getNumChildren() == 2);
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
  Assert(n.getKind() == AND); 
  Assert(n.getNumChildren() >= 1);

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

  vec<Lit> c(lits.size()+1);
  for(int index = 0; index < lits.size(); ++index) {
    Lit a = lits[index];
    c[index] = (~a);
    insertClauseIntoStream(~e, a);
  }
  c[lits.size()] = e;

  insertClauseIntoStream(c);

  return e;
}

Lit TseitinCnfStream::handleImplies(const Node & n) {
  Assert(n.getKind() == IMPLIES);
  Assert(n.getNumChildren() == 2);
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
  Assert(n.getNumChildren() == 1);

  // n : NOT m
  Node m = n[0];
  Lit equivM = recTransform(m);

  Lit equivN = ~equivM;

  cacheTranslation(n, equivN);

  return equivN;
}

//FIXME: This function is a major hack! Should be changed ASAP
//Assumes binary no else if branchs, and that ITEs 
Lit TseitinCnfStream::handleIte(const Node & n) {
  Assert(n.getKind() == ITE);
  Assert(n.getNumChildren() == 3);

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
  case IMPLIES:
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
    
    /* Unforunately we need to potentially allow
     * for n to be to the Atom <-> Var map but not the
     * translation cache.
     * This is because the translation cache can be flushed.
     * It is really not clear where this check should go, but
     * it needs to be done.
     */
    if(isAtomMapped(n)){
      /* Puts the atom in the translation cache after looking it up.
       * Avoids doing 2 map lookups for this atom in the future.
       */
      Lit l(lookupAtom(n));
      cacheTranslation(n, l);
      return l;
    }
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
    case IMPLIES:
      return handleImplies(n);
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
  Lit e = recTransform(n);
  insertClauseIntoStream(e);
}

}/* CVC4::prop namespace */
}/* CVC4 namespace */
