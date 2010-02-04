/*********************                                                        */
/** cnf_stream.cpp
 ** Original author: taking
 ** Major contributors: dejan
 ** Minor contributors (to current version): mdeters
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

using namespace std;

namespace CVC4 {
namespace prop {

CnfStream::CnfStream(PropEngine *pe) :
  d_propEngine(pe) {
}

TseitinCnfStream::TseitinCnfStream(PropEngine *pe) :
  CnfStream(pe) {
}

void CnfStream::insertClauseIntoStream(SatClause& c) {
  Debug("cnf") << "Inserting into stream " << c << endl;
  d_propEngine->assertClause(c);
}

void CnfStream::insertClauseIntoStream(SatLiteral a) {
  SatClause clause(1);
  clause[0] = a;
  insertClauseIntoStream(clause);
}
void CnfStream::insertClauseIntoStream(SatLiteral a, SatLiteral b) {
  SatClause clause(2);
  clause[0] = a;
  clause[1] = b;
  insertClauseIntoStream(clause);
}
void CnfStream::insertClauseIntoStream(SatLiteral a, SatLiteral b, SatLiteral c) {
  SatClause clause(3);
  clause[0] = a;
  clause[1] = b;
  clause[2] = c;
  insertClauseIntoStream(clause);
}

bool CnfStream::isCached(const Node& n) const {
  return d_translationCache.find(n) != d_translationCache.end();
}

SatLiteral CnfStream::lookupInCache(const Node& n) const {
  Assert(isCached(n),
      "Node is not in cnf translation cache");
  return d_translationCache.find(n)->second;
}

void CnfStream::flushCache() {
  Debug("cnf") << "flushing the translation cache" << endl;
  d_translationCache.clear();
}

void CnfStream::cacheTranslation(const Node& node, SatLiteral lit) {
  Debug("cnf") << "caching translation " << node << " to " << lit << endl;
  d_translationCache.insert(make_pair(node, lit));
}

SatLiteral CnfStream::aquireAndRegister(const Node& node, bool atom) {
  SatVariable var = atom ? d_propEngine->registerAtom(node)
      : d_propEngine->requestFreshVar();
  SatLiteral lit(var);
  cacheTranslation(node, lit);
  return lit;
}

bool CnfStream::isAtomMapped(const Node& n) const {
  return d_propEngine->isAtomMapped(n);
}

SatVariable CnfStream::lookupAtom(const Node& n) const {
  return d_propEngine->lookupAtom(n);
}

/***********************************************/
/***********************************************/
/************ End of CnfStream *****************/
/***********************************************/
/***********************************************/

SatLiteral TseitinCnfStream::handleAtom(const Node& n) {
  Assert(n.isAtomic(), "handleAtom(n) expects n to be an atom");

  Debug("cnf") << "handling atom" << endl;

  SatLiteral l = aquireAndRegister(n, true);
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

SatLiteral TseitinCnfStream::handleXor(const Node& n) {
  // n: a XOR b

  SatLiteral a = recTransform(n[0]);
  SatLiteral b = recTransform(n[1]);

  SatLiteral l = aquireAndRegister(n);

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
                                                   SatClause& target) {
  Assert((unsigned)target.size() == n.getNumChildren(),
      "Size of the children must be the same the constructed clause");

  int i = 0;
  Node::iterator subExprIter = n.begin();

  while(subExprIter != n.end()) {
    SatLiteral equivalentLit = recTransform(*subExprIter);
    target[i] = equivalentLit;
    ++subExprIter;
    ++i;
  }
}

SatLiteral TseitinCnfStream::handleOr(const Node& n) {
  //child_literals
  SatClause lits(n.getNumChildren());
  mapRecTransformOverChildren(n, lits);

  SatLiteral e = aquireAndRegister(n);

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

  SatClause c(1 + lits.size());

  for(int index = 0; index < lits.size(); ++index) {
    SatLiteral a = lits[index];
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
SatLiteral TseitinCnfStream::handleIff(const Node& n) {
  Assert(n.getKind() == IFF);
  Assert(n.getNumChildren() == 2);
  // n: a <=> b;

  SatLiteral a = recTransform(n[0]);
  SatLiteral b = recTransform(n[1]);

  SatLiteral l = aquireAndRegister(n);

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

SatLiteral TseitinCnfStream::handleAnd(const Node& n) {
  Assert(n.getKind() == AND);
  Assert(n.getNumChildren() >= 1);

  //TODO: we know the exact size of the this.
  //Dynamically allocated array would have less overhead no?
  SatClause lits(n.getNumChildren());
  mapRecTransformOverChildren(n, lits);

  SatLiteral e = aquireAndRegister(n);

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

  SatClause c(lits.size() + 1);
  for(int index = 0; index < lits.size(); ++index) {
    SatLiteral a = lits[index];
    c[index] = (~a);
    insertClauseIntoStream(~e, a);
  }
  c[lits.size()] = e;

  insertClauseIntoStream(c);

  return e;
}

SatLiteral TseitinCnfStream::handleImplies(const Node& n) {
  Assert(n.getKind() == IMPLIES);
  Assert(n.getNumChildren() == 2);
  // n: a => b;

  SatLiteral a = recTransform(n[0]);
  SatLiteral b = recTransform(n[1]);

  SatLiteral l = aquireAndRegister(n);

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

SatLiteral TseitinCnfStream::handleNot(const Node& n) {
  Assert(n.getKind() == NOT);
  Assert(n.getNumChildren() == 1);

  // n : NOT m
  Node m = n[0];
  SatLiteral equivM = recTransform(m);

  SatLiteral equivN = ~equivM;

  cacheTranslation(n, equivN);

  return equivN;
}

SatLiteral TseitinCnfStream::handleIte(const Node& n) {
  Assert(n.getKind() == ITE);
  Assert(n.getNumChildren() == 3);

  // n : IF c THEN t ELSE f ENDIF;
  SatLiteral c = recTransform(n[0]);
  SatLiteral t = recTransform(n[1]);
  SatLiteral f = recTransform(n[2]);

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

  SatLiteral d = aquireAndRegister(n);

  insertClauseIntoStream(~d, ~c, t);
  insertClauseIntoStream(~d, c, f);
  insertClauseIntoStream(~d, f, t);
  insertClauseIntoStream(~c, ~t, d);
  insertClauseIntoStream(c, ~f, d);

  return d;
}

//TODO: The following code assumes everything is either
// an atom or is a logical connective. This ignores quantifiers and lambdas.
SatLiteral TseitinCnfStream::recTransform(const Node& n) {
  if(isCached(n)) {
    return lookupInCache(n);
  }

  if(n.isAtomic()) {

    /* Unfortunately we need to potentially allow
     * for n to be to the Atom <-> Var map but not the
     * translation cache.
     * This is because the translation cache can be flushed.
     * It is really not clear where this check should go, but
     * it needs to be done.
     */
    if(isAtomMapped(n)) {
      /* Puts the atom in the translation cache after looking it up.
       * Avoids doing 2 map lookups for this atom in the future.
       */
      SatLiteral l(lookupAtom(n));
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

void TseitinCnfStream::convertAndAssert(const Node& n) {
  SatLiteral e = recTransform(n);
  insertClauseIntoStream(e);
}

}/* CVC4::prop namespace */
}/* CVC4 namespace */
