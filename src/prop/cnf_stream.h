/*********************                                                        */
/** cnf_stream.h
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
 ** This class takes a sequence of formulas.
 ** It outputs a stream of clauses that is propositional
 ** equisatisfiable with the conjunction of the formulas.
 ** This stream is maintained in an online fashion.
 **
 ** Unlike other parts of the system it is aware of the PropEngine's
 ** internals such as the representation and translation of 
 **/

#ifndef __CVC4__CNF_STREAM_H
#define __CVC4__CNF_STREAM_H

#include "expr/node.h"
#include "prop/sat.h"

#include <map>

namespace CVC4 {
namespace prop {

class PropEngine;

/**
 * Comments for the behavior of the whole class...
 * @author Tim King <taking@cs.nyu.edu>
 */
class CnfStream {

private:

  /**
   * d_propEngine is the PropEngine that the CnfStream interacts with directly
   * through the following functions:
   *    - insertClauseIntoStream
   *    - acquireFreshLit
   *    - registerMapping
   */
  PropEngine *d_propEngine;

  /**
   * Cache of what literal have been registered to a node. Not strictly needed
   * for correctness. This can be flushed when memory is under pressure.
   * TODO: Use attributes when they arrive
   */
  std::map<Node, SatLiteral> d_translationCache;

protected:

  bool isAtomMapped(const Node& n) const;

  SatVariable lookupAtom(const Node& node) const;

  /**
   * Uniform interface for sending a clause back to d_propEngine.
   * May want to have internal data-structures later on
   */
  void insertClauseIntoStream(SatClause& clause);
  void insertClauseIntoStream(SatLiteral a);
  void insertClauseIntoStream(SatLiteral a, SatLiteral b);
  void insertClauseIntoStream(SatLiteral a, SatLiteral b, SatLiteral c);

  //utilities for the translation cache;
  bool isCached(const Node& node) const;

  /**
   * Method comments...
   * @param n
   * @return returns ...
   */
  SatLiteral lookupInCache(const Node& n) const;

  //negotiates the mapping of atoms to literals with PropEngine
  void cacheTranslation(const Node& node, SatLiteral lit);

  SatLiteral aquireAndRegister(const Node& node, bool atom = false);

public:

  /**
   * Constructs a CnfStream that sends constructs an equisatisfiable set of clauses
   * and sends them to the given PropEngine.
   * @param propEngine
   */
  CnfStream(PropEngine* propEngine);

  /**
   * Empties the internal translation cache.
   */
  void flushCache();

  /**
   * Converts and asserts a formula.
   * @param node node to convert and assert
   */
  virtual void convertAndAssert(const Node& node) = 0;

}; /* class CnfStream */

/**
 * TseitinCnfStream is based on the following recursive algorithm
 * http://people.inf.ethz.ch/daniekro/classes/251-0247-00/f2007/readings/Tseitin70.pdf
 * The general gist of the algorithm is to introduce a new literal that 
 * will be equivalent to each subexpression in the constructed equisatisfiable
 * formula then substitute the new literal for the formula, and to do this
 * recursively.
 * 
 * This implementation does this in a single recursive pass.
 */
class TseitinCnfStream : public CnfStream {

public:

  void convertAndAssert(const Node& node);

  TseitinCnfStream(PropEngine* propEngine);

private:

  /* Each of these formulas handles takes care of a Node of each Kind.
   *
   * Each handleX(Node &n) is responsible for:
   *   - constructing a new literal, l (if necessary)
   *   - calling registerNode(n,l)
   *   - adding clauses assure that l is equivalent to the Node
   *   - calling recTransform on its children (if necessary)
   *   - returning l
   *
   * handleX( n ) can assume that n is not in d_translationCache
   */
  SatLiteral handleAtom(const Node& node);
  SatLiteral handleNot(const Node& node);
  SatLiteral handleXor(const Node& node);
  SatLiteral handleImplies(const Node& node);
  SatLiteral handleIff(const Node& node);
  SatLiteral handleIte(const Node& node);

  SatLiteral handleAnd(const Node& node);
  SatLiteral handleOr(const Node& node);

  /**
   * Maps recTransform over the children of a node. This is very useful for
   * n-ary Kinds (OR, AND). Non n-ary kinds (IMPLIES) should avoid using this
   * as it requires a tiny bit of extra overhead, and it leads to less readable
   * code.
   *
   * precondition: target.size() == n.getNumChildren()
   * @param n ...
   * @param target ...
   */
  void mapRecTransformOverChildren(const Node& node, SatClause& target);

  //Recursively dispatches the various Kinds to the appropriate handler.
  SatLiteral recTransform(const Node& node);

}; /* class TseitinCnfStream */

}/* prop namespace */
}/* CVC4 namespace */

#endif /* __CVC4__CNF_STREAM_H */
