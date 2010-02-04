/*********************                                           -*- C++ -*-  */
/** cnf_stream.h
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
#include "prop/minisat/simp/SimpSolver.h"
#include "prop/minisat/core/SolverTypes.h"
#include "prop/prop_engine.h"

#include <map>

namespace CVC4 {
class PropEngine;
}

namespace CVC4 {
namespace prop {

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
  std::map<Node, minisat::Lit> d_translationCache;

protected:

  /**
   * Uniform interface for sending a clause back to d_propEngine.
   * May want to have internal data-structures later on
   */
  void insertClauseIntoStream(minisat::vec<minisat::Lit> & c);
  void insertClauseIntoStream(minisat::Lit a);
  void insertClauseIntoStream(minisat::Lit a, minisat::Lit b);
  void insertClauseIntoStream(minisat::Lit a, minisat::Lit b, minisat::Lit c);

  //utilities for the translation cache;
  bool isCached(const Node & n) const;

  /**
   * Method comments...
   * @param n
   * @return returns ...
   */
  minisat::Lit lookupInCache(const Node & n) const;


  //negotiates the mapping of atoms to literals with PropEngine
  void registerMapping(const Node & node, minisat::Lit lit, bool atom = false);
  minisat::Lit acquireFreshLit(const Node & n);
  minisat::Lit aquireAndRegister(const Node & n, bool atom = false);

public:
  /**
   * Constructs a CnfStream that sends constructs an equisatisfiable set of clauses
   * and sends them to the given PropEngine.
   * @param pe
   */
  CnfStream(CVC4::PropEngine *pe);


  /**
   * Empties the internal translation cache.
   */
  void flushCache();

  /**
   * Converts and asserts a formula.
   * @param n node to convert and assert
   */
  virtual void convertAndAssert(const Node & n) = 0;

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
  void convertAndAssert(const Node & n);
  TseitinCnfStream(CVC4::PropEngine *pe);

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
  minisat::Lit handleAtom(const Node & n);
  minisat::Lit handleNot(const Node & n);
  minisat::Lit handleXor(const Node & n);
  minisat::Lit handleImplies(const Node & n);
  minisat::Lit handleIff(const Node & n);
  minisat::Lit handleIte(const Node & n);

  minisat::Lit handleAnd(const Node& n);
  minisat::Lit handleOr(const Node& n);

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
  void mapRecTransformOverChildren(const Node& n,
                                   minisat::vec<minisat::Lit> & target);

  //Recursively dispatches the various Kinds to the appropriate handler.
  minisat::Lit recTransform(const Node & n);

}; /* class TseitinCnfStream */

}/* prop namespace */
}/* CVC4 namespace */

#endif /* __CVC4__CNF_STREAM_H */
