#pragma once

#include "cvc4_private.h"

#include "cnf_stream.h"

#include "context/cdlist.h"
#include "context/cdhashset.h"

#include <ext/hash_map>

namespace CVC4 {
namespace mcsat {

/**
 * Simple conversion due to Tseitin.
 */
class TseitinCnfStream : public CnfStream {

public:

  /**
   * Constructs the stream to use the given sat solver. All information
   * is kept with accordance to the given context. If the given context is 
   * null single context is assumed.
   */
  TseitinCnfStream(context::Context* cnfContext = 0);

  ~TseitinCnfStream();
  
  /**
   * Same as above, except that removable is remembered.
   */
  void convert(TNode node, bool negated);

private:

  /** CNf context */
  context::Context* d_cnfContext;
  
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;

  /** Set of nodes that have already been translated */
  NodeSet d_alreadyTranslated;

  /** Has the node been already translated */
  bool alreadyTranslated(TNode node) const {
    return d_alreadyTranslated.find(node) != d_alreadyTranslated.end();
  }

  /** Returns the positive literal */
  Literal getLiteral(TNode node) const {
    return Literal(VariableDatabase::getCurrentDB()->getVariable(node), false);
  }

  // Each of these formulas handles takes care of a Node of each Kind.
  //
  // Each handleX(Node &n) is responsible for:
  //   - constructing a new literal, l (if necessary)
  //   - calling registerNode(n,l)
  //   - adding clauses assure that l is equivalent to the Node
  //   - calling toCNF on its children (if necessary)
  //   - returning l
  //
  // handleX( n ) can assume that n is not in d_translationCache
  Literal handleNot(TNode node);
  Literal handleXor(TNode node);
  Literal handleImplies(TNode node);
  Literal handleIff(TNode node);
  Literal handleIte(TNode node);
  Literal handleAnd(TNode node);
  Literal handleOr(TNode node);

  void topLevelAnd(TNode node, bool negated);
  void topLevelOr(TNode node, bool negated);
  void topLevelXor(TNode node, bool negated);
  void topLevelIff(TNode node, bool negated);
  void topLevelImplies(TNode node, bool negated);
  void topLevelIte(TNode node, bool negated);

  /**
   * Transforms the node into CNF recursively.
   * @param node the formula to transform
   * @param negated whether the literal is negated
   * @return the literal representing the root of the formula
   */
  Literal toCnfRecursive(TNode node, bool negated = false);

};/* class TseitinCnfStream */


}/* mcsat namespace */
}/* CVC4 namespace */
