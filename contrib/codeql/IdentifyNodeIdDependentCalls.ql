/**
 * @name Identify NodeId-Dependent Calls
 * @kind table
 * @id cpp/cvc5/identify-node-id-dependencies
 * @description Finds all functions that transitively trigger NodeId assignment by calling mkConstInternal or constructNV.
 */

import cpp

/** 
 * Low-level functions that directly increment the internal NodeId counter.
 * These are the "Minting Points" for the NodeManager.
 */
class NodeIdMintingPoint extends Function {
  NodeIdMintingPoint() {
    this.getQualifiedName() = "cvc5::internal::NodeManager::mkConstInternal" or
    this.getQualifiedName() = "cvc5::internal::NodeBuilder::constructNV"
  }
}

/**
 * A recursive predicate to identify functions whose execution depends on 
 * or triggers a NodeId assignment.
 */
query predicate isNodeIdDependent(Function f) {
  // Base case: The function is a direct minting point
  f instanceof NodeIdMintingPoint
  or
  // Recursive case: The function calls another function that is NodeId-dependent
  exists(Function callee |
    f.calls(callee) and
    isNodeIdDependent(callee)
  ) and
  // Focus only on the cvc5 source tree to avoid library noise
  f.getFile().getAbsolutePath().matches("%/cvc5/%")
}

from Function f
where isNodeIdDependent(f)
select f.getQualifiedName()
