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
 * The innermost ancestor directory named "src" of a file that defines a
 * minting point. Both the checked-in sources and the sources generated into
 * the build directory provide one.
 */
Folder getSourceDir() {
  exists(NodeIdMintingPoint mint |
    result = mint.getFile().getParentContainer+() and
    result.getBaseName() = "src" and
    not exists(Folder deeper |
      deeper = mint.getFile().getParentContainer+() and
      deeper.getBaseName() = "src" and
      result = deeper.getParentContainer+()
    )
  )
}

/** A root directory of the analyzed source tree. */
Folder getSourceRoot() { result = getSourceDir().getParentContainer() }

/**
 * Holds if `f` is defined in the analyzed source tree.
 *
 * The root is derived from where the minting points themselves are defined,
 * rather than by matching the absolute path against a fixed pattern. Matching
 * the path ties the result to where the repository happens to be checked out:
 * the recursive case below then contributes nothing whenever the checkout has
 * no matching path segment, the closure silently collapses to the two minting
 * points, and the clang-tidy check that consumes this list stops matching
 * anything instead of failing.
 */
predicate inSourceTree(Function f) {
  f.getFile().getParentContainer+() = getSourceRoot()
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
  // Focus only on the analyzed source tree to avoid library noise
  inSourceTree(f)
}

from Function f
where isNodeIdDependent(f)
select f.getQualifiedName()
