/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Rewrite database term processor
 */

#include "rewriter/rewrite_db_term_process.h"

#include "expr/attribute.h"
#include "expr/nary_term_util.h"
#include "theory/builtin/generic_op.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/strings/theory_strings_utils.h"
#include "util/bitvector.h"
#include "util/rational.h"
#include "util/string.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace rewriter {

Node RewriteDbNodeConverter::postConvert(Node n)
{
  Kind k = n.getKind();
  TypeNode tn = n.getType();
  if (k == Kind::CONST_STRING)
  {
    NodeManager* nm = NodeManager::currentNM();
    // "ABC" is (str.++ "A" "B" "C")
    const std::vector<unsigned>& vec = n.getConst<String>().getVec();
    if (vec.size() <= 1)
    {
      return n;
    }
    std::vector<Node> children;
    for (unsigned c : vec)
    {
      std::vector<unsigned> tmp;
      tmp.push_back(c);
      children.push_back(nm->mkConst(String(tmp)));
    }
    return nm->mkNode(Kind::STRING_CONCAT, children);
  }
  else if (k == Kind::CONST_SEQUENCE)
  {
    return theory::strings::utils::mkConcatForConstSequence(n);
  }
  else if (k == Kind::CONST_BITVECTOR)
  {
    // (_ bv N M) is (bv N M)
    NodeManager* nm = NodeManager::currentNM();
    std::vector<Node> children;
    children.push_back(
        nm->mkConstInt(Rational(n.getConst<BitVector>().toInteger())));
    children.push_back(nm->mkConstInt(Rational(theory::bv::utils::getSize(n))));
    return nm->mkNode(Kind::CONST_BITVECTOR_SYMBOLIC, children);
  }
  else if (k == Kind::FORALL)
  {
    // ignore annotation
    if (n.getNumChildren() == 3)
    {
      NodeManager* nm = NodeManager::currentNM();
      return nm->mkNode(Kind::FORALL, n[0], n[1]);
    }
  }
  // convert indexed operators to symbolic
  if (GenericOp::isIndexedOperatorKind(k))
  {
    NodeManager* nm = NodeManager::currentNM();
    std::vector<Node> indices =
        GenericOp::getIndicesForOperator(k, n.getOperator());
    indices.insert(indices.begin(), nm->mkConst(GenericOp(k)));
    indices.insert(indices.end(), n.begin(), n.end());
    return nm->mkNode(Kind::APPLY_INDEXED_SYMBOLIC, indices);
  }

  return n;
}

bool RewriteDbNodeConverter::shouldTraverse(Node n)
{
  return n.getKind() != Kind::INST_PATTERN_LIST;
}

}  // namespace rewriter
}  // namespace cvc5::internal
