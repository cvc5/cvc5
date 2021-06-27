/*********************                                                        */
/*! \file rewrite_db_term_process.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of rewrite db term processor.
 **/

#include "theory/rewrite_db_term_process.h"

#include "expr/attribute.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/strings/word.h"
#include "util/bitvector.h"
#include "util/rational.h"
#include "util/regexp.h"
#include "util/string.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {

Node RewriteDbNodeConverter::postConvert(Node n)
{
  Kind k = n.getKind();
  TypeNode tn = n.getType();
  if (k == CONST_STRING)
  {
    NodeManager* nm = NodeManager::currentNM();
    // "ABC" is (str.++ "A" (str.++ "B" "C"))
    const std::vector<unsigned>& vec = n.getConst<String>().getVec();
    if (vec.size() <= 1)
    {
      return n;
    }
    std::vector<unsigned> v(vec.begin(), vec.end());
    std::reverse(v.begin(), v.end());
    Node ret = getNullTerminator(STRING_CONCAT, tn);
    Assert(!ret.isNull());
    for (unsigned i = 0, size = v.size(); i < size; i++)
    {
      std::vector<unsigned> tmp;
      tmp.push_back(v[i]);
      ret = nm->mkNode(STRING_CONCAT, nm->mkConst(String(tmp)), ret);
    }
    return ret;
  }
  else if (NodeManager::isNAryKind(k) && n.getNumChildren() >= 2)
  {
    NodeManager* nm = NodeManager::currentNM();
    Assert(n.getMetaKind() != kind::metakind::PARAMETERIZED);
    // convert to binary + null terminator
    std::vector<Node> children(n.begin(), n.end());
    std::reverse(children.begin(), children.end());
    Node ret = getNullTerminator(k, tn);
    if (ret.isNull())
    {
      if (k == DISTINCT)
      {
        // FIXME
      }
      return n;
    }
    for (unsigned i = 0, nchild = n.getNumChildren(); i < nchild; i++)
    {
      ret = nm->mkNode(k, children[i], ret);
    }
    return ret;
  }
  return n;
}

Node RewriteDbNodeConverter::getNullTerminator(Kind k, TypeNode tn)
{
  NodeManager* nm = NodeManager::currentNM();
  Node nullTerm;
  switch (k)
  {
    case OR: nullTerm = nm->mkConst(false); break;
    case AND:
    case SEP_STAR: nullTerm = nm->mkConst(true); break;
    case PLUS: nullTerm = nm->mkConst(Rational(0)); break;
    case MULT:
    case NONLINEAR_MULT: nullTerm = nm->mkConst(Rational(1)); break;
    case STRING_CONCAT:
      // handles strings and sequences
      nullTerm = theory::strings::Word::mkEmptyWord(tn);
      break;
    case REGEXP_CONCAT:
      // the language containing only the empty string
      nullTerm = nm->mkNode(STRING_TO_REGEXP, nm->mkConst(String("")));
      break;
    case BITVECTOR_AND:
      nullTerm = theory::bv::utils::mkOnes(tn.getBitVectorSize());
      break;
    case BITVECTOR_OR:
    case BITVECTOR_ADD:
    case BITVECTOR_XOR:
      nullTerm = theory::bv::utils::mkZero(tn.getBitVectorSize());
      break;
    case BITVECTOR_MULT:
      nullTerm = theory::bv::utils::mkOne(tn.getBitVectorSize());
      break;
    case BITVECTOR_CONCAT:
    {
      // the null terminator of bitvector concat is a dummy variable of
      // bit-vector type with zero width, regardless of the type of the overall
      // concat. FIXME
    }
    break;
    default:
      // not handled as null-terminated
      break;
  }
  return nullTerm;
}

}  // namespace theory
}  // namespace cvc5
