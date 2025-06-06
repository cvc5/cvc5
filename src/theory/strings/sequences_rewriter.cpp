/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the theory of strings.
 */

#include "theory/strings/sequences_rewriter.h"

#include "expr/attribute.h"
#include "expr/node_builder.h"
#include "expr/sequence.h"
#include "theory/rewriter.h"
#include "theory/strings/arith_entail.h"
#include "theory/strings/regexp_entail.h"
#include "theory/strings/skolem_cache.h"
#include "theory/strings/strings_rewriter.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/strings/word.h"
#include "util/rational.h"
#include "util/regexp.h"
#include "util/statistics_registry.h"
#include "util/string.h"

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace strings {

SequencesRewriter::SequencesRewriter(NodeManager* nm,
                                     ArithEntail& ae,
                                     StringsEntail& se,
                                     HistogramStat<Rewrite>* statistics)
    : TheoryRewriter(nm),
      d_statistics(statistics),
      d_arithEntail(ae),
      d_stringsEntail(se)
{
  d_sigmaStar = nm->mkNode(Kind::REGEXP_STAR, nm->mkNode(Kind::REGEXP_ALLCHAR));
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
  registerProofRewriteRule(ProofRewriteRule::RE_LOOP_ELIM,
                           TheoryRewriteCtx::PRE_DSL);
  registerProofRewriteRule(ProofRewriteRule::MACRO_RE_INTER_UNION_INCLUSION,
                           TheoryRewriteCtx::PRE_DSL);
  registerProofRewriteRule(ProofRewriteRule::STR_IN_RE_EVAL,
                           TheoryRewriteCtx::DSL_SUBCALL);
  registerProofRewriteRule(ProofRewriteRule::STR_IN_RE_CONSUME,
                           TheoryRewriteCtx::PRE_DSL);
  registerProofRewriteRule(ProofRewriteRule::STR_IN_RE_CONCAT_STAR_CHAR,
                           TheoryRewriteCtx::PRE_DSL);
  registerProofRewriteRule(ProofRewriteRule::STR_IN_RE_SIGMA,
                           TheoryRewriteCtx::PRE_DSL);
  registerProofRewriteRule(ProofRewriteRule::STR_IN_RE_SIGMA_STAR,
                           TheoryRewriteCtx::PRE_DSL);
  registerProofRewriteRule(ProofRewriteRule::MACRO_SUBSTR_STRIP_SYM_LENGTH,
                           TheoryRewriteCtx::POST_DSL);
  registerProofRewriteRule(ProofRewriteRule::STR_CTN_MULTISET_SUBSET,
                           TheoryRewriteCtx::DSL_SUBCALL);
  registerProofRewriteRule(ProofRewriteRule::MACRO_STR_EQ_LEN_UNIFY_PREFIX,
                           TheoryRewriteCtx::POST_DSL);
  registerProofRewriteRule(ProofRewriteRule::MACRO_STR_EQ_LEN_UNIFY,
                           TheoryRewriteCtx::POST_DSL);
  registerProofRewriteRule(ProofRewriteRule::STR_INDEXOF_RE_EVAL,
                           TheoryRewriteCtx::POST_DSL);
  registerProofRewriteRule(ProofRewriteRule::STR_REPLACE_RE_EVAL,
                           TheoryRewriteCtx::POST_DSL);
  registerProofRewriteRule(ProofRewriteRule::STR_REPLACE_RE_ALL_EVAL,
                           TheoryRewriteCtx::POST_DSL);
  registerProofRewriteRule(ProofRewriteRule::MACRO_STR_CONST_NCTN_CONCAT,
                           TheoryRewriteCtx::DSL_SUBCALL);
  registerProofRewriteRule(ProofRewriteRule::MACRO_STR_IN_RE_INCLUSION,
                           TheoryRewriteCtx::POST_DSL);
  registerProofRewriteRule(ProofRewriteRule::MACRO_STR_STRIP_ENDPOINTS,
                           TheoryRewriteCtx::POST_DSL);
  registerProofRewriteRule(ProofRewriteRule::MACRO_STR_SPLIT_CTN,
                           TheoryRewriteCtx::POST_DSL);
  // MACRO_RE_INTER_UNION_CONST_ELIM should always be called at post-dsl
  // as it is partly subsumed by RARE rewrites for intersection.
  registerProofRewriteRule(ProofRewriteRule::MACRO_RE_INTER_UNION_CONST_ELIM,
                           TheoryRewriteCtx::POST_DSL);
  registerProofRewriteRule(ProofRewriteRule::MACRO_STR_COMPONENT_CTN,
                           TheoryRewriteCtx::POST_DSL);
  registerProofRewriteRule(ProofRewriteRule::SEQ_EVAL_OP,
                           TheoryRewriteCtx::PRE_DSL);
  // make back pointer to this (for rewriting contains)
  se.d_rewriter = this;
}

Node SequencesRewriter::rewriteViaRule(ProofRewriteRule id, const Node& n)
{
  switch (id)
  {
    case ProofRewriteRule::RE_LOOP_ELIM: return rewriteViaReLoopElim(n);
    case ProofRewriteRule::MACRO_RE_INTER_UNION_INCLUSION:
      return rewriteViaMacroReInterUnionInclusion(n);
    case ProofRewriteRule::RE_INTER_INCLUSION:
    case ProofRewriteRule::RE_UNION_INCLUSION:
      return rewriteViaReInterUnionInclusion(id, n);
    case ProofRewriteRule::STR_IN_RE_EVAL: return rewriteViaStrInReEval(n);
    case ProofRewriteRule::STR_IN_RE_CONSUME:
      return rewriteViaStrInReConsume(n);
    case ProofRewriteRule::STR_IN_RE_CONCAT_STAR_CHAR:
      return rewriteViaStrInReConcatStarChar(n);
    case ProofRewriteRule::STR_IN_RE_SIGMA: return rewriteViaStrInReSigma(n);
    case ProofRewriteRule::STR_IN_RE_SIGMA_STAR:
      return rewriteViaStrInReSigmaStar(n);
    case ProofRewriteRule::MACRO_SUBSTR_STRIP_SYM_LENGTH:
    {
      // Rewrite without using the rewriter as a subutility, which ensures
      // that we can reconstruct the reasoning in a proof.
      Rewrite rule;
      ArithEntail ae(nodeManager(), nullptr);
      StringsEntail sent(nullptr, ae);
      return rewriteViaMacroSubstrStripSymLength(n, rule, sent);
    }
    case ProofRewriteRule::STR_CTN_MULTISET_SUBSET:
    {
      // don't use this just for evaluation
      if (n.getKind() == Kind::STRING_CONTAINS
          && (!n[0].isConst() || !n[1].isConst()))
      {
        if (d_stringsEntail.checkMultisetSubset(n[0], n[1]))
        {
          return d_nm->mkConst(false);
        }
      }
    }
    break;
    case ProofRewriteRule::MACRO_STR_EQ_LEN_UNIFY_PREFIX:
    {
      if (n.getKind() == Kind::EQUAL)
      {
        return rewriteViaStrEqLenUnifyPrefix(n);
      }
    }
    break;
    case ProofRewriteRule::MACRO_STR_EQ_LEN_UNIFY:
    {
      if (n.getKind() == Kind::EQUAL)
      {
        Rewrite rule;
        return rewriteViaStrEqLenUnify(n, rule);
      }
    }
    break;
    case ProofRewriteRule::STR_INDEXOF_RE_EVAL:
    {
      return rewriteViaStrIndexofReEval(n);
    }
    break;
    case ProofRewriteRule::STR_REPLACE_RE_EVAL:
    {
      return rewriteViaStrReplaceReEval(n);
    }
    break;
    case ProofRewriteRule::STR_REPLACE_RE_ALL_EVAL:
    {
      return rewriteViaStrReplaceReAllEval(n);
    }
    break;
    case ProofRewriteRule::MACRO_STR_CONST_NCTN_CONCAT:
    {
      if (n.getKind() == Kind::STRING_CONTAINS
          && n[0].getKind() == Kind::CONST_STRING)
      {
        NodeManager* nm = nodeManager();
        RegExpEntail re(nm, nullptr);
        Node re2 = re.getGeneralizedConstRegExp(n[1]);
        if (!re2.isNull())
        {
          Node re2s =
              nm->mkNode(Kind::REGEXP_CONCAT, d_sigmaStar, re2, d_sigmaStar);
          String s = n[0].getConst<String>();
          if (!RegExpEntail::testConstStringInRegExp(s, re2s))
          {
            return nm->mkConst(false);
          }
        }
      }
    }
    break;
    case ProofRewriteRule::MACRO_STR_IN_RE_INCLUSION:
      return rewriteViaMacroStrInReInclusion(n);
    case ProofRewriteRule::MACRO_STR_SPLIT_CTN:
      return rewriteViaMacroStrSplitCtn(n);
    case ProofRewriteRule::MACRO_STR_STRIP_ENDPOINTS:
    {
      std::vector<Node> nb, nrem, ne;
      return rewriteViaMacroStrStripEndpoints(n, nb, nrem, ne);
    }
    case ProofRewriteRule::MACRO_RE_INTER_UNION_CONST_ELIM:
      return rewriteViaMacroReInterUnionConstElim(n);
    case ProofRewriteRule::MACRO_STR_COMPONENT_CTN:
    {
      if (n.getKind() == Kind::STRING_CONTAINS)
      {
        std::vector<Node> nc1;
        utils::getConcat(n[0], nc1);
        std::vector<Node> nc2;
        utils::getConcat(n[1], nc2);
        // component-wise containment, note we do not use the extended version
        std::vector<Node> nc1rb;
        std::vector<Node> nc1re;
        if (d_stringsEntail.componentContains(nc1, nc2, nc1rb, nc1re) != -1)
        {
          return nodeManager()->mkConst(true);
        }
      }
    }
    break;
    case ProofRewriteRule::SEQ_EVAL_OP:
    {
      // this is a catchall rule for evaluation of operations on constant
      // sequences
      TypeNode tn = utils::getOwnerStringType(n);
      if (tn.isSequence())
      {
        for (const Node& nc : n)
        {
          if (!nc.isConst())
          {
            return Node::null();
          }
        }
        RewriteResponse response = postRewrite(n);
        Node ret = response.d_node;
        if (ret.isConst())
        {
          return ret;
        }
      }
    }
    break;
    case ProofRewriteRule::STR_OVERLAP_SPLIT_CTN:
    case ProofRewriteRule::STR_OVERLAP_ENDPOINTS_CTN:
    case ProofRewriteRule::STR_OVERLAP_ENDPOINTS_INDEXOF:
    case ProofRewriteRule::STR_OVERLAP_ENDPOINTS_REPLACE:
      return rewriteViaOverlap(id, n);
    default: break;
  }
  return Node::null();
}

ArithEntail& SequencesRewriter::getArithEntail() { return d_arithEntail; }

StringsEntail& SequencesRewriter::getStringsEntail() { return d_stringsEntail; }

Node SequencesRewriter::rewriteEquality(Node node)
{
  Assert(node.getKind() == Kind::EQUAL);
  if (node[0] == node[1])
  {
    return returnRewrite(node, d_true, Rewrite::EQ_REFL);
  }
  else if (node[0].isConst() && node[1].isConst())
  {
    return returnRewrite(node, d_false, Rewrite::EQ_CONST_FALSE);
  }
  // standard ordering
  if (node[0] > node[1])
  {
    Node ret = nodeManager()->mkNode(Kind::EQUAL, node[1], node[0]);
    return returnRewrite(node, ret, Rewrite::EQ_SYM);
  }
  return node;
}

Node SequencesRewriter::rewriteEqualityExt(Node node)
{
  Assert(node.getKind() == Kind::EQUAL);
  TypeNode tn = node[0].getType();
  if (tn.isInteger())
  {
    return rewriteArithEqualityExt(node);
  }
  if (tn.isStringLike())
  {
    return rewriteStrEqualityExt(node);
  }
  return node;
}

Node SequencesRewriter::rewriteStrEqualityExt(Node node)
{
  Assert(node.getKind() == Kind::EQUAL && node[0].getType().isStringLike());
  TypeNode stype = node[0].getType();

  bool hasStrTerm = false;
  for (size_t r = 0; r < 2; r++)
  {
    if (!node[r].isConst()
        && kindToTheoryId(node[r].getKind()) == THEORY_STRINGS)
    {
      hasStrTerm = true;
      break;
    }
  }
  if (!hasStrTerm)
  {
    // equality between variables and constants, no rewrites apply
    return node;
  }

  NodeManager* nm = nodeManager();
  // ( ~contains( s, t ) V ~contains( t, s ) ) => ( s == t ---> false )
  for (unsigned r = 0; r < 2; r++)
  {
    // must call rewrite contains directly to avoid infinite loop
    Node ctn = nm->mkNode(Kind::STRING_CONTAINS, node[r], node[1 - r]);
    Node prev = ctn;
    ctn = rewriteContains(ctn);
    Assert(!ctn.isNull());
    if (ctn != prev && ctn.getKind() == Kind::STRING_CONTAINS)
    {
      prev = ctn;
      ctn = rewriteContains(ctn);
      Assert(!ctn.isNull());
    }
    if (ctn.isConst())
    {
      if (!ctn.getConst<bool>())
      {
        return returnRewrite(node, ctn, Rewrite::EQ_NCTN);
      }
      else
      {
        // definitely contains but not syntactically equal
        // We may be able to simplify, e.g.
        //  str.++( x, "a" ) == "a"  ----> x = ""
      }
    }
  }

  std::vector<Node> c[2];
  for (unsigned i = 0; i < 2; i++)
  {
    utils::getConcat(node[i], c[i]);
  }

  // check if the prefix, suffix mismatches
  //   For example, str.++( x, "a", y ) == str.++( x, "bc", z ) ---> false
  unsigned minsize = std::min(c[0].size(), c[1].size());
  for (unsigned r = 0; r < 2; r++)
  {
    for (unsigned i = 0; i < minsize; i++)
    {
      unsigned index1 = r == 0 ? i : (c[0].size() - 1) - i;
      unsigned index2 = r == 0 ? i : (c[1].size() - 1) - i;
      Node s = c[0][index1];
      Node t = c[1][index2];
      if (s.isConst() && t.isConst())
      {
        size_t lenS = Word::getLength(s);
        size_t lenT = Word::getLength(t);
        size_t lenShort = lenS <= lenT ? lenS : lenT;
        bool isSameFix = r == 1 ? Word::rstrncmp(s, t, lenShort)
                                : Word::strncmp(s, t, lenShort);
        if (!isSameFix)
        {
          Node ret = nodeManager()->mkConst(false);
          return returnRewrite(node, ret, Rewrite::EQ_NFIX);
        }
      }
      if (s != t)
      {
        break;
      }
    }
  }

  Node new_ret;
  // ------- equality unification
  bool changed = false;
  for (unsigned i = 0; i < 2; i++)
  {
    while (!c[0].empty() && !c[1].empty() && c[0].back() == c[1].back())
    {
      c[0].pop_back();
      c[1].pop_back();
      changed = true;
    }
    // splice constants
    if (!c[0].empty() && !c[1].empty() && c[0].back().isConst()
        && c[1].back().isConst())
    {
      Node cs[2];
      size_t csl[2];
      for (unsigned j = 0; j < 2; j++)
      {
        cs[j] = c[j].back();
        csl[j] = Word::getLength(cs[j]);
      }
      size_t larger = csl[0] > csl[1] ? 0 : 1;
      size_t smallerSize = csl[1 - larger];
      if (cs[1 - larger]
          == (i == 0 ? Word::suffix(cs[larger], smallerSize)
                     : Word::prefix(cs[larger], smallerSize)))
      {
        size_t sizeDiff = csl[larger] - smallerSize;
        c[larger][c[larger].size() - 1] =
            i == 0 ? Word::prefix(cs[larger], sizeDiff)
                   : Word::suffix(cs[larger], sizeDiff);
        c[1 - larger].pop_back();
        changed = true;
      }
    }
    for (unsigned j = 0; j < 2; j++)
    {
      std::reverse(c[j].begin(), c[j].end());
    }
  }
  if (changed)
  {
    // e.g. x++y = x++z ---> y = z, "AB" ++ x = "A" ++ y --> "B" ++ x = y
    Node s1 = utils::mkConcat(c[0], stype);
    Node s2 = utils::mkConcat(c[1], stype);
    if (s1 != node[0] || s2 != node[1])
    {
      new_ret = s1.eqNode(s2);
      // We generally don't apply the extended equality rewriter if the
      // original node was an equality but we may be able to do additional
      // rewriting here, e.g.,
      // x++y = "" --> x = "" and y = ""
      return returnRewrite(node, new_ret, Rewrite::STR_EQ_UNIFY);
    }
  }

  // ------- rewrites for (= "" _)
  Node empty = Word::mkEmptyWord(stype);
  for (size_t i = 0; i < 2; i++)
  {
    if (node[i] == empty)
    {
      Node ne = node[1 - i];
      if (ne.getKind() == Kind::STRING_REPLACE)
      {
        // (= "" (str.replace x y x)) ---> (= x "")
        if (ne[0] == ne[2])
        {
          Node ret = nm->mkNode(Kind::EQUAL, ne[0], empty);
          return returnRewrite(node, ret, Rewrite::STR_EMP_REPL_X_Y_X);
        }

        // (= "" (str.replace x y "A")) ---> (and (= x "") (not (= y "")))
        if (d_stringsEntail.checkNonEmpty(ne[2]))
        {
          Node ret = nm->mkNode(
              Kind::AND,
              nm->mkNode(Kind::EQUAL, ne[0], empty),
              nm->mkNode(Kind::NOT, nm->mkNode(Kind::EQUAL, ne[1], empty)));
          return returnRewrite(node, ret, Rewrite::STR_EMP_REPL_EMP);
        }

        // (= "" (str.replace x "A" "")) ---> (str.prefix x "A")
        if (d_stringsEntail.checkLengthOne(ne[1], true) && ne[2] == empty)
        {
          Node ret = nm->mkNode(Kind::STRING_PREFIX, ne[0], ne[1]);
          return returnRewrite(node, ret, Rewrite::STR_EMP_REPL_EMP);
        }
      }
      else if (ne.getKind() == Kind::STRING_SUBSTR)
      {
        Node zero = nm->mkConstInt(Rational(0));

        if (d_arithEntail.check(ne[1], false)
            && d_arithEntail.check(ne[2], true))
        {
          // (= "" (str.substr x 0 m)) ---> (= "" x) if m > 0
          if (ne[1] == zero)
          {
            Node ret = nm->mkNode(Kind::EQUAL, ne[0], empty);
            return returnRewrite(node, ret, Rewrite::STR_EMP_SUBSTR_LEQ_LEN);
          }

          // (= "" (str.substr x n m)) ---> (<= (str.len x) n)
          // if n >= 0 and m > 0
          Node ret = nm->mkNode(
              Kind::LEQ, nm->mkNode(Kind::STRING_LENGTH, ne[0]), ne[1]);
          return returnRewrite(node, ret, Rewrite::STR_EMP_SUBSTR_LEQ_LEN);
        }

        // (= "" (str.substr "A" 0 z)) ---> (<= z 0)
        if (d_stringsEntail.checkNonEmpty(ne[0]) && ne[1] == zero)
        {
          Node ret = nm->mkNode(Kind::LEQ, ne[2], zero);
          return returnRewrite(node, ret, Rewrite::STR_EMP_SUBSTR_LEQ_Z);
        }
      }
    }
  }

  // ------- rewrites for (= (str.replace _ _ _) _)
  for (size_t i = 0; i < 2; i++)
  {
    if (node[i].getKind() == Kind::STRING_REPLACE)
    {
      Node repl = node[i];
      Node x = node[1 - i];

      // (= "A" (str.replace "" x y)) ---> (and (= x "") (= y "A"))
      if (d_stringsEntail.checkNonEmpty(x) && repl[0] == empty)
      {
        Node ret =
            nm->mkNode(Kind::AND, repl[1].eqNode(empty), repl[2].eqNode(x));
        return returnRewrite(node, ret, Rewrite::STR_EQ_REPL_EMP);
      }

      // (= x (str.replace y x y)) ---> (= x y)
      if (repl[0] == repl[2] && x == repl[1])
      {
        Node ret = nm->mkNode(Kind::EQUAL, x, repl[0]);
        return returnRewrite(node, ret, Rewrite::STR_EQ_REPL_TO_EQ);
      }

      // (= x (str.replace x "A" "B")) ---> (not (str.contains x "A"))
      if (x == repl[0])
      {
        Node eq = rewriteEquality(nm->mkNode(Kind::EQUAL, repl[1], repl[2]));
        if (eq.isConst() && !eq.getConst<bool>())
        {
          Node ret = nm->mkNode(Kind::NOT,
                                nm->mkNode(Kind::STRING_CONTAINS, x, repl[1]));
          return returnRewrite(node, ret, Rewrite::STR_EQ_REPL_NOT_CTN);
        }
      }

      // (= (str.replace x y z) z) --> (or (= x y) (= x z))
      // if (str.len y) = (str.len z)
      if (repl[2] == x)
      {
        Node lenY = nm->mkNode(Kind::STRING_LENGTH, repl[1]);
        Node lenZ = nm->mkNode(Kind::STRING_LENGTH, repl[2]);
        if (d_arithEntail.checkEq(lenY, lenZ))
        {
          Node ret = nm->mkNode(Kind::OR,
                                nm->mkNode(Kind::EQUAL, repl[0], repl[1]),
                                nm->mkNode(Kind::EQUAL, repl[0], repl[2]));
          return returnRewrite(node, ret, Rewrite::STR_EQ_REPL_TO_DIS);
        }
      }
    }
  }

  // Try to rewrite (= x y) into a conjunction of equalities based on length
  // entailment.
  //
  // (<= (str.len x) (str.++ y1 ... yn)) AND (= x (str.++ y1 ... yn)) --->
  //  (and (= x (str.++ y1' ... ym')) (= y1'' "") ... (= yk'' ""))
  //
  // where yi' and yi'' correspond to some yj and
  //   (<= (str.len x) (str.++ y1' ... ym'))
  new_ret = rewriteViaStrEqLenUnifyPrefix(node);
  if (!new_ret.isNull())
  {
    return returnRewrite(node, new_ret, Rewrite::STR_EQ_CONJ_LEN_ENTAIL);
  }

  // (= (str.++ x_1 ... x_i x_{i + 1} ... x_n)
  //    (str.++ y_1 ... y_j y_{j + 1} ... y_m)) --->
  //  (and (= (str.++ x_1 ... x_i) (str.++ y_1 ... y_j))
  //       (= (str.++ x_{i + 1} ... x_n) (str.++ y_{j + 1} ... y_m)))
  //
  // if (str.len (str.++ x_1 ... x_i)) = (str.len (str.++ y_1 ... y_j))
  //
  // This rewrite performs length-based equality splitting: If we can show
  // that two prefixes have the same length, we can split an equality into
  // two equalities, one over the prefixes and another over the suffixes.
  Rewrite rule;
  new_ret = rewriteViaStrEqLenUnify(node, rule);
  if (!new_ret.isNull())
  {
    return returnRewrite(node, new_ret, rule);
  }

  return node;
}

Node SequencesRewriter::rewriteArithEqualityExt(Node node)
{
  Assert(node.getKind() == Kind::EQUAL && node[0].getType().isInteger());

  // cases where we can solve the equality

  // notice we cannot rewrite str.to.int(x)=n to x="n" due to leading zeroes.

  return node;
}

Node SequencesRewriter::rewriteLength(Node node)
{
  Assert(node.getKind() == Kind::STRING_LENGTH);
  NodeManager* nm = nodeManager();
  Kind nk0 = node[0].getKind();
  if (node[0].isConst())
  {
    Node retNode = nm->mkConstInt(Rational(Word::getLength(node[0])));
    return returnRewrite(node, retNode, Rewrite::LEN_EVAL);
  }
  else if (nk0 == Kind::STRING_CONCAT)
  {
    Node tmpNode = node[0];
    if (tmpNode.getKind() == Kind::STRING_CONCAT)
    {
      std::vector<Node> node_vec;
      for (unsigned int i = 0; i < tmpNode.getNumChildren(); ++i)
      {
        if (tmpNode[i].isConst())
        {
          node_vec.push_back(
              nm->mkConstInt(Rational(Word::getLength(tmpNode[i]))));
        }
        else
        {
          node_vec.push_back(
              nodeManager()->mkNode(Kind::STRING_LENGTH, tmpNode[i]));
        }
      }
      Node retNode = nodeManager()->mkNode(Kind::ADD, node_vec);
      return returnRewrite(node, retNode, Rewrite::LEN_CONCAT);
    }
  }
  else if (nk0 == Kind::STRING_REPLACE || nk0 == Kind::STRING_REPLACE_ALL)
  {
    Node len1 = nm->mkNode(Kind::STRING_LENGTH, node[0][1]);
    Node len2 = nm->mkNode(Kind::STRING_LENGTH, node[0][2]);
    if (d_arithEntail.checkEq(len1, len2))
    {
      // len( y ) == len( z ) => len( str.replace( x, y, z ) ) ---> len( x )
      Node retNode = nm->mkNode(Kind::STRING_LENGTH, node[0][0]);
      return returnRewrite(node, retNode, Rewrite::LEN_REPL_INV);
    }
  }
  else if (nk0 == Kind::STRING_TO_LOWER || nk0 == Kind::STRING_TO_UPPER
           || nk0 == Kind::STRING_REV || nk0 == Kind::STRING_UPDATE)
  {
    // len( f( x ) ) == len( x ) where f is to_lower, to_upper, or rev.
    // len( update( x, n, y ) ) = len( x )
    Node retNode = nm->mkNode(Kind::STRING_LENGTH, node[0][0]);
    return returnRewrite(node, retNode, Rewrite::LEN_CONV_INV);
  }
  else if (nk0 == Kind::SEQ_UNIT || nk0 == Kind::STRING_UNIT)
  {
    Node retNode = nm->mkConstInt(Rational(1));
    return returnRewrite(node, retNode, Rewrite::LEN_SEQ_UNIT);
  }
  return node;
}

// TODO (#1180) add rewrite
//  str.++( str.substr( x, n1, n2 ), str.substr( x, n1+n2, n3 ) ) --->
//  str.substr( x, n1, n2+n3 )
Node SequencesRewriter::rewriteConcat(Node node)
{
  Assert(node.getKind() == Kind::STRING_CONCAT);
  Trace("strings-rewrite-debug")
      << "Strings::rewriteConcat start " << node << std::endl;
  std::vector<Node> node_vec;
  Node preNode = Node::null();
  for (Node tmpNode : node)
  {
    if (tmpNode.getKind() == Kind::STRING_CONCAT)
    {
      unsigned j = 0;
      // combine the first term with the previous constant if applicable
      if (!preNode.isNull())
      {
        if (tmpNode[0].isConst())
        {
          std::vector<Node> wvec;
          wvec.push_back(preNode);
          wvec.push_back(tmpNode[0]);
          preNode = Word::mkWordFlatten(wvec);
          node_vec.push_back(preNode);
        }
        else
        {
          node_vec.push_back(preNode);
          node_vec.push_back(tmpNode[0]);
        }
        preNode = Node::null();
        ++j;
      }
      // insert the middle terms to node_vec
      if (j <= tmpNode.getNumChildren() - 1)
      {
        node_vec.insert(node_vec.end(), tmpNode.begin() + j, tmpNode.end() - 1);
      }
      // take the last term as the current
      tmpNode = tmpNode[tmpNode.getNumChildren() - 1];
    }
    if (!tmpNode.isConst())
    {
      if (!preNode.isNull())
      {
        if (preNode.isConst() && !Word::isEmpty(preNode))
        {
          node_vec.push_back(preNode);
        }
        preNode = Node::null();
      }
      node_vec.push_back(tmpNode);
    }
    else
    {
      if (preNode.isNull())
      {
        preNode = tmpNode;
      }
      else
      {
        std::vector<Node> vec;
        vec.push_back(preNode);
        vec.push_back(tmpNode);
        preNode = Word::mkWordFlatten(vec);
      }
    }
  }
  if (!preNode.isNull() && (!preNode.isConst() || !Word::isEmpty(preNode)))
  {
    node_vec.push_back(preNode);
  }

  TypeNode tn = node.getType();
  Node retNode = utils::mkConcat(node_vec, tn);
  Trace("strings-rewrite-debug")
      << "Strings::rewriteConcat end " << retNode << std::endl;
  if (retNode != node)
  {
    return returnRewrite(node, retNode, Rewrite::CONCAT_NORM);
  }
  return node;
}

Node SequencesRewriter::rewriteAllRegExp(TNode node)
{
  Assert(node.getKind() == Kind::REGEXP_ALL);
  NodeManager* nm = nodeManager();
  // re.all ----> (re.* re.allchar)
  Node ret = nm->mkNode(Kind::REGEXP_STAR, nm->mkNode(Kind::REGEXP_ALLCHAR));
  return returnRewrite(node, ret, Rewrite::RE_ALL_ELIM);
}

Node SequencesRewriter::rewriteConcatRegExp(TNode node)
{
  Assert(node.getKind() == Kind::REGEXP_CONCAT);
  NodeManager* nm = nodeManager();
  Trace("strings-rewrite-debug")
      << "Strings::rewriteConcatRegExp flatten " << node << std::endl;
  Node retNode = node;
  std::vector<Node> vec;
  bool changed = false;
  Node emptyRe;

  // get the string type that are members of this regular expression
  TypeNode rtype = node.getType();
  TypeNode stype;
  if (rtype.isRegExp())
  {
    // standard regular expressions are for strings
    stype = nm->stringType();
  }
  else
  {
    Unimplemented();
  }

  for (const Node& c : node)
  {
    if (c.getKind() == Kind::REGEXP_CONCAT)
    {
      changed = true;
      for (const Node& cc : c)
      {
        vec.push_back(cc);
      }
    }
    else if (c.getKind() == Kind::STRING_TO_REGEXP && c[0].isConst()
             && Word::isEmpty(c[0]))
    {
      changed = true;
      emptyRe = c;
    }
    else if (c.getKind() == Kind::REGEXP_NONE)
    {
      // re.++( ..., empty, ... ) ---> empty
      Node ret = nm->mkNode(Kind::REGEXP_NONE);
      return returnRewrite(node, ret, Rewrite::RE_CONCAT_EMPTY);
    }
    else
    {
      vec.push_back(c);
    }
  }
  if (changed)
  {
    // flatten
    // this handles nested re.++ and elimination or str.to.re(""), e.g.:
    // re.++( re.++( R1, R2 ), str.to.re(""), R3 ) ---> re.++( R1, R2, R3 )
    if (vec.empty())
    {
      Assert(!emptyRe.isNull());
      retNode = emptyRe;
    }
    else
    {
      retNode = vec.size() == 1 ? vec[0] : nm->mkNode(Kind::REGEXP_CONCAT, vec);
    }
    return returnRewrite(node, retNode, Rewrite::RE_CONCAT_FLATTEN);
  }
  Trace("strings-rewrite-debug")
      << "Strings::rewriteConcatRegExp start " << node << std::endl;
  std::vector<Node> cvec;
  // the current accumulation of constant strings
  std::vector<Node> preReStr;
  // whether the last component was (_)*
  bool lastAllStar = false;
  String emptyStr = String("");
  // this loop checks to see if components can be combined or dropped
  for (unsigned i = 0, size = vec.size(); i <= size; i++)
  {
    Node curr;
    if (i < size)
    {
      curr = vec[i];
      Assert(curr.getKind() != Kind::REGEXP_CONCAT);
    }
    // update preReStr
    if (!curr.isNull() && curr.getKind() == Kind::STRING_TO_REGEXP)
    {
      lastAllStar = false;
      preReStr.push_back(curr[0]);
      curr = Node::null();
    }
    else if (!preReStr.empty())
    {
      Assert(!lastAllStar);
      // this groups consecutive strings a++b ---> ab
      Node acc =
          nm->mkNode(Kind::STRING_TO_REGEXP, utils::mkConcat(preReStr, stype));
      cvec.push_back(acc);
      preReStr.clear();
    }
    else if (!curr.isNull() && lastAllStar)
    {
      // if empty, drop it
      // e.g. this ensures we rewrite (_)* ++ (a)* ---> (_)*
      if (RegExpEntail::isConstRegExp(curr)
          && RegExpEntail::testConstStringInRegExp(emptyStr, curr))
      {
        curr = Node::null();
      }
    }
    if (!curr.isNull())
    {
      lastAllStar = false;
      if (curr.getKind() == Kind::REGEXP_STAR)
      {
        // we can group stars (a)* ++ (a)* ---> (a)*
        if (!cvec.empty() && cvec.back() == curr)
        {
          curr = Node::null();
        }
        else if (curr[0].getKind() == Kind::REGEXP_ALLCHAR)
        {
          Assert(!lastAllStar);
          lastAllStar = true;
          // go back and remove empty ones from back of cvec
          // e.g. this ensures we rewrite (a)* ++ (_)* ---> (_)*
          while (
              !cvec.empty() && RegExpEntail::isConstRegExp(cvec.back())
              && RegExpEntail::testConstStringInRegExp(emptyStr, cvec.back()))
          {
            cvec.pop_back();
          }
        }
      }
    }
    if (!curr.isNull())
    {
      cvec.push_back(curr);
    }
  }
  Assert(!cvec.empty());
  retNode = utils::mkConcat(cvec, rtype);
  if (retNode != node)
  {
    // handles all cases where consecutive re constants are combined or
    // dropped as described in the loop above.
    return returnRewrite(node, retNode, Rewrite::RE_CONCAT);
  }

  // flipping adjacent star arguments
  changed = false;
  for (size_t i = 0, size = cvec.size() - 1; i < size; i++)
  {
    if (cvec[i].getKind() == Kind::REGEXP_STAR && cvec[i][0] == cvec[i + 1])
    {
      // by convention, flip the order (a*)++a ---> a++(a*)
      std::swap(cvec[i], cvec[i + 1]);
      changed = true;
    }
  }
  if (changed)
  {
    retNode = utils::mkConcat(cvec, rtype);
    return returnRewrite(node, retNode, Rewrite::RE_CONCAT_OPT);
  }
  return node;
}

Node SequencesRewriter::rewriteStarRegExp(TNode node)
{
  Assert(node.getKind() == Kind::REGEXP_STAR);
  NodeManager* nm = nodeManager();
  Node retNode = node;
  if (node[0].getKind() == Kind::REGEXP_STAR)
  {
    // ((R)*)* ---> R*
    return returnRewrite(node, node[0], Rewrite::RE_STAR_NESTED_STAR);
  }
  else if (node[0].getKind() == Kind::STRING_TO_REGEXP && node[0][0].isConst()
           && Word::isEmpty(node[0][0]))
  {
    // ("")* ---> ""
    return returnRewrite(node, node[0], Rewrite::RE_STAR_EMPTY_STRING);
  }
  else if (node[0].getKind() == Kind::REGEXP_NONE)
  {
    // (empty)* ---> ""
    retNode = nm->mkNode(Kind::STRING_TO_REGEXP, nm->mkConst(String("")));
    return returnRewrite(node, retNode, Rewrite::RE_STAR_EMPTY);
  }
  else if (node[0].getKind() == Kind::REGEXP_UNION)
  {
    for (const Node& nc : node[0])
    {
      if (nc.getKind() == Kind::REGEXP_ALLCHAR)
      {
        // (re.* (re.union ... re.allchar ...)) ---> (re.* re.allchar)
        retNode = nm->mkNode(Kind::REGEXP_STAR, nc);
        return returnRewrite(node, retNode, Rewrite::RE_STAR_UNION_CHAR);
      }
    }
    // simplification of unions under star
    if (RegExpEntail::hasEpsilonNode(node[0]))
    {
      bool changed = false;
      std::vector<Node> node_vec;
      for (const Node& nc : node[0])
      {
        if (nc.getKind() == Kind::STRING_TO_REGEXP && nc[0].isConst()
            && Word::isEmpty(nc[0]))
        {
          // can be removed
          changed = true;
        }
        else
        {
          node_vec.push_back(nc);
        }
      }
      if (changed)
      {
        retNode = node_vec.size() == 1
                      ? node_vec[0]
                      : nm->mkNode(Kind::REGEXP_UNION, node_vec);
        retNode = nm->mkNode(Kind::REGEXP_STAR, retNode);
        // simplification of union beneath star based on loop above
        // for example, ( "" | "a" )* ---> ("a")*
        return returnRewrite(node, retNode, Rewrite::RE_STAR_UNION);
      }
    }
  }
  return node;
}

Node SequencesRewriter::rewriteViaMacroReInterUnionInclusion(const Node& node)
{
  Kind nk = node.getKind();
  if (nk != Kind::REGEXP_UNION && nk != Kind::REGEXP_INTER)
  {
    return Node::null();
  }
  std::vector<Node> polRegExp[2];
  for (const Node& ni : node)
  {
    Kind nik = ni.getKind();
    uint32_t pindex = nik == Kind::REGEXP_COMPLEMENT ? 1 : 0;
    Node nia = pindex == 1 ? ni[0] : ni;
    polRegExp[pindex].push_back(nia);
  }
  for (const Node& negMem : polRegExp[1])
  {
    for (const Node& posMem : polRegExp[0])
    {
      Node m1 = nk == Kind::REGEXP_INTER ? negMem : posMem;
      Node m2 = nk == Kind::REGEXP_INTER ? posMem : negMem;
      // inclusion test for conflicting case m1 contains m2
      // (re.inter (re.comp R1) R2) --> re.none where R1 includes R2
      // (re.union R1 (re.comp R2)) --> (re.* re.allchar) where R1 includes R2
      if (RegExpEntail::regExpIncludes(m1, m2))
      {
        NodeManager* nm = nodeManager();
        Node retNode = nk == Kind::REGEXP_INTER
                           ? nm->mkNode(Kind::REGEXP_NONE)
                           : nm->mkNode(Kind::REGEXP_STAR,
                                        nm->mkNode(Kind::REGEXP_ALLCHAR));
        std::vector<Node> newChildren;
        newChildren.push_back(retNode);
        // Now go back and include all the remaining children that were
        // not involved. This simplifies proof checking, since we can isolate
        // which children led to the conflict.
        // In particular, if Ri includes Rj, then we rewrite
        //    (re.inter R1 ... (re.comp Ri) ... Rj ... Rn)
        // to
        //    (re.inter re.none R1...R{i-1} R{i+1} ... R{j-1} R{j+1} .. Rn)
        // where the latter will be rewritten to re.none.
        bool foundPos = false;
        bool foundNeg = false;
        for (const Node& nc : node)
        {
          if (!foundPos && nc == posMem)
          {
            foundPos = true;
            continue;
          }
          if (!foundNeg && nc.getKind() == Kind::REGEXP_COMPLEMENT
              && nc[0] == negMem)
          {
            foundNeg = true;
            continue;
          }
          newChildren.push_back(nc);
        }
        if (newChildren.size() > 1)
        {
          retNode = nm->mkNode(nk, newChildren);
        }
        return retNode;
      }
    }
  }
  return Node::null();
}

Node SequencesRewriter::rewriteViaReInterUnionInclusion(ProofRewriteRule id,
                                                        const Node& n)
{
  if (n.getNumChildren() != 2 || n[1].getKind() != Kind::REGEXP_COMPLEMENT)
  {
    return Node::null();
  }
  Kind k = n.getKind();
  if (id == ProofRewriteRule::RE_INTER_INCLUSION)
  {
    if (k == Kind::REGEXP_INTER && RegExpEntail::regExpIncludes(n[1][0], n[0]))
    {
      return nodeManager()->mkNode(Kind::REGEXP_NONE);
    }
  }
  else
  {
    Assert(id == ProofRewriteRule::RE_UNION_INCLUSION);
    if (k == Kind::REGEXP_UNION && RegExpEntail::regExpIncludes(n[0], n[1][0]))
    {
      NodeManager* nm = nodeManager();
      return nm->mkNode(Kind::REGEXP_STAR, nm->mkNode(Kind::REGEXP_ALLCHAR));
    }
  }
  return Node::null();
}

Node SequencesRewriter::rewriteAndOrRegExp(TNode node)
{
  Kind nk = node.getKind();
  Assert(nk == Kind::REGEXP_UNION || nk == Kind::REGEXP_INTER);
  Trace("strings-rewrite-debug")
      << "Strings::rewriteAndOrRegExp start " << node << std::endl;
  NodeManager* nm = nodeManager();
  std::vector<Node> node_vec;
  // list of constant string regular expressions (str.to_re c)
  std::vector<Node> constStrRe;
  bool changed = false;
  for (const Node& ni : node)
  {
    Kind nik = ni.getKind();
    if (nik == nk)
    {
      for (const Node& nic : ni)
      {
        if (std::find(node_vec.begin(), node_vec.end(), nic) == node_vec.end())
        {
          node_vec.push_back(nic);
        }
      }
      changed = true;
    }
    else if (nik == Kind::REGEXP_NONE)
    {
      if (nk == Kind::REGEXP_INTER)
      {
        return returnRewrite(node, ni, Rewrite::RE_AND_EMPTY);
      }
      // otherwise, can ignore
      changed = true;
    }
    else if (nik == Kind::REGEXP_STAR
             && ni[0].getKind() == Kind::REGEXP_ALLCHAR)
    {
      if (nk == Kind::REGEXP_UNION)
      {
        return returnRewrite(node, ni, Rewrite::RE_OR_ALL);
      }
      // otherwise, can ignore
      changed = true;
    }
    else if (std::find(node_vec.begin(), node_vec.end(), ni) == node_vec.end())
    {
      if (nik == Kind::STRING_TO_REGEXP && ni[0].isConst())
      {
        if (nk == Kind::REGEXP_INTER)
        {
          if (!constStrRe.empty())
          {
            Assert(constStrRe[0][0] != ni[0]);
            // (re.inter .. (str.to_re c1) .. (str.to_re c2) ..) ---> re.none
            // for distinct constant strings c1, c2.
            Node ret = nm->mkNode(Kind::REGEXP_NONE);
            return returnRewrite(
                node, ret, Rewrite::RE_INTER_CONST_CONST_CONFLICT);
          }
        }
        else
        {
          Assert(nk == Kind::REGEXP_UNION);
        }
        constStrRe.push_back(ni);
      }
      node_vec.push_back(ni);
    }
    else
    {
      changed = true;
    }
  }
  // if we already changed due to flattening, return already
  if (changed)
  {
    Node retNode = node;
    if (node_vec.empty())
    {
      if (nk == Kind::REGEXP_INTER)
      {
        retNode =
            nm->mkNode(Kind::REGEXP_STAR, nm->mkNode(Kind::REGEXP_ALLCHAR));
      }
      else
      {
        retNode = nm->mkNode(Kind::REGEXP_NONE);
      }
    }
    else
    {
      retNode = node_vec.size() == 1 ? node_vec[0] : nm->mkNode(nk, node_vec);
    }
    if (retNode != node)
    {
      // flattening and removing children, based on loop above
      return returnRewrite(node, retNode, Rewrite::RE_ANDOR_FLATTEN);
    }
  }
  // try to eliminate components via constant membership tests
  Node retNode = rewriteViaMacroReInterUnionConstElim(node);
  if (!retNode.isNull())
  {
    return returnRewrite(node, retNode, Rewrite::RE_ANDOR_CONST_REMOVE);
  }

  // use inclusion tests
  retNode = rewriteViaMacroReInterUnionInclusion(node);
  if (!retNode.isNull())
  {
    return returnRewrite(node, retNode, Rewrite::RE_ANDOR_INC_CONFLICT);
  }

  // otherwise there is no change
  return node;
}

Node SequencesRewriter::rewriteLoopRegExp(TNode node)
{
  Assert(node.getKind() == Kind::REGEXP_LOOP);
  uint32_t l = utils::getLoopMinOccurrences(node);
  uint32_t u = utils::getLoopMaxOccurrences(node);
  Node r = node[0];
  Node retNode = node;

  NodeManager* nm = nodeManager();
  if (u < l)
  {
    // ((_ re.loop l u) r) --> re.none if u < l
    std::vector<Node> nvec;
    retNode = nm->mkNode(Kind::REGEXP_NONE, nvec);
    return returnRewrite(node, retNode, Rewrite::RE_LOOP_NONE);
  }
  else if (u==0)
  {
    retNode = nm->mkNode(Kind::STRING_TO_REGEXP, nm->mkConst(String("")));
    return returnRewrite(node, retNode, Rewrite::RE_LOOP_ZERO);
  }
  else if (r.getKind() == Kind::REGEXP_STAR)
  {
    return returnRewrite(node, r, Rewrite::RE_LOOP_STAR);
  }
  retNode = rewriteViaReLoopElim(node);
  Assert(!retNode.isNull() && retNode != node);
  return returnRewrite(node, retNode, Rewrite::RE_LOOP);
}

Node SequencesRewriter::rewriteViaStrEqLenUnifyPrefix(const Node& node)
{
  Node newRet;
  for (unsigned i = 0; i < 2; i++)
  {
    if (node[1 - i].getKind() == Kind::STRING_CONCAT)
    {
      newRet = d_stringsEntail.inferEqsFromContains(node[i], node[1 - i]);
      // don't rewrite if just returning a (flipped) equality
      if (!newRet.isNull() && newRet.getKind() == Kind::AND)
      {
        if (i == 1)
        {
          // flip the first equality back
          std::vector<Node> nc(newRet.begin(), newRet.end());
          nc[0] = nc[0][1].eqNode(nc[0][0]);
          newRet = nodeManager()->mkNode(Kind::AND, nc);
        }
        return newRet;
      }
    }
  }
  return Node::null();
}

Node SequencesRewriter::rewriteViaStrEqLenUnify(const Node& node, Rewrite& rule)
{
  if (node[0].getKind() == Kind::STRING_CONCAT
      && node[1].getKind() == Kind::STRING_CONCAT)
  {
    std::vector<Node> v0, v1;
    utils::getConcat(node[0], v0);
    utils::getConcat(node[1], v1);
    size_t startRhs = 0;
    TypeNode stype = node[0].getType();
    for (size_t i = 0, size0 = v0.size(); i <= size0; i++)
    {
      const std::vector<Node> pfxv0(v0.begin(), v0.begin() + i);
      Node pfx0 = utils::mkConcat(pfxv0, stype);
      for (size_t j = startRhs, size1 = v1.size(); j <= size1; j++)
      {
        if (!(i == 0 && j == 0) && !(i == v0.size() && j == v1.size()))
        {
          std::vector<Node> pfxv1(v1.begin(), v1.begin() + j);
          Node pfx1 = utils::mkConcat(pfxv1, stype);
          Node lenPfx0 = d_nm->mkNode(Kind::STRING_LENGTH, pfx0);
          Node lenPfx1 = d_nm->mkNode(Kind::STRING_LENGTH, pfx1);

          if (d_arithEntail.checkEq(lenPfx0, lenPfx1))
          {
            std::vector<Node> sfxv0(v0.begin() + i, v0.end());
            std::vector<Node> sfxv1(v1.begin() + j, v1.end());
            Node ret = d_nm->mkNode(Kind::AND,
                                    pfx0.eqNode(pfx1),
                                    utils::mkConcat(sfxv0, stype)
                                        .eqNode(utils::mkConcat(sfxv1, stype)));
            rule = Rewrite::SPLIT_EQ;
            return ret;
          }
          else if (d_arithEntail.check(lenPfx1, lenPfx0, true))
          {
            // The prefix on the right-hand side is strictly longer than the
            // prefix on the left-hand side, so we try to strip the right-hand
            // prefix by the length of the left-hand prefix
            //
            // Example:
            // (= (str.++ "A" x y) (str.++ x "AB" z)) --->
            //   (and (= (str.++ "A" x) (str.++ x "A")) (= y (str.++ "B" z)))
            std::vector<Node> rpfxv1;
            if (d_stringsEntail.stripSymbolicLength(
                    pfxv1, rpfxv1, 1, lenPfx0, true))
            {
              // The rewrite requires the full left-hand prefix length to be
              // stripped (otherwise we would have to keep parts of the
              // left-hand prefix).
              if (lenPfx0.isConst() && lenPfx0.getConst<Rational>().isZero())
              {
                std::vector<Node> sfxv0(v0.begin() + i, v0.end());
                pfxv1.insert(pfxv1.end(), v1.begin() + j, v1.end());
                Node ret =
                    d_nm->mkNode(Kind::AND,
                                 pfx0.eqNode(utils::mkConcat(rpfxv1, stype)),
                                 utils::mkConcat(sfxv0, stype)
                                     .eqNode(utils::mkConcat(pfxv1, stype)));
                rule = Rewrite::SPLIT_EQ_STRIP_R;
                return ret;
              }
            }

            // If the prefix of the right-hand side is (strictly) longer than
            // the prefix of the left-hand side, we can advance the left-hand
            // side (since the length of the right-hand side is only increasing
            // in the inner loop)
            break;
          }
          else if (d_arithEntail.check(lenPfx0, lenPfx1, true))
          {
            // The prefix on the left-hand side is strictly longer than the
            // prefix on the right-hand side, so we try to strip the left-hand
            // prefix by the length of the right-hand prefix
            //
            // Example:
            // (= (str.++ x "AB" z) (str.++ "A" x y)) --->
            //   (and (= (str.++ x "A") (str.++ "A" x)) (= (str.++ "B" z) y))
            std::vector<Node> sfxv0 = pfxv0;
            std::vector<Node> rpfxv0;
            if (d_stringsEntail.stripSymbolicLength(
                    sfxv0, rpfxv0, 1, lenPfx1, true))
            {
              // The rewrite requires the full right-hand prefix length to be
              // stripped (otherwise we would have to keep parts of the
              // right-hand prefix).
              if (lenPfx1.isConst() && lenPfx1.getConst<Rational>().isZero())
              {
                sfxv0.insert(sfxv0.end(), v0.begin() + i, v0.end());
                std::vector<Node> sfxv1(v1.begin() + j, v1.end());
                Node ret =
                    d_nm->mkNode(Kind::AND,
                                 utils::mkConcat(rpfxv0, stype).eqNode(pfx1),
                                 utils::mkConcat(sfxv0, stype)
                                     .eqNode(utils::mkConcat(sfxv1, stype)));
                rule = Rewrite::SPLIT_EQ_STRIP_L;
                return ret;
              }
            }

            // If the prefix of the left-hand side is (strictly) longer than
            // the prefix of the right-hand side, then we don't need to check
            // that right-hand prefix for future left-hand prefixes anymore
            // (since they are increasing in length)
            startRhs = j + 1;
          }
        }
      }
    }
  }
  return Node::null();
}

Node SequencesRewriter::rewriteViaReLoopElim(const Node& node)
{
  if (node.getKind() != Kind::REGEXP_LOOP)
  {
    return Node::null();
  }
  uint32_t l = utils::getLoopMinOccurrences(node);
  uint32_t u = utils::getLoopMaxOccurrences(node);
  if (u < l)
  {
    return Node::null();
  }
  Node r = node[0];
  std::vector<Node> vec_nodes;
  for (unsigned i = 0; i < l; i++)
  {
    vec_nodes.push_back(r);
  }
  NodeManager* nm = nodeManager();
  Node n = vec_nodes.size() == 0
               ? nm->mkNode(Kind::STRING_TO_REGEXP, nm->mkConst(String("")))
           : vec_nodes.size() == 1 ? r
                                   : nm->mkNode(Kind::REGEXP_CONCAT, vec_nodes);
  Node retNode;
  if (u == l)
  {
    retNode = n;
  }
  else
  {
    std::vector<Node> vec2;
    vec2.push_back(n);
    TypeNode rtype = nm->regExpType();
    for (uint32_t j = l; j < u; j++)
    {
      vec_nodes.push_back(r);
      n = utils::mkConcat(vec_nodes, rtype);
      vec2.push_back(n);
    }
    retNode = nm->mkNode(Kind::REGEXP_UNION, vec2);
  }
  Trace("strings-lp") << "Strings::lp " << node << " => " << retNode
                      << std::endl;
  Assert(retNode != node);
  return retNode;
}

Node SequencesRewriter::rewriteViaStrInReEval(const Node& node)
{
  if (node.getKind() != Kind::STRING_IN_REGEXP || !node[0].isConst()
      || !RegExpEntail::isConstRegExp(node[1]))
  {
    return Node::null();
  }
  // test whether x in node[1]
  String s = node[0].getConst<String>();
  bool test = RegExpEntail::testConstStringInRegExp(s, node[1]);
  return nodeManager()->mkConst(test);
}

Node SequencesRewriter::rewriteViaStrInReConcatStarChar(const Node& n)
{
  if (n.getKind() != Kind::STRING_IN_REGEXP
      || n[0].getKind() != Kind::STRING_CONCAT
      || n[1].getKind() != Kind::REGEXP_STAR)
  {
    return Node::null();
  }
  Node len = RegExpEntail::getFixedLengthForRegexp(n[1][0]);
  if (len.isNull())
  {
    return Node::null();
  }
  if (!len.isConst() || len.getConst<Rational>() != Rational(1))
  {
    return Node::null();
  }
  NodeManager* nm = nodeManager();
  std::vector<Node> cc;
  utils::getConcat(n[0], cc);
  std::vector<Node> conj;
  for (const Node& c : cc)
  {
    conj.push_back(nm->mkNode(Kind::STRING_IN_REGEXP, c, n[1]));
  }
  return nm->mkAnd(conj);
}

Node SequencesRewriter::rewriteViaStrInReSigma(const Node& n)
{
  if (n.getKind() != Kind::STRING_IN_REGEXP
      || n[1].getKind() != Kind::REGEXP_CONCAT)
  {
    return Node::null();
  }
  const Node& r = n[1];
  bool allSigmaStrict = true;
  size_t allSigmaMinSize = 0;
  for (const Node& rc : r)
  {
    if (rc.getKind() == Kind::REGEXP_ALLCHAR)
    {
      allSigmaMinSize++;
    }
    else if (rc.getKind() == Kind::REGEXP_STAR
             && rc[0].getKind() == Kind::REGEXP_ALLCHAR)
    {
      allSigmaStrict = false;
    }
    else
    {
      return Node::null();
    }
  }
  // x in re.++(_*, _, _) ---> str.len(x) >= 2
  NodeManager* nm = nodeManager();
  Node num = nm->mkConstInt(Rational(allSigmaMinSize));
  Node lenx = nm->mkNode(Kind::STRING_LENGTH, n[0]);
  return nm->mkNode(allSigmaStrict ? Kind::EQUAL : Kind::GEQ, lenx, num);
}
Node SequencesRewriter::rewriteViaStrInReSigmaStar(const Node& n)
{
  if (n.getKind() != Kind::STRING_IN_REGEXP
      || n[1].getKind() != Kind::REGEXP_STAR
      || n[1][0].getKind() != Kind::REGEXP_CONCAT)
  {
    return Node::null();
  }
  const Node& r = n[1][0];
  for (const Node& rc : r)
  {
    if (rc.getKind() != Kind::REGEXP_ALLCHAR)
    {
      return Node::null();
    }
  }
  NodeManager* nm = nodeManager();
  Node zero = nm->mkConstInt(Rational(0));
  Node num = nm->mkConstInt(Rational(r.getNumChildren()));
  Node lenx = nm->mkNode(Kind::STRING_LENGTH, n[0]);
  Node t = nm->mkNode(Kind::INTS_MODULUS, lenx, num);
  return nm->mkNode(Kind::EQUAL, t, zero);
}

Node SequencesRewriter::rewriteViaMacroSubstrStripSymLength(const Node& node,
                                                            Rewrite& rule,
                                                            StringsEntail& sent)
{
  if (node.getKind() != Kind::STRING_SUBSTR)
  {
    return Node::null();
  }
  std::vector<Node> ch1;
  std::vector<Node> ch2;
  return sent.rewriteViaMacroSubstrStripSymLength(node, rule, ch1, ch2);
}

Node SequencesRewriter::rewriteViaMacroStrInReInclusion(const Node& n)
{
  if (n.getKind() != Kind::STRING_IN_REGEXP)
  {
    return Node::null();
  }
  // check regular expression inclusion
  // This makes a regular expression that contains all possible model values
  // for x, and checks whether r includes this regular expression. If so,
  // the membership rewrites to true.
  RegExpEntail re(nodeManager(), nullptr);
  Node reForX = re.getGeneralizedConstRegExp(n[0]);
  // only chance of success is if there was at least one constant
  if (!reForX.isNull())
  {
    if (RegExpEntail::regExpIncludes(n[1], reForX))
    {
      return d_true;
    }
  }
  return Node::null();
}

Node SequencesRewriter::rewriteViaMacroStrSplitCtn(const Node& node)
{
  if (node.getKind() != Kind::STRING_CONTAINS
      || node[0].getKind() != Kind::STRING_CONCAT || !node[1].isConst()
      || Word::getLength(node[1]) == 0)  // don't bother if empty string
  {
    return Node::null();
  }
  Node t = node[1];
  // Below, we are looking for a constant component of node[0]
  // has no overlap with node[1], which means we can split.
  // Notice that if the first or last components had no
  // overlap, these would have been removed by strip
  // constant endpoints. Hence, we consider only the inner children.
  for (size_t i = 1, iend = (node[0].getNumChildren() - 1); i < iend; i++)
  {
    // constant contains
    if (node[0][i].isConst())
    {
      // if no overlap, we can split into disjunction
      if (!Word::hasOverlap(node[0][i], node[1], false)
          && !Word::hasOverlap(node[1], node[0][i], false))
      {
        std::vector<Node> nc0;
        utils::getConcat(node[0], nc0);
        std::vector<Node> spl[2];
        spl[0].insert(spl[0].end(), nc0.begin(), nc0.begin() + i);
        Assert(i < nc0.size() - 1);
        spl[1].insert(spl[1].end(), nc0.begin() + i + 1, nc0.end());
        TypeNode stype = node[0].getType();
        Node ret = nodeManager()->mkNode(
            Kind::OR,
            nodeManager()->mkNode(
                Kind::STRING_CONTAINS, utils::mkConcat(spl[0], stype), node[1]),
            nodeManager()->mkNode(Kind::STRING_CONTAINS,
                                  utils::mkConcat(spl[1], stype),
                                  node[1]));
        return ret;
      }
    }
  }
  return Node::null();
}

Node SequencesRewriter::rewriteViaMacroStrStripEndpoints(
    const Node& n,
    std::vector<Node>& nb,
    std::vector<Node>& nrem,
    std::vector<Node>& ne)
{
  Kind k = n.getKind();
  std::vector<int> dirs;
  if (k == Kind::STRING_INDEXOF)
  {
    // must start at zero
    if (!n[2].isConst() || n[2].getConst<Rational>().sgn() != 0)
    {
      return Node::null();
    }
    // only strip off the end
    dirs.push_back(-1);
  }
  else if (k == Kind::STRING_CONTAINS || k == Kind::STRING_REPLACE)
  {
    if (n[1].isConst())
    {
      // if constant, we strip from one direction at a time, to ease proof
      // reconstruction
      dirs.push_back(-1);
      dirs.push_back(1);
    }
    else
    {
      dirs.push_back(0);
    }
  }
  else
  {
    return Node::null();
  }

  std::vector<Node> nc2;
  utils::getConcat(n[1], nc2);
  if (nc2.empty())
  {
    return Node::null();
  }
  // strip endpoints
  bool success = false;
  for (int dir : dirs)
  {
    nrem.clear();
    utils::getConcat(n[0], nrem);
    nb.clear();
    ne.clear();
    if (d_stringsEntail.stripConstantEndpoints(nrem, nc2, nb, ne, dir))
    {
      success = true;
      break;
    }
  }
  if (success)
  {
    NodeManager* nm = nodeManager();
    TypeNode stype = n[0].getType();
    Node rem = utils::mkConcat(nrem, stype);
    switch (k)
    {
      case Kind::STRING_CONTAINS:
      {
        return nm->mkNode(Kind::STRING_CONTAINS, rem, n[1]);
      }
      case Kind::STRING_REPLACE:
      {
        std::vector<Node> cc;
        cc.insert(cc.end(), nb.begin(), nb.end());
        cc.push_back(nm->mkNode(Kind::STRING_REPLACE, rem, n[1], n[2]));
        cc.insert(cc.end(), ne.begin(), ne.end());
        return utils::mkConcat(cc, stype);
      }
      case Kind::STRING_INDEXOF:
      {
        return nm->mkNode(Kind::STRING_INDEXOF, rem, n[1], n[2]);
      }
      default: break;
    }
  }
  return Node::null();
}

Node SequencesRewriter::rewriteViaMacroReInterUnionConstElim(const Node& n)
{
  Kind k = n.getKind();
  if (k != Kind::REGEXP_INTER && k != Kind::REGEXP_UNION)
  {
    return Node::null();
  }
  std::vector<Node> constStrRe;
  std::vector<Node> otherRe;
  for (const Node& nc : n)
  {
    if (!RegExpEntail::isConstRegExp(nc))
    {
      continue;
    }
    if (nc.getKind() == Kind::STRING_TO_REGEXP)
    {
      Assert(nc[0].isConst());
      constStrRe.push_back(nc);
    }
    else
    {
      otherRe.push_back(nc);
    }
  }

  if (constStrRe.empty() || otherRe.empty())
  {
    return Node::null();
  }
  // go back and process constant strings against the others
  std::unordered_set<Node> toRemove;
  for (const Node& c : constStrRe)
  {
    Assert(c.getKind() == Kind::STRING_TO_REGEXP && c[0].isConst());
    String s = c[0].getConst<String>();
    for (const Node& r : otherRe)
    {
      Assert(RegExpEntail::isConstRegExp(r));
      Trace("strings-rewrite-debug")
          << "Check " << c << " vs " << r << std::endl;
      // skip if already removing, or not constant
      if (toRemove.find(r) != toRemove.end())
      {
        Trace("strings-rewrite-debug") << "...skip" << std::endl;
        continue;
      }
      // test whether c from (str.to_re c) is in r
      if (RegExpEntail::testConstStringInRegExp(s, r))
      {
        Trace("strings-rewrite-debug") << "...included" << std::endl;
        if (k == Kind::REGEXP_INTER)
        {
          // (re.inter .. (str.to_re c) .. R ..) --->
          // (re.inter .. (str.to_re c) .. ..) when c in R
          toRemove.insert(r);
        }
        else
        {
          // (re.union .. (str.to_re c) .. R ..) --->
          // (re.union .. .. R ..) when c in R
          toRemove.insert(c);
          break;
        }
      }
      else
      {
        Trace("strings-rewrite-debug") << "...not included" << std::endl;
        if (k == Kind::REGEXP_INTER)
        {
          // (re.inter .. (str.to_re c) .. R ..) ---> re.none
          // if c is not a member of R.
          return nodeManager()->mkNode(Kind::REGEXP_NONE);
        }
      }
    }
  }

  if (!toRemove.empty())
  {
    std::vector<Node> vec;
    for (const Node& nc : n)
    {
      if (toRemove.find(nc) == toRemove.end())
      {
        vec.push_back(nc);
      }
    }
    Assert(!vec.empty());
    return vec.size() == 1 ? vec[0] : nodeManager()->mkNode(k, vec);
  }

  return Node::null();
}

Node SequencesRewriter::rewriteViaStrIndexofReEval(const Node& n)
{
  if (n.getKind() == Kind::STRING_INDEXOF_RE && n[0].isConst() && n[2].isConst()
      && RegExpEntail::isConstRegExp(n[1]))
  {
    NodeManager* nm = nodeManager();
    Rational nrat = n[2].getConst<Rational>();
    String s = n[0].getConst<String>();
    Rational rsize(s.size());
    if (nrat > rsize || nrat.sgn() < 0)
    {
      Node negone = nm->mkConstInt(Rational(-1));
      return negone;
    }
    uint32_t start = nrat.getNumerator().toUnsignedInt();
    Node rem = nm->mkConst(s.substr(start));
    std::pair<size_t, size_t> match = firstMatch(rem, n[1]);
    Node ret = nm->mkConstInt(
        Rational(match.first == string::npos
                     ? -1
                     : static_cast<int64_t>(start + match.first)));
    return ret;
  }
  return Node::null();
}

Node SequencesRewriter::rewriteViaStrReplaceReEval(const Node& n)
{
  if (n.getKind() == Kind::STRING_REPLACE_RE && n[0].isConst()
      && RegExpEntail::isConstRegExp(n[1]))
  {
    NodeManager* nm = nodeManager();
    // str.replace_re("ZABCZ", re.++("A", _*, "C"), y) ---> "Z" ++ y ++ "Z"
    std::pair<size_t, size_t> match = firstMatch(n[0], n[1]);
    if (match.first != string::npos)
    {
      String s = n[0].getConst<String>();
      Node ret = nm->mkNode(Kind::STRING_CONCAT,
                            nm->mkConst(s.substr(0, match.first)),
                            n[2],
                            nm->mkConst(s.substr(match.second)));
      return ret;
    }
    return n[0];
  }
  return Node::null();
}

Node SequencesRewriter::rewriteViaStrReplaceReAllEval(const Node& n)
{
  if (n.getKind() == Kind::STRING_REPLACE_RE_ALL && n[0].isConst()
      && RegExpEntail::isConstRegExp(n[1]))
  {
    NodeManager* nm = nodeManager();
    // str.replace_re_all("ZABCZAB", re.++("A", _*, "C"), y) --->
    //   "Z" ++ y ++ "Z" ++ y
    TypeNode t = n[0].getType();
    Assert(t.isString());
    Node emp = Word::mkEmptyWord(t);
    Node yp = nm->mkNode(Kind::REGEXP_INTER,
                         n[1],
                         nm->mkNode(Kind::REGEXP_COMPLEMENT,
                                    nm->mkNode(Kind::STRING_TO_REGEXP, emp)));
    std::vector<Node> res;
    String rem = n[0].getConst<String>();
    std::pair<size_t, size_t> match(0, 0);
    while (rem.size() != 0)
    {
      match = firstMatch(nm->mkConst(rem), yp);
      if (match.first == string::npos)
      {
        break;
      }
      res.push_back(nm->mkConst(rem.substr(0, match.first)));
      res.push_back(n[2]);
      rem = rem.substr(match.second);
    }
    // only concatenate remainder if non-empty
    if (rem.size()!=0)
    {
      res.push_back(nm->mkConst(rem));
    }
    Node ret = utils::mkConcat(res, t);
    return ret;
  }
  return Node::null();
}

Node SequencesRewriter::rewriteViaOverlap(ProofRewriteRule id, const Node& n)
{
  if (n.getNumChildren() < 2)
  {
    return Node::null();
  }
  // get the list of overlaps to check, based on the rule, which will be passed
  // to Word::hasOverlap below.
  std::vector<std::tuple<Node, Node, int>> overlap;
  Kind k = n.getKind();
  switch (id)
  {
    case ProofRewriteRule::STR_OVERLAP_SPLIT_CTN:
    {
      if (k != Kind::STRING_CONTAINS || n[0].getNumChildren() != 3)
      {
        return Node::null();
      }
      overlap.emplace_back(n[0][1], n[1], false);
      overlap.emplace_back(n[1], n[0][1], false);
    }
    break;
    case ProofRewriteRule::STR_OVERLAP_ENDPOINTS_CTN:
    {
      if (k != Kind::STRING_CONTAINS || n[0].getNumChildren() != 3
          || n[1].getNumChildren() != 3)
      {
        return Node::null();
      }
      overlap.emplace_back(n[0][0], n[1][0], false);
      overlap.emplace_back(n[0][2], n[1][2], true);
    }
    break;
    case ProofRewriteRule::STR_OVERLAP_ENDPOINTS_INDEXOF:
    {
      if (k != Kind::STRING_INDEXOF || n[0].getNumChildren() != 2
          || n[1].getNumChildren() != 2 || !n[2].isConst()
          || n[2].getConst<Rational>().sgn() != 0)
      {
        return Node::null();
      }
      overlap.emplace_back(n[0][1], n[1][1], true);
    }
    break;
    case ProofRewriteRule::STR_OVERLAP_ENDPOINTS_REPLACE:
    {
      if (k != Kind::STRING_REPLACE || n[0].getNumChildren() != 3
          || n[1].getNumChildren() != 3)
      {
        return Node::null();
      }
      overlap.emplace_back(n[0][0], n[1][0], false);
      overlap.emplace_back(n[0][2], n[1][2], true);
    }
    break;
    default: return Node::null();
  }
  for (const std::tuple<Node, Node, int>& f : overlap)
  {
    const Node& c1 = std::get<0>(f);
    const Node& c2 = std::get<1>(f);
    // ensure it is a constant
    if (!c1.isConst() || !c2.isConst())
    {
      return Node::null();
    }
    // if it has an overlap
    if (Word::hasOverlap(c1, c2, std::get<2>(f)))
    {
      return Node::null();
    }
  }

  // checks succeeded, make the appropriate rewritten term
  NodeManager* nm = nodeManager();
  switch (id)
  {
    case ProofRewriteRule::STR_OVERLAP_SPLIT_CTN:
      return nm->mkNode(
          Kind::OR, nm->mkNode(k, n[0][0], n[1]), nm->mkNode(k, n[0][2], n[1]));
    case ProofRewriteRule::STR_OVERLAP_ENDPOINTS_CTN:
      return nm->mkNode(k, n[0][1], n[1]);
    case ProofRewriteRule::STR_OVERLAP_ENDPOINTS_INDEXOF:
      return nm->mkNode(k, n[0][0], n[1], n[2]);
    case ProofRewriteRule::STR_OVERLAP_ENDPOINTS_REPLACE:
      return nm->mkNode(Kind::STRING_CONCAT,
                        n[0][0],
                        nm->mkNode(k, n[0][1], n[1], n[2]),
                        n[0][2]);
    default: break;
  }
  return Node::null();
}

Node SequencesRewriter::rewriteRepeatRegExp(TNode node)
{
  Assert(node.getKind() == Kind::REGEXP_REPEAT);
  NodeManager* nm = nodeManager();
  // ((_ re.^ n) R) --> ((_ re.loop n n) R)
  unsigned r = utils::getRepeatAmount(node);
  Node lop = nm->mkConst(RegExpLoop(r, r));
  Node retNode = nm->mkNode(Kind::REGEXP_LOOP, lop, node[0]);
  return returnRewrite(node, retNode, Rewrite::RE_REPEAT_ELIM);
}

Node SequencesRewriter::rewriteOptionRegExp(TNode node)
{
  Assert(node.getKind() == Kind::REGEXP_OPT);
  NodeManager* nm = nodeManager();
  Node retNode =
      nm->mkNode(Kind::REGEXP_UNION,
                 nm->mkNode(Kind::STRING_TO_REGEXP, nm->mkConst(String(""))),
                 node[0]);
  return returnRewrite(node, retNode, Rewrite::RE_OPT_ELIM);
}

Node SequencesRewriter::rewritePlusRegExp(TNode node)
{
  Assert(node.getKind() == Kind::REGEXP_PLUS);
  NodeManager* nm = nodeManager();
  Node retNode = nm->mkNode(
      Kind::REGEXP_CONCAT, node[0], nm->mkNode(Kind::REGEXP_STAR, node[0]));
  return returnRewrite(node, retNode, Rewrite::RE_PLUS_ELIM);
}

Node SequencesRewriter::rewriteDifferenceRegExp(TNode node)
{
  Assert(node.getKind() == Kind::REGEXP_DIFF);
  NodeManager* nm = nodeManager();
  Node retNode = nm->mkNode(Kind::REGEXP_INTER,
                            node[0],
                            nm->mkNode(Kind::REGEXP_COMPLEMENT, node[1]));
  return returnRewrite(node, retNode, Rewrite::RE_DIFF_ELIM);
}

Node SequencesRewriter::rewriteRangeRegExp(TNode node)
{
  Assert(node.getKind() == Kind::REGEXP_RANGE);
  unsigned ch[2];
  for (size_t i = 0; i < 2; ++i)
  {
    if (!node[i].isConst() || node[i].getConst<String>().size() != 1)
    {
      // not applied to characters, it is not handled
      return node;
    }
    ch[i] = node[i].getConst<String>().front();
  }

  NodeManager* nm = nodeManager();
  if (node[0] == node[1])
  {
    Node retNode = nm->mkNode(Kind::STRING_TO_REGEXP, node[0]);
    // re.range( "A", "A" ) ---> str.to_re( "A" )
    return returnRewrite(node, retNode, Rewrite::RE_RANGE_SINGLE);
  }

  if (ch[0] > ch[1])
  {
    // re.range( "B", "A" ) ---> re.none
    Node retNode = nm->mkNode(Kind::REGEXP_NONE);
    return returnRewrite(node, retNode, Rewrite::RE_RANGE_EMPTY);
  }
  return node;
}


Node SequencesRewriter::rewriteViaStrInReConsume(const Node& node)
{
  if (node.getKind() != Kind::STRING_IN_REGEXP)
  {
    return Node::null();
  }
  // if star, we consider the body of the star
  bool isStar = (node[1].getKind()==Kind::REGEXP_STAR);
  size_t numIter = isStar ? 2 : 1;
  for (size_t i=0; i<numIter; i++)
  {
    int dir = isStar ? (i==0 ? 0 : 1) : -1;
    Node r = isStar ? node[1][0] : node[1];
    std::vector<Node> children;
    utils::getConcat(r, children);
    std::vector<Node> mchildren;
    utils::getConcat(node[0], mchildren);
    Node scn =
        RegExpEntail::simpleRegexpConsume(d_nm, mchildren, children, dir);
    if (!scn.isNull())
    {
      return scn;
    }
    else if (!isStar || children.empty())
    {
      // Given a membership (str.++ x1 ... xn) in (re.++ r1 ... rm),
      // above, we strip components to construct an equivalent membership:
      // (str.++ xi .. xj) in (re.++ rk ... rl).
      Node xn = utils::mkConcat(mchildren, node[0].getType());
      // if we considered the body of the star, we revert to the original RE
      Node rn = isStar ? node[1] : utils::mkConcat(children, node[1].getType());
      // construct the updated regular expression
      Node newMem =
          nodeManager()->mkNode(Kind::STRING_IN_REGEXP,
                                xn,
                                rn);
      if (newMem != node)
      {
        return newMem;
      }
    }
  }
  return Node::null();
}

Node SequencesRewriter::rewriteMembership(TNode node)
{
  Assert(node.getKind() == Kind::STRING_IN_REGEXP);
  NodeManager* nm = nodeManager();
  Node x = node[0];
  Node r = node[1];

  TypeNode stype = x.getType();
  TypeNode rtype = r.getType();

  if (r.getKind() == Kind::REGEXP_NONE)
  {
    Node retNode = nodeManager()->mkConst(false);
    return returnRewrite(node, retNode, Rewrite::RE_IN_EMPTY);
  }
  // test for constant evaluation
  Node eval = rewriteViaStrInReEval(node);
  if (!eval.isNull())
  {
    return returnRewrite(node, eval, Rewrite::RE_IN_EVAL);
  }
  else if (r.getKind() == Kind::REGEXP_ALLCHAR)
  {
    Node one = nm->mkConstInt(Rational(1));
    Node retNode = one.eqNode(nm->mkNode(Kind::STRING_LENGTH, x));
    return returnRewrite(node, retNode, Rewrite::RE_IN_SIGMA);
  }
  else if (r.getKind() == Kind::REGEXP_STAR)
  {
    if (x.isConst())
    {
      size_t xlen = Word::getLength(x);
      if (xlen == 0)
      {
        // e.g. (str.in.re "" (re.* (str.to.re x))) ----> true
        return returnRewrite(node, d_true, Rewrite::RE_EMPTY_IN_STR_STAR);
      }
      else if (xlen == 1)
      {
        if (r[0].getKind() == Kind::STRING_TO_REGEXP)
        {
          Node retNode = r[0][0].eqNode(x);
          // e.g. (str.in.re "A" (re.* (str.to.re x))) ----> "A" = x
          return returnRewrite(node, retNode, Rewrite::RE_CHAR_IN_STR_STAR);
        }
      }
    }
    else if (x.getKind() == Kind::STRING_CONCAT)
    {
      // (str.in.re (str.++ x1 ... xn) (re.* R)) -->
      //   (str.in.re x1 (re.* R)) AND ... AND (str.in.re xn (re.* R))
      //     if the length of all strings in R is one.
      Node flr = RegExpEntail::getFixedLengthForRegexp(r[0]);
      if (!flr.isNull())
      {
        Node one = nm->mkConstInt(Rational(1));
        if (flr == one)
        {
          NodeBuilder nb(nodeManager(), Kind::AND);
          for (const Node& xc : x)
          {
            nb << nm->mkNode(Kind::STRING_IN_REGEXP, xc, r);
          }
          return returnRewrite(
              node, nb.constructNode(), Rewrite::RE_IN_DIST_CHAR_STAR);
        }
      }
    }
    if (r[0].getKind() == Kind::REGEXP_ALLCHAR)
    {
      return returnRewrite(node, d_true, Rewrite::RE_IN_SIGMA_STAR);
    }
    else if (r[0].getKind() == Kind::REGEXP_CONCAT)
    {
      bool isAllchar = true;
      for (const Node& rc : r[0])
      {
        if (rc.getKind() != Kind::REGEXP_ALLCHAR)
        {
          isAllchar = false;
          break;
        }
      }
      if (isAllchar)
      {
        // For example:
        // (str.in_re x (re.* re.allchar re.allchar)) --->
        // (= (mod (str.len x) 2) 0)
        Node zero = nm->mkConstInt(Rational(0));
        Node factor = nm->mkConstInt(Rational(r[0].getNumChildren()));
        Node t = nm->mkNode(
            Kind::INTS_MODULUS, nm->mkNode(Kind::STRING_LENGTH, x), factor);
        Node retNode = t.eqNode(zero);
        return returnRewrite(node, retNode, Rewrite::RE_IN_CHAR_MODULUS_STAR);
      }
    }
  }
  else if (r.getKind() == Kind::REGEXP_CONCAT)
  {
    bool allSigma = true;
    bool allSigmaStrict = true;
    unsigned allSigmaMinSize = 0;
    Node constStr;
    size_t constIdx = 0;
    size_t nchildren = r.getNumChildren();
    for (size_t i = 0; i < nchildren; i++)
    {
      Node rc = r[i];
      Assert(rc.getKind() != Kind::REGEXP_NONE);
      if (rc.getKind() == Kind::REGEXP_ALLCHAR)
      {
        allSigmaMinSize++;
      }
      else if (rc.getKind() == Kind::REGEXP_STAR
               && rc[0].getKind() == Kind::REGEXP_ALLCHAR)
      {
        allSigmaStrict = false;
      }
      else if (rc.getKind() == Kind::STRING_TO_REGEXP)
      {
        if (constStr.isNull())
        {
          constStr = rc[0];
          constIdx = i;
        }
        else
        {
          allSigma = false;
          break;
        }
      }
      else
      {
        allSigma = false;
        break;
      }
    }
    if (allSigma)
    {
      if (constStr.isNull())
      {
        // x in re.++(_*, _, _) ---> str.len(x) >= 2
        Node num = nm->mkConstInt(Rational(allSigmaMinSize));
        Node lenx = nm->mkNode(Kind::STRING_LENGTH, x);
        Node retNode =
            nm->mkNode(allSigmaStrict ? Kind::EQUAL : Kind::GEQ, lenx, num);
        return returnRewrite(node, retNode, Rewrite::RE_CONCAT_PURE_ALLCHAR);
      }
      else if (allSigmaMinSize == 0 && nchildren >= 3 && constIdx != 0
               && constIdx != nchildren - 1)
      {
        // x in re.++(_*, "abc", _*) ---> str.contains(x, "abc")
        Node retNode = nm->mkNode(Kind::STRING_CONTAINS, x, constStr);
        return returnRewrite(node, retNode, Rewrite::RE_CONCAT_TO_CONTAINS);
      }
    }
  }
  else if (r.getKind() == Kind::REGEXP_INTER
           || r.getKind() == Kind::REGEXP_UNION)
  {
    std::vector<Node> mvec;
    for (unsigned i = 0; i < r.getNumChildren(); i++)
    {
      mvec.push_back(nodeManager()->mkNode(Kind::STRING_IN_REGEXP, x, r[i]));
    }
    Node retNode = nodeManager()->mkNode(
        r.getKind() == Kind::REGEXP_INTER ? Kind::AND : Kind::OR, mvec);
    return returnRewrite(node, retNode, Rewrite::RE_IN_ANDOR);
  }
  else if (r.getKind() == Kind::STRING_TO_REGEXP)
  {
    Node retNode = x.eqNode(r[0]);
    return returnRewrite(node, retNode, Rewrite::RE_IN_CSTRING);
  }
  else if (r.getKind() == Kind::REGEXP_RANGE)
  {
    // x in re.range( char_i, char_j ) ---> i <= str.code(x) <= j
    // we do not do this if the arguments are not constant
    if (RegExpEntail::isConstRegExp(r))
    {
      Node xcode = nm->mkNode(Kind::STRING_TO_CODE, x);
      Node retNode = nm->mkNode(
          Kind::AND,
          nm->mkNode(Kind::LEQ, nm->mkNode(Kind::STRING_TO_CODE, r[0]), xcode),
          nm->mkNode(Kind::LEQ, xcode, nm->mkNode(Kind::STRING_TO_CODE, r[1])));
      return returnRewrite(node, retNode, Rewrite::RE_IN_RANGE);
    }
  }
  else if (r.getKind() == Kind::REGEXP_COMPLEMENT)
  {
    Node retNode = nm->mkNode(Kind::STRING_IN_REGEXP, x, r[0]).negate();
    return returnRewrite(node, retNode, Rewrite::RE_IN_COMPLEMENT);
  }

  // do simple consumes
  Node retNode = rewriteViaStrInReConsume(node);
  if (!retNode.isNull())
  {
    Trace("regexp-ext-rewrite")
        << "Regexp : rewrite : " << node << " -> " << retNode << std::endl;
    return returnRewrite(node, retNode, Rewrite::RE_SIMPLE_CONSUME);
  }
  // check regular expression inclusion
  // This makes a regular expression that contains all possible model values
  // for x, and checks whether r includes this regular expression. If so,
  // the membership rewrites to true.
  Node ret = rewriteViaMacroStrInReInclusion(node);
  if (!ret.isNull())
  {
    return returnRewrite(node, ret, Rewrite::RE_IN_INCLUSION);
  }
  return node;
}

RewriteResponse SequencesRewriter::postRewrite(TNode node)
{
  Trace("sequences-postrewrite")
      << "Strings::SequencesRewriter::postRewrite start " << node << std::endl;
  Node retNode = node;
  Kind nk = node.getKind();
  if (nk == Kind::STRING_CONCAT)
  {
    retNode = rewriteConcat(node);
  }
  else if (nk == Kind::EQUAL)
  {
    retNode = rewriteEquality(node);
  }
  else if (nk == Kind::STRING_LENGTH)
  {
    retNode = rewriteLength(node);
  }
  else if (nk == Kind::STRING_CHARAT)
  {
    retNode = rewriteCharAt(node);
  }
  else if (nk == Kind::STRING_SUBSTR)
  {
    retNode = rewriteSubstr(node);
  }
  else if (nk == Kind::STRING_UPDATE)
  {
    retNode = rewriteUpdate(node);
  }
  else if (nk == Kind::STRING_CONTAINS)
  {
    retNode = rewriteContains(node);
  }
  else if (nk == Kind::STRING_INDEXOF)
  {
    retNode = rewriteIndexof(node);
  }
  else if (nk == Kind::STRING_INDEXOF_RE)
  {
    retNode = rewriteIndexofRe(node);
  }
  else if (nk == Kind::STRING_REPLACE)
  {
    retNode = rewriteReplace(node);
  }
  else if (nk == Kind::STRING_REPLACE_ALL)
  {
    retNode = rewriteReplaceAll(node);
  }
  else if (nk == Kind::STRING_REPLACE_RE)
  {
    retNode = rewriteReplaceRe(node);
  }
  else if (nk == Kind::STRING_REPLACE_RE_ALL)
  {
    retNode = rewriteReplaceReAll(node);
  }
  else if (nk == Kind::STRING_REV)
  {
    retNode = rewriteStrReverse(node);
  }
  else if (nk == Kind::STRING_PREFIX || nk == Kind::STRING_SUFFIX)
  {
    retNode = rewritePrefixSuffix(node);
  }
  else if (nk == Kind::STRING_IN_REGEXP)
  {
    retNode = rewriteMembership(node);
  }
  else if (nk == Kind::REGEXP_ALL)
  {
    retNode = rewriteAllRegExp(node);
  }
  else if (nk == Kind::REGEXP_CONCAT)
  {
    retNode = rewriteConcatRegExp(node);
  }
  else if (nk == Kind::REGEXP_UNION || nk == Kind::REGEXP_INTER)
  {
    retNode = rewriteAndOrRegExp(node);
  }
  else if (nk == Kind::REGEXP_DIFF)
  {
    retNode = rewriteDifferenceRegExp(node);
  }
  else if (nk == Kind::REGEXP_STAR)
  {
    retNode = rewriteStarRegExp(node);
  }
  else if (nk == Kind::REGEXP_PLUS)
  {
    retNode = rewritePlusRegExp(node);
  }
  else if (nk == Kind::REGEXP_OPT)
  {
    retNode = rewriteOptionRegExp(node);
  }
  else if (nk == Kind::REGEXP_RANGE)
  {
    retNode = rewriteRangeRegExp(node);
  }
  else if (nk == Kind::REGEXP_LOOP)
  {
    retNode = rewriteLoopRegExp(node);
  }
  else if (nk == Kind::REGEXP_REPEAT)
  {
    retNode = rewriteRepeatRegExp(node);
  }
  else if (nk == Kind::SEQ_UNIT)
  {
    retNode = rewriteSeqUnit(node);
  }
  else if (nk == Kind::SEQ_NTH)
  {
    retNode = rewriteSeqNth(node);
  }

  Trace("sequences-postrewrite")
      << "Strings::SequencesRewriter::postRewrite returning " << retNode
      << std::endl;
  if (node != retNode)
  {
    Trace("strings-rewrite-debug") << "Strings::SequencesRewriter::postRewrite "
                                   << node << " to " << retNode << std::endl;
    return RewriteResponse(REWRITE_AGAIN_FULL, retNode);
  }
  Trace("strings-rewrite-nf") << "No rewrites for : " << node << std::endl;
  return RewriteResponse(REWRITE_DONE, retNode);
}

RewriteResponse SequencesRewriter::preRewrite(TNode node)
{
  return RewriteResponse(REWRITE_DONE, node);
}

Node SequencesRewriter::rewriteSeqNth(Node node)
{
  Assert(node.getKind() == Kind::SEQ_NTH);
  Node s = node[0];
  Node i = node[1];
  if (s.isConst() && i.isConst())
  {
    size_t len = Word::getLength(s);
    if (i.getConst<Rational>().sgn() != -1)
    {
      Integer posInt = i.getConst<Rational>().getNumerator();
      if (posInt.fitsUnsignedInt() && posInt < Integer(len))
      {
        size_t pos = posInt.toUnsignedInt();
        Node ret = Word::getNth(s, pos);
        return returnRewrite(node, ret, Rewrite::SEQ_NTH_EVAL);
      }
    }
  }

  std::vector<Node> prefix, suffix;
  utils::getConcat(s, suffix);
  if ((i.isConst() && i.getConst<Rational>().isZero())
      || d_stringsEntail.stripSymbolicLength(suffix, prefix, 1, i, true))
  {
    if (suffix.size() > 0)
    {
      if (suffix[0].getKind() == Kind::SEQ_UNIT)
      {
        // (seq.nth (seq.++ prefix (seq.unit x) suffix) n) ---> x
        // if len(prefix) = n
        Node ret = suffix[0][0];
        return returnRewrite(node, ret, Rewrite::SEQ_NTH_EVAL_SYM);
      }
      // TODO: STRING_UNIT?
    }
  }

  return node;
}

Node SequencesRewriter::rewriteCharAt(Node node)
{
  Assert(node.getKind() == Kind::STRING_CHARAT);
  NodeManager* nm = nodeManager();
  Node one = nm->mkConstInt(Rational(1));
  Node retNode = nm->mkNode(Kind::STRING_SUBSTR, node[0], node[1], one);
  return returnRewrite(node, retNode, Rewrite::CHARAT_ELIM);
}

Node SequencesRewriter::rewriteSubstr(Node node)
{
  Assert(node.getKind() == Kind::STRING_SUBSTR);

  NodeManager* nm = nodeManager();
  if (node[0].isConst())
  {
    if (Word::isEmpty(node[0]))
    {
      Node ret = node[0];
      return returnRewrite(node, ret, Rewrite::SS_EMPTYSTR);
    }
    // rewriting for constant arguments
    if (node[1].isConst() && node[2].isConst())
    {
      Node s = node[0];
      cvc5::internal::Rational rMaxInt(String::maxSize());
      uint32_t start;
      if (node[1].getConst<Rational>() > rMaxInt)
      {
        // start beyond the maximum size of strings
        // thus, it must be beyond the end point of this string
        Node ret = Word::mkEmptyWord(node.getType());
        return returnRewrite(node, ret, Rewrite::SS_CONST_START_MAX_OOB);
      }
      else if (node[1].getConst<Rational>().sgn() < 0)
      {
        // start before the beginning of the string
        Node ret = Word::mkEmptyWord(node.getType());
        return returnRewrite(node, ret, Rewrite::SS_CONST_START_NEG);
      }
      else
      {
        start = node[1].getConst<Rational>().getNumerator().toUnsignedInt();
        if (start >= Word::getLength(node[0]))
        {
          // start beyond the end of the string
          Node ret = Word::mkEmptyWord(node.getType());
          return returnRewrite(node, ret, Rewrite::SS_CONST_START_OOB);
        }
      }
      Rational endPt(node[1].getConst<Rational>()
                     + node[2].getConst<Rational>());
      if (endPt > rMaxInt)
      {
        // take up to the end of the string
        size_t lenS = Word::getLength(s);
        Node ret = Word::suffix(s, lenS - start);
        return returnRewrite(node, ret, Rewrite::SS_CONST_LEN_MAX_OOB);
      }
      else if (node[2].getConst<Rational>().sgn() <= 0)
      {
        Node ret = Word::mkEmptyWord(node.getType());
        return returnRewrite(node, ret, Rewrite::SS_CONST_LEN_NON_POS);
      }
      else
      {
        uint32_t len =
            node[2].getConst<Rational>().getNumerator().toUnsignedInt();
        // should not overflow due to checks above
        Assert(start == 0 || start + len > len);
        if (start + len > Word::getLength(node[0]))
        {
          // take up to the end of the string
          size_t lenS = Word::getLength(s);
          Node ret = Word::suffix(s, lenS - start);
          return returnRewrite(node, ret, Rewrite::SS_CONST_END_OOB);
        }
        else
        {
          // compute the substr using the constant string
          Node ret = Word::substr(s, start, len);
          return returnRewrite(node, ret, Rewrite::SS_CONST_SS);
        }
      }
    }
  }
  Node zero = nm->mkConstInt(cvc5::internal::Rational(0));

  // if entailed non-positive length or negative start point
  if (d_arithEntail.check(zero, node[1], true))
  {
    Node ret = Word::mkEmptyWord(node.getType());
    return returnRewrite(node, ret, Rewrite::SS_START_NEG);
  }
  else if (d_arithEntail.check(zero, node[2]))
  {
    Node ret = Word::mkEmptyWord(node.getType());
    return returnRewrite(node, ret, Rewrite::SS_LEN_NON_POS);
  }

  if (node[0].getKind() == Kind::STRING_SUBSTR)
  {
    // (str.substr (str.substr x a b) c d) ---> "" if c >= b
    //
    // Note that this rewrite can be generalized to:
    //
    // (str.substr x a b) ---> "" if a >= (str.len x)
    //
    // This can be done when we generalize our entailment methods to
    // accept an optional context. Then we could conjecture that
    // (str.substr x a b) rewrites to "" and do a case analysis:
    //
    // - a < 0 or b < 0 (the result is trivially empty in these cases)
    // - a >= (str.len x) assuming that { a >= 0, b >= 0 }
    //
    // For example, for (str.substr (str.substr x a a) a a), we could
    // then deduce that under those assumptions, "a" is an
    // over-approximation of the length of (str.substr x a a), which
    // then allows us to reason that the result of the whole term must
    // be empty.
    if (d_arithEntail.check(node[1], node[0][2]))
    {
      Node ret = Word::mkEmptyWord(node.getType());
      return returnRewrite(node, ret, Rewrite::SS_START_GEQ_LEN);
    }
  }
  else if (node[0].getKind() == Kind::STRING_REPLACE)
  {
    // (str.substr (str.replace x y z) 0 n)
    // 	 ---> (str.replace (str.substr x 0 n) y z)
    // if (str.len y) = 1 and (str.len z) = 1
    if (node[1] == zero)
    {
      if (d_stringsEntail.checkLengthOne(node[0][1], true)
          && d_stringsEntail.checkLengthOne(node[0][2], true))
      {
        Node ret = nm->mkNode(
            Kind::STRING_REPLACE,
            nm->mkNode(Kind::STRING_SUBSTR, node[0][0], node[1], node[2]),
            node[0][1],
            node[0][2]);
        return returnRewrite(node, ret, Rewrite::SUBSTR_REPL_SWAP);
      }
    }
  }

  TypeNode stype = node.getType();

  // (str.substr s x x) ---> "" if (str.len s) <= 1
  if (node[1] == node[2] && d_stringsEntail.checkLengthOne(node[0]))
  {
    Node ret = Word::mkEmptyWord(node.getType());
    return returnRewrite(node, ret, Rewrite::SS_LEN_ONE_Z_Z);
  }

  Node slenRew = nm->mkNode(Kind::STRING_LENGTH, node[0]);
  // make strict to avoid infinite loops
  if (d_arithEntail.check(node[2], slenRew, true))
  {
    // end point beyond end point of string, map to slenRew
    Node ret = nm->mkNode(Kind::STRING_SUBSTR, node[0], node[1], slenRew);
    return returnRewrite(node, ret, Rewrite::SS_END_PT_NORM);
  }

  // Rewrite based on symbolic length analysis, using the strings entailment
  // utility that is owned by this rewriter. This handles three rewrite rules
  // that are also included as part of the macro proof rewrite rule
  // MACRO_SUBSTR_STRIP_SYM_LENGTH.
  Rewrite ruleSymLen;
  Node retSymLen =
      rewriteViaMacroSubstrStripSymLength(node, ruleSymLen, d_stringsEntail);
  if (!retSymLen.isNull())
  {
    return returnRewrite(node, retSymLen, ruleSymLen);
  }
  // combine substr
  if (node[0].getKind() == Kind::STRING_SUBSTR)
  {
    Node start_inner = node[0][1];
    Node start_outer = node[1];
    if (d_arithEntail.check(start_outer) && d_arithEntail.check(start_inner))
    {
      // both are positive
      // thus, start point is definitely start_inner+start_outer.
      // We can rewrite if it for certain what the length is

      // the length of a string from the inner substr subtracts the start point
      // of the outer substr
      Node len_from_inner = nm->mkNode(Kind::SUB, node[0][2], start_outer);
      Node len_from_outer = node[2];
      Node new_len;
      Rewrite rule = Rewrite::NONE;
      // take quantity that is for sure smaller than the other
      if (len_from_inner == len_from_outer)
      {
        new_len = len_from_inner;
        rule = Rewrite::SS_COMBINE_EQ;
      }
      else if (d_arithEntail.check(len_from_inner, len_from_outer))
      {
        new_len = len_from_outer;
        rule = Rewrite::SS_COMBINE_GEQ_INNER;
      }
      else if (d_arithEntail.check(len_from_outer, len_from_inner))
      {
        new_len = len_from_inner;
        rule = Rewrite::SS_COMBINE_GEQ_OUTER;
      }
      if (!new_len.isNull())
      {
        Node new_start = nm->mkNode(Kind::ADD, start_inner, start_outer);
        Node ret =
            nm->mkNode(Kind::STRING_SUBSTR, node[0][0], new_start, new_len);
        return returnRewrite(node, ret, rule);
      }
    }
  }
  return node;
}

Node SequencesRewriter::rewriteUpdate(Node node)
{
  Assert(node.getKind() == Kind::STRING_UPDATE);
  Node s = node[0];
  Node i = node[1];
  Node x = node[2];
  if (s.isConst())
  {
    if (Word::isEmpty(s))
    {
      return returnRewrite(node, s, Rewrite::UPD_EMPTYSTR);
    }
    // rewriting for constant arguments
    if (node[1].isConst())
    {
      cvc5::internal::Rational rMaxInt(String::maxSize());
      if (node[1].getConst<Rational>() > rMaxInt)
      {
        // start beyond the maximum size of strings
        // thus, it must be beyond the end point of this string
        return returnRewrite(node, s, Rewrite::UPD_CONST_INDEX_MAX_OOB);
      }
      else if (node[1].getConst<Rational>().sgn() < 0)
      {
        // start before the beginning of the string
        return returnRewrite(node, s, Rewrite::UPD_CONST_INDEX_NEG);
      }
      uint32_t start =
          node[1].getConst<Rational>().getNumerator().toUnsignedInt();
      size_t len = Word::getLength(s);
      if (start >= len)
      {
        // start beyond the end of the string
        return returnRewrite(node, s, Rewrite::UPD_CONST_INDEX_OOB);
      }
      if (node[2].isConst())
      {
        Node ret = Word::update(s, start, node[2]);
        return returnRewrite(node, ret, Rewrite::UPD_EVAL);
      }
    }
  }

  NodeManager* nm = nodeManager();
  Node zero = nm->mkConstInt(0);
  Node sLen = nm->mkNode(Kind::STRING_LENGTH, s);
  if (d_arithEntail.check(zero, i, true) || d_arithEntail.check(i, sLen))
  {
    // (seq.update s i x) ---> s if x < 0 or x >= len(s)
    Node ret = s;
    return returnRewrite(node, ret, Rewrite::UPD_OOB);
  }

  std::vector<Node> prefix, suffix;
  utils::getConcat(s, suffix);
  if ((i.isConst() && i.getConst<Rational>().isZero())
      || d_stringsEntail.stripSymbolicLength(suffix, prefix, 1, i, true))
  {
    Node updateLen = nm->mkNode(Kind::STRING_LENGTH, x);
    std::vector<Node> replaced;
    if (d_stringsEntail.stripSymbolicLength(
            suffix, replaced, 1, updateLen, true))
    {
      // (seq.update (seq.++ p r s) i x) ---> (seq.++ p x s)
      // if len(p) = i and len(r) = len(x)
      prefix.emplace_back(x);
      prefix.insert(prefix.end(), suffix.begin(), suffix.end());
      Node ret = utils::mkConcat(prefix, node.getType());
      return returnRewrite(node, ret, Rewrite::UPD_EVAL_SYM);
    }
  }

  if (s.getKind() == Kind::STRING_REV && d_stringsEntail.checkLengthOne(x))
  {
    // str.update(str.rev(s), n, t) --->
    //   str.rev(str.update(s, len(s) - (n + 1), t))
    Node idx =
        nm->mkNode(Kind::SUB,
                   nm->mkNode(Kind::STRING_LENGTH, s),
                   nm->mkNode(Kind::ADD, i, nm->mkConstInt(Rational(1))));
    Node ret = nm->mkNode(Kind::STRING_REV,
                          nm->mkNode(Kind::STRING_UPDATE, s[0], idx, x));
    return returnRewrite(node, ret, Rewrite::UPD_REV);
  }

  return node;
}

Node SequencesRewriter::rewriteContains(Node node)
{
  Assert(node.getKind() == Kind::STRING_CONTAINS);
  NodeManager* nm = nodeManager();

  if (node[0] == node[1])
  {
    return returnRewrite(node, d_true, Rewrite::CTN_EQ);
  }
  if (node[0].isConst())
  {
    if (node[1].isConst())
    {
      Node ret = nm->mkConst(Word::find(node[0], node[1]) != std::string::npos);
      return returnRewrite(node, ret, Rewrite::CTN_CONST);
    }
    else
    {
      Node t = node[1];
      if (Word::isEmpty(node[0]))
      {
        Node len1 = nodeManager()->mkNode(Kind::STRING_LENGTH, node[1]);
        if (d_arithEntail.check(len1, true))
        {
          // we handle the false case here since the rewrite for equality
          // uses this function, hence we want to conclude false if possible.
          // len(x)>0 => contains( "", x ) ---> false
          Node ret = nodeManager()->mkConst(false);
          return returnRewrite(node, ret, Rewrite::CTN_LHS_EMPTYSTR);
        }
      }
      else if (d_stringsEntail.checkLengthOne(t))
      {
        std::vector<Node> vec = Word::getChars(node[0]);
        Node emp = Word::mkEmptyWord(t.getType());
        NodeBuilder nb(nodeManager(), Kind::OR);
        nb << emp.eqNode(t);
        for (const Node& c : vec)
        {
          Assert(c.getType() == t.getType());
          nb << c.eqNode(t);
        }

        // str.contains("ABCabc", t) --->
        // t = "" v t = "A" v t = "B" v t = "C" v t = "a" v t = "b" v t = "c"
        // if len(t) <= 1
        Node ret = nb;
        return returnRewrite(node, ret, Rewrite::CTN_SPLIT);
      }
      else
      {
        Node ret =
            rewriteViaRule(ProofRewriteRule::MACRO_STR_CONST_NCTN_CONCAT, node);
        if (!ret.isNull())
        {
          return returnRewrite(node, ret, Rewrite::CTN_NCONST_CTN_CONCAT);
        }
      }
    }
  }
  Node maybeRew;
  Rewrite maybeRule = Rewrite::NONE;
  if (node[1].isConst())
  {
    size_t len = Word::getLength(node[1]);
    if (len == 0)
    {
      // contains( x, "" ) ---> true
      Node ret = nodeManager()->mkConst(true);
      return returnRewrite(node, ret, Rewrite::CTN_RHS_EMPTYSTR);
    }
    else if (len == 1)
    {
      // The following rewrites are specific to a single character second
      // argument of contains, where we can reason that this character is
      // not split over multiple components in the first argument.
      if (node[0].getKind() == Kind::STRING_CONCAT)
      {
        std::vector<Node> nc1;
        utils::getConcat(node[0], nc1);
        NodeBuilder nb(nodeManager(), Kind::OR);
        for (const Node& ncc : nc1)
        {
          nb << nm->mkNode(Kind::STRING_CONTAINS, ncc, node[1]);
        }
        Node ret = nb.constructNode();
        // str.contains( x ++ y, "A" ) --->
        //   str.contains( x, "A" ) OR str.contains( y, "A" )
        // Remember the rewrite, we might find a better rule in following.
        maybeRew = ret;
        maybeRule = Rewrite::CTN_CONCAT_CHAR;
      }
      else if (node[0].getKind() == Kind::STRING_REPLACE)
      {
        Node rplDomain = d_stringsEntail.checkContains(node[0][1], node[1]);
        if (!rplDomain.isNull() && !rplDomain.getConst<bool>())
        {
          Node d1 = nm->mkNode(Kind::STRING_CONTAINS, node[0][0], node[1]);
          Node d2 = nm->mkNode(
              Kind::AND,
              nm->mkNode(Kind::STRING_CONTAINS, node[0][0], node[0][1]),
              nm->mkNode(Kind::STRING_CONTAINS, node[0][2], node[1]));
          Node ret = nm->mkNode(Kind::OR, d1, d2);
          // If str.contains( y, "A" ) ---> false, then:
          // str.contains( str.replace( x, y, z ), "A" ) --->
          //   str.contains( x, "A" ) OR
          //   ( str.contains( x, y ) AND str.contains( z, "A" ) )
          return returnRewrite(node, ret, Rewrite::CTN_REPL_CHAR);
        }
      }
    }
  }
  std::vector<Node> nc1;
  utils::getConcat(node[0], nc1);
  std::vector<Node> nc2;
  utils::getConcat(node[1], nc2);

  // component-wise containment
  Node cret = rewriteViaRule(ProofRewriteRule::MACRO_STR_COMPONENT_CTN, node);
  if (!cret.isNull())
  {
    return returnRewrite(node, cret, Rewrite::CTN_COMPONENT);
  }
  TypeNode stype = node[0].getType();
  
  // (str.contains (str.++ ... s ...) (str.substr s n m)) ---> true
  if (node[1].getKind()==Kind::STRING_SUBSTR)
  {
    if (std::find(nc1.begin(), nc1.end(), node[1][0])!=nc1.end())
    {
      Node res = nm->mkConst(true);
      return returnRewrite(node, res, Rewrite::CTN_CONCAT_CTN_SUBSTR);
    }
  }

  // strip endpoints
  Node retStr =
      rewriteViaRule(ProofRewriteRule::MACRO_STR_STRIP_ENDPOINTS, node);
  if (!retStr.isNull())
  {
    return returnRewrite(node, retStr, Rewrite::CTN_STRIP_ENDPT);
  }

  for (const Node& n : nc2)
  {
    if (nc2.size() > 1)
    {
      Node ctnConst = d_stringsEntail.checkContains(node[0], n);
      if (!ctnConst.isNull() && !ctnConst.getConst<bool>())
      {
        Node res = nm->mkConst(false);
        return returnRewrite(node, res, Rewrite::CTN_CONCAT_COM_NON_CTN);
      }
    }
    if (n.getKind() == Kind::STRING_REPLACE)
    {
      // (str.contains x (str.replace y z w)) --> false
      // if (str.contains x y) = false and (str.contains x w) = false
      //
      // Reasoning: (str.contains x y) checks that x does not contain y if the
      // replacement does not change y. (str.contains x w) checks that if the
      // replacement changes anything in y, the w makes it impossible for it to
      // occur in x.
      Node ctnConst = d_stringsEntail.checkContains(node[0], n[0]);
      if (!ctnConst.isNull() && !ctnConst.getConst<bool>())
      {
        Node ctnConst2 = d_stringsEntail.checkContains(node[0], n[2]);
        if (!ctnConst2.isNull() && !ctnConst2.getConst<bool>())
        {
          Node res = nm->mkConst(false);
          return returnRewrite(node, res, Rewrite::CTN_RPL_NON_CTN);
        }
      }
    }
  }

  // length entailment
  Node len_n1 = nodeManager()->mkNode(Kind::STRING_LENGTH, node[0]);
  Node len_n2 = nodeManager()->mkNode(Kind::STRING_LENGTH, node[1]);
  if (d_arithEntail.check(len_n2, len_n1, true))
  {
    // len( n2 ) > len( n1 ) => contains( n1, n2 ) ---> false
    Node ret = nodeManager()->mkConst(false);
    return returnRewrite(node, ret, Rewrite::CTN_LEN_INEQ);
  }

  // multi-set reasoning
  //   For example, contains( str.++( x, "b" ), str.++( "a", x ) ) ---> false
  //   since the number of a's in the second argument is greater than the number
  //   of a's in the first argument
  if (d_stringsEntail.checkMultisetSubset(node[0], node[1]))
  {
    Node ret = nm->mkConst(false);
    return returnRewrite(node, ret, Rewrite::CTN_MSET_NSS);
  }

  if (d_arithEntail.check(len_n2, len_n1, false))
  {
    // len( n2 ) >= len( n1 ) => contains( n1, n2 ) ---> n1 = n2
    Node ret = node[0].eqNode(node[1]);
    return returnRewrite(node, ret, Rewrite::CTN_LEN_INEQ_NSTRICT);
  }

  // splitting
  if (node[0].getKind() == Kind::STRING_CONCAT)
  {
    // e.g. (str.contains (str.++ x "AB" y) "C") -->
    // (or (str.contains x "C") (str.contains y "C")
    Node ret = rewriteViaMacroStrSplitCtn(node);
    if (!ret.isNull())
    {
      return returnRewrite(node, ret, Rewrite::CTN_SPLIT);
    }
  }
  else if (node[0].getKind() == Kind::STRING_SUBSTR)
  {
    // (str.contains (str.substr x n (str.len y)) y) --->
    //   (= (str.substr x n (str.len y)) y)
    //
    // TODO: Remove with under-/over-approximation
    if (node[0][2] == nm->mkNode(Kind::STRING_LENGTH, node[1]))
    {
      Node ret = nm->mkNode(Kind::EQUAL, node[0], node[1]);
      return returnRewrite(node, ret, Rewrite::CTN_SUBSTR);
    }
  }
  else if (node[0].getKind() == Kind::STRING_REPLACE)
  {
    if (node[0][0] == node[0][2])
    {
      // (str.contains (str.replace x y x) y) ---> (str.contains x y)
      if (node[0][1] == node[1])
      {
        Node ret = nm->mkNode(Kind::STRING_CONTAINS, node[0][0], node[1]);
        return returnRewrite(node, ret, Rewrite::CTN_REPL_TO_CTN);
      }

      // (str.contains (str.replace x y x) z) ---> (str.contains x z)
      // if (str.len z) <= 1
      if (d_stringsEntail.checkLengthOne(node[1]))
      {
        Node ret = nm->mkNode(Kind::STRING_CONTAINS, node[0][0], node[1]);
        return returnRewrite(node, ret, Rewrite::CTN_REPL_LEN_ONE_TO_CTN);
      }
    }

    // (str.contains (str.replace x y z) z) --->
    //   (or (str.contains x y) (str.contains x z))
    if (node[0][2] == node[1])
    {
      Node ret =
          nm->mkNode(Kind::OR,
                     nm->mkNode(Kind::STRING_CONTAINS, node[0][0], node[0][1]),
                     nm->mkNode(Kind::STRING_CONTAINS, node[0][0], node[0][2]));
      return returnRewrite(node, ret, Rewrite::CTN_REPL_TO_CTN_DISJ);
    }
  }
  else if (node[0].getKind() == Kind::STRING_ITOS && node[1].isConst())
  {
    String s = node[1].getConst<String>();
    if (!s.isNumber())
    {
      Node ret = nm->mkConst(false);
      return returnRewrite(node, ret, Rewrite::CTN_ITOS_NON_DIGIT);
    }
  }

  if (node[1].getKind() == Kind::STRING_REPLACE)
  {
    // (str.contains x (str.replace y x y)) --->
    //   (str.contains x y)
    if (node[0] == node[1][1] && node[1][0] == node[1][2])
    {
      Node ret = nm->mkNode(Kind::STRING_CONTAINS, node[0], node[1][0]);
      return returnRewrite(node, ret, Rewrite::CTN_REPL);
    }

    // (str.contains x (str.replace "" x y)) --->
    //   (= "" (str.replace "" x y))
    //
    // Note: Length-based reasoning is not sufficient to get this rewrite. We
    // can neither show that str.len(str.replace("", x, y)) - str.len(x) >= 0
    // nor str.len(x) - str.len(str.replace("", x, y)) >= 0
    Node emp = Word::mkEmptyWord(stype);
    if (node[0] == node[1][1] && node[1][0] == emp)
    {
      Node ret = nm->mkNode(Kind::EQUAL, emp, node[1]);
      return returnRewrite(node, ret, Rewrite::CTN_REPL_EMPTY);
    }
  }
  // If we marked a rewrite but did not yet return it.
  if (!maybeRew.isNull())
  {
    return returnRewrite(node, maybeRew, maybeRule);
  }

  return node;
}

Node SequencesRewriter::rewriteIndexof(Node node)
{
  Assert(node.getKind() == Kind::STRING_INDEXOF);
  NodeManager* nm = nodeManager();

  if (node[2].isConst() && node[2].getConst<Rational>().sgn() < 0)
  {
    // z<0  implies  str.indexof( x, y, z ) --> -1
    Node negone = nm->mkConstInt(Rational(-1));
    return returnRewrite(node, negone, Rewrite::IDOF_NEG);
  }

  // the string type
  TypeNode stype = node[0].getType();

  // evaluation and simple cases
  std::vector<Node> children0;
  utils::getConcat(node[0], children0);
  if (children0[0].isConst() && node[1].isConst() && node[2].isConst())
  {
    cvc5::internal::Rational rMaxInt(cvc5::internal::String::maxSize());
    if (node[2].getConst<Rational>() > rMaxInt)
    {
      if (node[0].isConst())
      {
        // We know that, due to limitations on the size of string constants
        // in our implementation, that accessing a position greater than
        // rMaxInt is guaranteed to be out of bounds.
        Node negone = nm->mkConstInt(Rational(-1));
        return returnRewrite(node, negone, Rewrite::IDOF_MAX);
      }
    }
    else
    {
      Assert(node[2].getConst<Rational>().sgn() >= 0);
      Node s = children0[0];
      Node t = node[1];
      uint32_t start =
          node[2].getConst<Rational>().getNumerator().toUnsignedInt();
      std::size_t ret = Word::find(s, t, start);
      if (ret != std::string::npos)
      {
        Node retv = nm->mkConstInt(Rational(static_cast<unsigned>(ret)));
        return returnRewrite(node, retv, Rewrite::IDOF_FIND);
      }
      else if (children0.size() == 1)
      {
        Node negone = nm->mkConstInt(Rational(-1));
        return returnRewrite(node, negone, Rewrite::IDOF_NFIND);
      }
    }
  }

  if (node[0] == node[1])
  {
    if (node[2].isConst())
    {
      if (node[2].getConst<Rational>().sgn() == 0)
      {
        // indexof( x, x, 0 ) --> 0
        Node zero = nm->mkConstInt(Rational(0));
        return returnRewrite(node, zero, Rewrite::IDOF_EQ_CST_START);
      }
    }
    if (d_arithEntail.check(node[2], true))
    {
      // y>0  implies  indexof( x, x, y ) --> -1
      Node negone = nm->mkConstInt(Rational(-1));
      return returnRewrite(node, negone, Rewrite::IDOF_EQ_NSTART);
    }
    Node emp = Word::mkEmptyWord(stype);
    if (node[0] != emp)
    {
      // indexof( x, x, z ) ---> indexof( "", "", z )
      Node ret = nm->mkNode(Kind::STRING_INDEXOF, emp, emp, node[2]);
      return returnRewrite(node, ret, Rewrite::IDOF_EQ_NORM);
    }
  }

  Node len0 = nm->mkNode(Kind::STRING_LENGTH, node[0]);
  Node len1 = nm->mkNode(Kind::STRING_LENGTH, node[1]);
  Node len0m2 = nm->mkNode(Kind::SUB, len0, node[2]);

  if (node[1].isConst())
  {
    if (Word::isEmpty(node[1]))
    {
      if (d_arithEntail.check(len0, node[2]) && d_arithEntail.check(node[2]))
      {
        // len(x)>=z ^ z >=0 implies indexof( x, "", z ) ---> z
        return returnRewrite(node, node[2], Rewrite::IDOF_EMP_IDOF);
      }
    }
  }

  if (d_arithEntail.check(len1, len0m2, true))
  {
    // len(x)-z < len(y)  implies  indexof( x, y, z ) ----> -1
    Node negone = nm->mkConstInt(Rational(-1));
    return returnRewrite(node, negone, Rewrite::IDOF_LEN);
  }

  Node fstr = node[0];
  if (!node[2].isConst() || node[2].getConst<Rational>().sgn() != 0)
  {
    fstr = nm->mkNode(Kind::STRING_SUBSTR, node[0], node[2], len0);
  }

  Node cmp_conr = d_stringsEntail.checkContains(fstr, node[1]);
  Trace("strings-rewrite-debug") << "For " << node << ", check contains("
                                 << fstr << ", " << node[1] << ")" << std::endl;
  Trace("strings-rewrite-debug") << "...got " << cmp_conr << std::endl;
  std::vector<Node> children1;
  utils::getConcat(node[1], children1);
  if (!cmp_conr.isNull())
  {
    if (cmp_conr.getConst<bool>())
    {
      if (node[2].isConst() && node[2].getConst<Rational>().sgn() == 0)
      {
        // past the first position in node[0] that contains node[1], we can drop
        std::vector<Node> nb;
        std::vector<Node> ne;
        int cc = d_stringsEntail.componentContains(
            children0, children1, nb, ne, true, 1);
        if (cc != -1 && !ne.empty())
        {
          // For example:
          // str.indexof(str.++(x,y,z),y,0) ---> str.indexof(str.++(x,y),y,0)
          Node nn = utils::mkConcat(children0, stype);
          Node ret = nm->mkNode(Kind::STRING_INDEXOF, nn, node[1], node[2]);
          return returnRewrite(node, ret, Rewrite::IDOF_DEF_CTN);
        }

        // Strip components from the beginning that are guaranteed not to match
        if (d_stringsEntail.stripConstantEndpoints(
                children0, children1, nb, ne, 1))
        {
          // str.indexof(str.++("AB", x, "C"), "C", 0) --->
          // 2 + str.indexof(str.++(x, "C"), "C", 0)
          Node ret = nm->mkNode(
              Kind::ADD,
              nm->mkNode(Kind::STRING_LENGTH, utils::mkConcat(nb, stype)),
              nm->mkNode(Kind::STRING_INDEXOF,
                         utils::mkConcat(children0, stype),
                         node[1],
                         node[2]));
          return returnRewrite(node, ret, Rewrite::IDOF_STRIP_CNST_ENDPTS);
        }
      }
      // To show that the first argument definitely contains the second, the
      // index must be a valid index in the first argument. This ensures that
      // (str.indexof t "" n) is not rewritten to something other than -1 when n
      // is beyond the length of t. This is not required for the above rewrites,
      // which only apply when n=0.
      if (d_arithEntail.check(node[2]) && d_arithEntail.check(len0, node[2]))
      {
        // strip symbolic length
        Node new_len = node[2];
        std::vector<Node> nr;
        if (d_stringsEntail.stripSymbolicLength(children0, nr, 1, new_len))
        {
          // For example:
          // z>=0 and z>str.len( x1 ) and str.contains( x2, y )-->true
          // implies
          // str.indexof( str.++( x1, x2 ), y, z ) --->
          // str.len( x1 ) + str.indexof( x2, y, z-str.len(x1) )
          Node nn = utils::mkConcat(children0, stype);
          Node ret = nm->mkNode(
              Kind::ADD,
              nm->mkNode(Kind::SUB, node[2], new_len),
              nm->mkNode(Kind::STRING_INDEXOF, nn, node[1], new_len));
          return returnRewrite(node, ret, Rewrite::IDOF_STRIP_SYM_LEN);
        }
      }
    }
    else
    {
      // str.contains( x, y ) --> false  implies  str.indexof(x,y,z) --> -1
      Node negone = nm->mkConstInt(Rational(-1));
      return returnRewrite(node, negone, Rewrite::IDOF_NCTN);
    }
  }
  else
  {
    Node new_len = node[2];
    std::vector<Node> nr;
    if (d_stringsEntail.stripSymbolicLength(children0, nr, 1, new_len))
    {
      // Normalize the string before the start index.
      //
      // For example:
      // str.indexof(str.++("ABCD", x), y, 3) --->
      // str.indexof(str.++("AAAD", x), y, 3)
      Node nodeNr = utils::mkConcat(nr, stype);
      Node normNr = lengthPreserveRewrite(nodeNr);
      if (normNr != nodeNr)
      {
        std::vector<Node> normNrChildren;
        utils::getConcat(normNr, normNrChildren);
        std::vector<Node> children(normNrChildren);
        children.insert(children.end(), children0.begin(), children0.end());
        Node nn = utils::mkConcat(children, stype);
        Node res = nm->mkNode(Kind::STRING_INDEXOF, nn, node[1], node[2]);
        return returnRewrite(node, res, Rewrite::IDOF_NORM_PREFIX);
      }
    }
  }

  if (node[2].isConst() && node[2].getConst<Rational>().sgn() == 0)
  {
    Node retStr =
        rewriteViaRule(ProofRewriteRule::MACRO_STR_STRIP_ENDPOINTS, node);
    if (!retStr.isNull())
    {
      // For example:
      // str.indexof( str.++( x, "A" ), "B", 0 ) ---> str.indexof( x, "B", 0 )
      return returnRewrite(node, retStr, Rewrite::RPL_PULL_ENDPT);
    }
  }

  return node;
}

Node SequencesRewriter::rewriteIndexofRe(Node node)
{
  Assert(node.getKind() == Kind::STRING_INDEXOF_RE);
  NodeManager* nm = nodeManager();
  Node s = node[0];
  Node r = node[1];
  Node n = node[2];
  Node zero = nm->mkConstInt(Rational(0));
  Node slen = nm->mkNode(Kind::STRING_LENGTH, s);

  if (d_arithEntail.check(zero, n, true) || d_arithEntail.check(n, slen, true))
  {
    Node ret = nm->mkConstInt(Rational(-1));
    return returnRewrite(node, ret, Rewrite::INDEXOF_RE_INVALID_INDEX);
  }

  if (RegExpEntail::isConstRegExp(r))
  {
    Node neval = rewriteViaStrIndexofReEval(node);
    if (!neval.isNull())
    {
      return returnRewrite(node, neval, Rewrite::INDEXOF_RE_EVAL);
    }
    if (d_arithEntail.check(n, zero) && d_arithEntail.check(slen, n))
    {
      String emptyStr("");
      if (RegExpEntail::testConstStringInRegExp(emptyStr, r))
      {
        return returnRewrite(node, n, Rewrite::INDEXOF_RE_EMP_RE);
      }
    }
    if (r.getKind()==Kind::REGEXP_NONE)
    {
      Node ret = nm->mkConstInt(Rational(-1));
      return returnRewrite(node, ret, Rewrite::INDEXOF_RE_NONE);
    }
  }
  return node;
}

Node SequencesRewriter::rewriteReplace(Node node)
{
  Assert(node.getKind() == Kind::STRING_REPLACE);
  NodeManager* nm = nodeManager();

  // the string type
  TypeNode stype = node.getType();

  std::vector<Node> children0;
  utils::getConcat(node[0], children0);

  if (node[1].isConst() && children0[0].isConst())
  {
    Node s = children0[0];
    Node t = node[1];
    std::size_t p = Word::find(s, t);
    if (p == std::string::npos)
    {
      if (children0.size() == 1)
      {
        return returnRewrite(node, node[0], Rewrite::RPL_CONST_NFIND);
      }
    }
    else
    {
      Node s1 = Word::substr(s, 0, p);
      Node s3 = Word::substr(s, p + Word::getLength(t));
      std::vector<Node> children;
      if (!Word::isEmpty(s1))
      {
        children.push_back(s1);
      }
      children.push_back(node[2]);
      if (!Word::isEmpty(s3))
      {
        children.push_back(s3);
      }
      children.insert(children.end(), children0.begin() + 1, children0.end());
      Node ret;
      if (children0.size() == 1 && node[2].isConst())
      {
        // evaluate the constant, this ensures that we always immediately
        // evaluate constants immediately, which is important for proof
        // reconstruction.
        ret = Word::mkWordFlatten(children);
      }
      else
      {
        ret = utils::mkConcat(children, stype);
      }
      return returnRewrite(node, ret, Rewrite::RPL_CONST_FIND);
    }
  }

  if (node[1].isConst() && Word::isEmpty(node[1]))
  {
    Node ret = nm->mkNode(Kind::STRING_CONCAT, node[2], node[0]);
    return returnRewrite(node, ret, Rewrite::RPL_RPL_EMPTY);
  }

  // rewrites that apply to both replace and replaceall
  Node rri = rewriteReplaceInternal(node);
  if (!rri.isNull())
  {
    // printing of the rewrite managed by the call above
    return rri;
  }

  if (node[0] == node[2])
  {
    // ( len( y )>=len(x) ) => str.replace( x, y, x ) ---> x
    Node l0 = nodeManager()->mkNode(Kind::STRING_LENGTH, node[0]);
    Node l1 = nodeManager()->mkNode(Kind::STRING_LENGTH, node[1]);
    if (d_arithEntail.check(l1, l0))
    {
      return returnRewrite(node, node[0], Rewrite::RPL_RPL_LEN_ID);
    }
  }

  std::vector<Node> children1;
  utils::getConcat(node[1], children1);

  // check if contains definitely does (or does not) hold
  Node cmp_conr = d_stringsEntail.checkContains(node[0], node[1]);
  if (!cmp_conr.isNull())
  {
    Assert(cmp_conr.isConst());
    if (cmp_conr.getConst<bool>())
    {
      // component-wise containment
      std::vector<Node> cb;
      std::vector<Node> ce;
      int cc = d_stringsEntail.componentContains(
          children0, children1, cb, ce, true, 1);
      if (cc != -1)
      {
        if (cc == 0 && children0[0] == children1[0])
        {
          // definitely a prefix, can do the replace
          // for example,
          //   str.replace( str.++( x, "ab" ), str.++( x, "a" ), y )  --->
          //   str.++( y, "b" )
          std::vector<Node> cres;
          cres.push_back(node[2]);
          cres.insert(cres.end(), ce.begin(), ce.end());
          Node ret = utils::mkConcat(cres, stype);
          return returnRewrite(node, ret, Rewrite::RPL_CCTN_RPL);
        }
        else if (!ce.empty())
        {
          // we can pull remainder past first definite containment
          // for example,
          //   str.replace( str.++( x, "ab" ), "a", y ) --->
          //   str.++( str.replace( str.++( x, "a" ), "a", y ), "b" )
          // this is independent of whether the second argument may be empty
          std::vector<Node> scc;
          scc.push_back(nodeManager()->mkNode(Kind::STRING_REPLACE,
                                              utils::mkConcat(children0, stype),
                                              node[1],
                                              node[2]));
          scc.insert(scc.end(), ce.begin(), ce.end());
          Node ret = utils::mkConcat(scc, stype);
          return returnRewrite(node, ret, Rewrite::RPL_CCTN);
        }
      }
    }
    else
    {
      // ~contains( t, s ) => ( replace( t, s, r ) ----> t )
      return returnRewrite(node, node[0], Rewrite::RPL_NCTN);
    }
  }

  if (d_stringsEntail.checkNonEmpty(node[1]))
  {
    // pull endpoints that can be stripped
    // for example,
    //   str.replace( str.++( "b", x, "b" ), "a", y ) --->
    //   str.++( "b", str.replace( x, "a", y ), "b" )
    Node retStr =
        rewriteViaRule(ProofRewriteRule::MACRO_STR_STRIP_ENDPOINTS, node);
    if (!retStr.isNull())
    {
      return returnRewrite(node, retStr, Rewrite::RPL_PULL_ENDPT);
    }
  }

  children1.clear();
  utils::getConcat(node[1], children1);
  Node lastChild1 = children1[children1.size() - 1];
  if (lastChild1.getKind() == Kind::STRING_SUBSTR)
  {
    // (str.replace x (str.++ t (str.substr y i j)) z) --->
    // (str.replace x (str.++ t
    //                  (str.substr y i (+ (str.len x) 1 (- (str.len t))))) z)
    // if j > len(x)
    //
    // Reasoning: If the string to be replaced is longer than x, then it does
    // not matter how much longer it is, the result is always x. Thus, it is
    // fine to only look at the prefix of length len(x) + 1 - len(t).

    children1.pop_back();
    // Length of the non-substr components in the second argument
    Node partLen1 =
        nm->mkNode(Kind::STRING_LENGTH, utils::mkConcat(children1, stype));
    Node maxLen1 = nm->mkNode(Kind::ADD, partLen1, lastChild1[2]);

    Node zero = nm->mkConstInt(Rational(0));
    Node one = nm->mkConstInt(Rational(1));
    Node len0 = nm->mkNode(Kind::STRING_LENGTH, node[0]);
    Node len0_1 = nm->mkNode(Kind::ADD, len0, one);
    // Check len(t) + j > len(x) + 1
    if (d_arithEntail.check(maxLen1, len0_1, true))
    {
      children1.push_back(nm->mkNode(
          Kind::STRING_SUBSTR,
          lastChild1[0],
          lastChild1[1],
          nm->mkNode(Kind::ADD, len0, one, nm->mkNode(Kind::NEG, partLen1))));
      Node res = nm->mkNode(Kind::STRING_REPLACE,
                            node[0],
                            utils::mkConcat(children1, stype),
                            node[2]);
      return returnRewrite(node, res, Rewrite::REPL_SUBST_IDX);
    }
  }

  if (node[0].getKind() == Kind::STRING_REPLACE)
  {
    Node x = node[0];
    Node y = node[1];
    Node z = node[2];
    if (x[0] == x[2] && x[0] == y)
    {
      // (str.replace (str.replace y w y) y z) -->
      //   (str.replace (str.replace y w z) y z)
      // if (str.len w) >= (str.len z) and w != z
      //
      // Reasoning: There are two cases: (1) w does not appear in y and (2) w
      // does appear in y.
      //
      // Case (1): In this case, the reasoning is trivial. The
      // inner replace does not do anything, so we can just replace its third
      // argument with any string.
      //
      // Case (2): After the inner replace, we are guaranteed to have a string
      // that contains y at the index of w in the original string y. The outer
      // replace then replaces that y with z, so we can short-circuit that
      // replace by directly replacing w with z in the inner replace. We can
      // only do that if the result of the new inner replace does not contain
      // y, otherwise we end up doing two replaces that are different from the
      // original expression. We enforce that by requiring that the length of w
      // has to be greater or equal to the length of z and that w and z have to
      // be different. This makes sure that an inner replace changes a string
      // to a string that is shorter than y, making it impossible for the outer
      // replace to match.
      Node w = x[1];

      // (str.len w) >= (str.len z)
      Node wlen = nm->mkNode(Kind::STRING_LENGTH, w);
      Node zlen = nm->mkNode(Kind::STRING_LENGTH, z);
      if (d_arithEntail.check(wlen, zlen))
      {
        // w != z
        if (w != z && w.isConst() && z.isConst())
        {
          Node ret = nm->mkNode(Kind::STRING_REPLACE,
                                nm->mkNode(Kind::STRING_REPLACE, y, w, z),
                                y,
                                z);
          return returnRewrite(node, ret, Rewrite::REPL_REPL_SHORT_CIRCUIT);
        }
      }
    }
  }

  if (node[1].getKind() == Kind::STRING_REPLACE)
  {
    if (node[1][0] == node[0])
    {
      if (node[1][0] == node[1][2] && node[1][0] == node[2])
      {
        // str.replace( x, str.replace( x, y, x ), x ) ---> x
        return returnRewrite(node, node[0], Rewrite::REPL_REPL2_INV_ID);
      }
      bool dualReplIteSuccess = false;
      Node cmp_con2 = d_stringsEntail.checkContains(node[1][0], node[1][2]);
      if (!cmp_con2.isNull() && !cmp_con2.getConst<bool>())
      {
        // str.contains( x, z ) ---> false
        //   implies
        // str.replace( x, str.replace( x, y, z ), w ) --->
        // ite( str.contains( x, y ), x, w )
        dualReplIteSuccess = true;
      }
      else
      {
        // str.contains( y, z ) ---> false and str.contains( z, y ) ---> false
        //   implies
        // str.replace( x, str.replace( x, y, z ), w ) --->
        // ite( str.contains( x, y ), x, w )
        cmp_con2 = d_stringsEntail.checkContains(node[1][1], node[1][2]);
        if (!cmp_con2.isNull() && !cmp_con2.getConst<bool>())
        {
          cmp_con2 = d_stringsEntail.checkContains(node[1][2], node[1][1]);
          if (!cmp_con2.isNull() && !cmp_con2.getConst<bool>())
          {
            dualReplIteSuccess = true;
          }
        }
      }
      if (dualReplIteSuccess)
      {
        Node res =
            nm->mkNode(Kind::ITE,
                       nm->mkNode(Kind::STRING_CONTAINS, node[0], node[1][1]),
                       node[0],
                       node[2]);
        return returnRewrite(node, res, Rewrite::REPL_DUAL_REPL_ITE);
      }
    }

    bool invSuccess = false;
    if (node[1][1] == node[0])
    {
      if (node[1][0] == node[1][2])
      {
        // str.replace(x, str.replace(y, x, y), w) ---> str.replace(x, y, w)
        invSuccess = true;
      }
      else if (node[1][1] == node[2] || node[1][0] == node[2])
      {
        // str.contains(y, z) ----> false and ( y == w or x == w ) implies
        //   implies
        // str.replace(x, str.replace(y, x, z), w) ---> str.replace(x, y, w)
        Node cmp_con2 = d_stringsEntail.checkContains(node[1][0], node[1][2]);
        invSuccess = !cmp_con2.isNull() && !cmp_con2.getConst<bool>();
      }
    }
    else
    {
      // str.contains(x, z) ----> false and str.contains(x, w) ----> false
      //   implies
      // str.replace(x, str.replace(y, z, w), u) ---> str.replace(x, y, u)
      Node cmp_con2 = d_stringsEntail.checkContains(node[0], node[1][1]);
      if (!cmp_con2.isNull() && !cmp_con2.getConst<bool>())
      {
        cmp_con2 = d_stringsEntail.checkContains(node[0], node[1][2]);
        invSuccess = !cmp_con2.isNull() && !cmp_con2.getConst<bool>();
      }
    }
    if (invSuccess)
    {
      Node res = nm->mkNode(Kind::STRING_REPLACE, node[0], node[1][0], node[2]);
      return returnRewrite(node, res, Rewrite::REPL_REPL2_INV);
    }
  }
  if (node[2].getKind() == Kind::STRING_REPLACE)
  {
    if (node[2][1] == node[0])
    {
      // str.contains( z, w ) ----> false implies
      // str.replace( x, w, str.replace( z, x, y ) ) ---> str.replace( x, w, z )
      Node cmp_con2 = d_stringsEntail.checkContains(node[2][0], node[1]);
      if (!cmp_con2.isNull() && !cmp_con2.getConst<bool>())
      {
        Node res =
            nm->mkNode(Kind::STRING_REPLACE, node[0], node[1], node[2][0]);
        return returnRewrite(node, res, Rewrite::REPL_REPL3_INV);
      }
    }
    if (node[2][0] == node[1])
    {
      bool success = false;
      if (node[2][0] == node[2][2] && node[2][1] == node[0])
      {
        // str.replace( x, y, str.replace( y, x, y ) ) ---> x
        success = true;
      }
      else
      {
        // str.contains( x, z ) ----> false implies
        // str.replace( x, y, str.replace( y, z, w ) ) ---> x
        cmp_conr = d_stringsEntail.checkContains(node[0], node[2][1]);
        success = !cmp_conr.isNull() && !cmp_conr.getConst<bool>();
      }
      if (success)
      {
        return returnRewrite(node, node[0], Rewrite::REPL_REPL3_INV_ID);
      }
    }
  }
  // miniscope based on components that do not contribute to contains
  // for example,
  //   str.replace( x ++ y ++ x ++ y, "A", z ) -->
  //   str.replace( x ++ y, "A", z ) ++ x ++ y
  // since if "A" occurs in x ++ y ++ x ++ y, then it must occur in x ++ y.
  if (d_stringsEntail.checkLengthOne(node[1]))
  {
    Node lastLhs;
    unsigned lastCheckIndex = 0;
    for (unsigned i = 1, iend = children0.size(); i < iend; i++)
    {
      unsigned checkIndex = children0.size() - i;
      std::vector<Node> checkLhs;
      checkLhs.insert(
          checkLhs.end(), children0.begin(), children0.begin() + checkIndex);
      Node lhs = utils::mkConcat(checkLhs, stype);
      Node rhs = children0[checkIndex];
      Node ctn = d_stringsEntail.checkContains(lhs, rhs);
      if (!ctn.isNull() && ctn.getConst<bool>())
      {
        lastLhs = lhs;
        lastCheckIndex = checkIndex;
      }
      else
      {
        break;
      }
    }
    if (!lastLhs.isNull())
    {
      std::vector<Node> remc(children0.begin() + lastCheckIndex,
                             children0.end());
      Node rem = utils::mkConcat(remc, stype);
      std::vector<Node> rchildren;
      rchildren.push_back(
          nm->mkNode(Kind::STRING_REPLACE, lastLhs, node[1], node[2]));
      // "inline" the components of concatenation, which makes RARE
      // reconstruction easier.
      utils::getConcat(rem, rchildren);
      Node ret = utils::mkConcat(rchildren, lastLhs.getType());
      // for example:
      //   str.replace( x ++ x, "A", y ) ---> str.replace( x, "A", y ) ++ x
      // Since we know that the first occurrence of "A" cannot be in the
      // second occurrence of x. Notice this is specific to single characters
      // due to complications with finds that span multiple components for
      // non-characters.
      return returnRewrite(node, ret, Rewrite::REPL_CHAR_NCONTRIB_FIND);
    }
  }

  // TODO (#1180) incorporate these?
  // contains( t, s ) =>
  //   replace( replace( x, t, s ), s, r ) ----> replace( x, t, r )
  // contains( t, s ) =>
  //   contains( replace( t, s, r ), r ) ----> true

  return node;
}

Node SequencesRewriter::rewriteReplaceAll(Node node)
{
  Assert(node.getKind() == Kind::STRING_REPLACE_ALL);

  TypeNode stype = node.getType();

  if (node[0].isConst() && node[1].isConst())
  {
    std::vector<Node> children;
    Node s = node[0];
    Node t = node[1];
    if (Word::isEmpty(s) || Word::isEmpty(t))
    {
      return returnRewrite(node, node[0], Rewrite::REPLALL_EMPTY_FIND);
    }
    std::size_t sizeS = Word::getLength(s);
    std::size_t sizeT = Word::getLength(t);
    std::size_t index = 0;
    std::size_t curr = 0;
    do
    {
      curr = Word::find(s, t, index);
      if (curr != std::string::npos)
      {
        if (curr > index)
        {
          children.push_back(Word::substr(s, index, curr - index));
        }
        children.push_back(node[2]);
        index = curr + sizeT;
      }
      else
      {
        children.push_back(Word::substr(s, index, sizeS - index));
      }
    } while (curr != std::string::npos && curr < sizeS);
    // constant evaluation
    Node res = utils::mkConcat(children, stype);
    return returnRewrite(node, res, Rewrite::REPLALL_CONST);
  }

  // rewrites that apply to both replace and replaceall
  Node rri = rewriteReplaceInternal(node);
  if (!rri.isNull())
  {
    // printing of the rewrite managed by the call above
    return rri;
  }

  Node cmp_conr = d_stringsEntail.checkContains(node[0], node[1]);
  if (!cmp_conr.isNull() && !cmp_conr.getConst<bool>())
  {
    // ~contains( t, s ) => ( replace_all( t, s, r ) ----> t )
    return returnRewrite(node, node[0], Rewrite::RPL_NCTN);
  }

  return node;
}

Node SequencesRewriter::rewriteReplaceInternal(Node node)
{
  Kind nk = node.getKind();
  Assert(nk == Kind::STRING_REPLACE || nk == Kind::STRING_REPLACE_ALL);

  if (node[1] == node[2])
  {
    return returnRewrite(node, node[0], Rewrite::RPL_ID);
  }

  if (node[0] == node[1])
  {
    // only holds for replaceall if non-empty
    if (nk == Kind::STRING_REPLACE || d_stringsEntail.checkNonEmpty(node[1]))
    {
      return returnRewrite(node, node[2], Rewrite::RPL_REPLACE);
    }
  }

  return Node::null();
}

Node SequencesRewriter::rewriteReplaceRe(Node node)
{
  Assert(node.getKind() == Kind::STRING_REPLACE_RE);
  NodeManager* nm = nodeManager();
  Node x = node[0];
  Node y = node[1];
  Node z = node[2];

  if (RegExpEntail::isConstRegExp(y))
  {
    Node neval = rewriteViaStrReplaceReEval(node);
    if (!neval.isNull())
    {
      return returnRewrite(node, neval, Rewrite::REPLACE_RE_EVAL);
    }
    // str.replace_re( x, y, z ) ---> z ++ x if "" in y ---> true
    String emptyStr("");
    if (RegExpEntail::testConstStringInRegExp(emptyStr, y))
    {
      Node ret = nm->mkNode(Kind::STRING_CONCAT, z, x);
      return returnRewrite(node, ret, Rewrite::REPLACE_RE_EMP_RE);
    }
    if (y.getKind()==Kind::REGEXP_NONE)
    {
      return returnRewrite(node, x, Rewrite::REPLACE_RE_NONE);
    }
  }
  return node;
}

Node SequencesRewriter::rewriteReplaceReAll(Node node)
{
  Assert(node.getKind() == Kind::STRING_REPLACE_RE_ALL);
  Node x = node[0];
  Node y = node[1];
  Node z = node[2];

  if (RegExpEntail::isConstRegExp(y))
  {
    Node neval = rewriteViaStrReplaceReAllEval(node);
    if (!neval.isNull())
    {
      return returnRewrite(node, neval, Rewrite::REPLACE_RE_ALL_EVAL);
    }
    if (y.getKind()==Kind::REGEXP_NONE)
    {
      return returnRewrite(node, x, Rewrite::REPLACE_RE_ALL_NONE);
    }
  }

  return node;
}

std::pair<size_t, size_t> SequencesRewriter::firstMatch(Node n, Node r)
{
  Assert(n.isConst() && n.getType().isStringLike());
  Assert(r.getType().isRegExp());
  NodeManager* nm = nodeManager();

  Node re = nm->mkNode(Kind::REGEXP_CONCAT, r, d_sigmaStar);
  String s = n.getConst<String>();

  if (s.size() == 0)
  {
    if (RegExpEntail::testConstStringInRegExp(s, r))
    {
      return std::make_pair(0, 0);
    }
    else
    {
      return std::make_pair(string::npos, string::npos);
    }
  }

  for (size_t i = 0, size = s.size(); i < size; i++)
  {
    String ss = s.substr(i);
    if (RegExpEntail::testConstStringInRegExp(ss, re))
    {
      for (size_t j = i; j <= size; j++)
      {
        String substr = s.substr(i, j - i);
        if (RegExpEntail::testConstStringInRegExp(substr, r))
        {
          return std::make_pair(i, j);
        }
      }
    }
  }

  return std::make_pair(string::npos, string::npos);
}

Node SequencesRewriter::rewriteStrReverse(Node node)
{
  Assert(node.getKind() == Kind::STRING_REV);
  NodeManager* nm = nodeManager();
  Node x = node[0];
  if (x.isConst())
  {
    // reverse the characters in the constant
    Node retNode = Word::reverse(x);
    return returnRewrite(node, retNode, Rewrite::STR_CONV_CONST);
  }
  else if (x.getKind() == Kind::STRING_CONCAT)
  {
    std::vector<Node> children;
    for (const Node& nc : x)
    {
      children.push_back(nm->mkNode(Kind::STRING_REV, nc));
    }
    std::reverse(children.begin(), children.end());
    // rev( x1 ++ x2 ) --> rev( x2 ) ++ rev( x1 )
    Node retNode = nm->mkNode(Kind::STRING_CONCAT, children);
    return returnRewrite(node, retNode, Rewrite::STR_REV_MINSCOPE_CONCAT);
  }
  else if (x.getKind() == Kind::STRING_REV)
  {
    // rev( rev( x ) ) --> x
    Node retNode = x[0];
    return returnRewrite(node, retNode, Rewrite::STR_REV_IDEM);
  }
  else if (x.getKind() == Kind::STRING_UNIT || x.getKind() == Kind::SEQ_UNIT)
  {
    // rev( str.unit( x ) ) --> str.unit( x )
    return returnRewrite(node, x, Rewrite::STR_REV_UNIT);
  }
  return node;
}

Node SequencesRewriter::rewritePrefixSuffix(Node n)
{
  Assert(n.getKind() == Kind::STRING_PREFIX
         || n.getKind() == Kind::STRING_SUFFIX);
  bool isPrefix = n.getKind() == Kind::STRING_PREFIX;
  if (n[0] == n[1])
  {
    Node ret = nodeManager()->mkConst(true);
    return returnRewrite(n, ret, Rewrite::SUF_PREFIX_EQ);
  }
  if (n[0].isConst())
  {
    if (Word::isEmpty(n[0]))
    {
      Node ret = nodeManager()->mkConst(true);
      return returnRewrite(n, ret, Rewrite::SUF_PREFIX_EMPTY_CONST);
    }
  }
  if (n[1].isConst())
  {
    Node s = n[1];
    size_t lenS = Word::getLength(s);
    if (n[0].isConst())
    {
      Node ret = nodeManager()->mkConst(false);
      Node t = n[0];
      size_t lenT = Word::getLength(t);
      if (lenS >= lenT)
      {
        if ((isPrefix && t == Word::prefix(s, lenT))
            || (!isPrefix && t == Word::suffix(s, lenT)))
        {
          ret = nodeManager()->mkConst(true);
        }
      }
      return returnRewrite(n, ret, Rewrite::SUF_PREFIX_CONST);
    }
    else if (lenS == 0)
    {
      Node ret = n[0].eqNode(n[1]);
      return returnRewrite(n, ret, Rewrite::SUF_PREFIX_EMPTY);
    }
    else if (lenS == 1)
    {
      // (str.prefix x "A") and (str.suffix x "A") are equivalent to
      // (str.contains "A" x )
      Node ret = nodeManager()->mkNode(Kind::STRING_CONTAINS, n[1], n[0]);
      return returnRewrite(n, ret, Rewrite::SUF_PREFIX_CTN);
    }
  }
  Node lens = nodeManager()->mkNode(Kind::STRING_LENGTH, n[0]);
  Node lent = nodeManager()->mkNode(Kind::STRING_LENGTH, n[1]);

  // Check if we can turn the prefix/suffix into an equality by showing that the
  // prefix/suffix is at least as long as the string
  if (d_arithEntail.check(lens, lent))
  {
    Node retNode = n[0].eqNode(n[1]);
    return returnRewrite(n, retNode, Rewrite::SUF_PREFIX_TO_EQS);
  }

  Node val;
  if (isPrefix)
  {
    val = nodeManager()->mkConstInt(cvc5::internal::Rational(0));
  }
  else
  {
    val = nodeManager()->mkNode(Kind::SUB, lent, lens);
  }

  // general reduction to equality + substr
  Node retNode =
      n[0].eqNode(nodeManager()->mkNode(Kind::STRING_SUBSTR, n[1], val, lens));

  return returnRewrite(n, retNode, Rewrite::SUF_PREFIX_ELIM);
}

Node SequencesRewriter::lengthPreserveRewrite(Node n)
{
  NodeManager* nm = nodeManager();
  Node len =
      d_arithEntail.rewriteLengthIntro(nm->mkNode(Kind::STRING_LENGTH, n));
  len = d_arithEntail.rewriteArith(len);
  Node res = canonicalStrForSymbolicLength(len, n.getType());
  return res.isNull() ? n : res;
}

Node SequencesRewriter::canonicalStrForSymbolicLength(Node len,
                                                      TypeNode stype) const
{
  NodeManager* nm = nodeManager();

  Node res;
  if (len.isConst())
  {
    // c -> "A" repeated c times
    Rational ratLen = len.getConst<Rational>();
    Assert(ratLen.getDenominator() == 1);
    Integer intLen = ratLen.getNumerator();
    uint32_t u = intLen.getUnsignedInt();
    if (stype.isString())  // string-only
    {
      res = nm->mkConst(String(std::string(u, 'A')));
    }
    // we could do this for sequences, but we need to be careful: some
    // sorts do not permit values that the solver can handle (e.g. uninterpreted
    // sorts and arrays).
  }
  else if (len.getKind() == Kind::ADD)
  {
    // x + y -> norm(x) + norm(y)
    NodeBuilder concatBuilder(nodeManager(), Kind::STRING_CONCAT);
    for (const auto& n : len)
    {
      Node sn = canonicalStrForSymbolicLength(n, stype);
      if (sn.isNull())
      {
        return Node::null();
      }
      std::vector<Node> snChildren;
      utils::getConcat(sn, snChildren);
      concatBuilder.append(snChildren);
    }
    res = concatBuilder.constructNode();
  }
  else if (len.getKind() == Kind::MULT && len.getNumChildren() == 2
           && len[0].isConst())
  {
    // c * x -> norm(x) repeated c times
    Rational ratReps = len[0].getConst<Rational>();
    Assert(ratReps.getDenominator() == 1);
    Integer intReps = ratReps.getNumerator();

    Node nRep = canonicalStrForSymbolicLength(len[1], stype);
    if (nRep.isNull())
    {
      return Node::null();
    }
    std::vector<Node> nRepChildren;
    utils::getConcat(nRep, nRepChildren);
    NodeBuilder concatBuilder(nodeManager(), Kind::STRING_CONCAT);
    for (size_t i = 0, reps = intReps.getUnsignedInt(); i < reps; i++)
    {
      concatBuilder.append(nRepChildren);
    }
    res = concatBuilder.constructNode();
  }
  else if (len.getKind() == Kind::STRING_LENGTH)
  {
    // len(x) -> x
    res = len[0];
  }
  return res;
}

Node SequencesRewriter::rewriteSeqUnit(Node node)
{
  Assert(node.getKind() == Kind::SEQ_UNIT);
  NodeManager* nm = nodeManager();
  if (node[0].isConst())
  {
    std::vector<Node> seq;
    seq.push_back(node[0]);
    // important to take the type according to the operator here, not the
    // type of the argument
    TypeNode stype = node.getType().getSequenceElementType();
    Node ret = nm->mkConst(Sequence(stype, seq));
    return returnRewrite(node, ret, Rewrite::SEQ_UNIT_EVAL);
  }
  return node;
}

Node SequencesRewriter::returnRewrite(Node node, Node ret, Rewrite r)
{
  Trace("strings-rewrite") << "Rewrite " << node << " to " << ret << " by " << r
                           << "." << std::endl;
  if (d_statistics != nullptr)
  {
    (*d_statistics) << r;
  }
  return ret;
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal
