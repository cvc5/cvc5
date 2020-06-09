/*********************                                                        */
/*! \file evaluator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The Evaluator class
 **
 ** The Evaluator class.
 **/

#include "theory/evaluator.h"

#include "theory/bv/theory_bv_utils.h"
#include "theory/rewriter.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/theory.h"
#include "util/integer.h"

namespace CVC4 {
namespace theory {

EvalResult::EvalResult(const EvalResult& other)
{
  d_tag = other.d_tag;
  switch (d_tag)
  {
    case BOOL: d_bool = other.d_bool; break;
    case BITVECTOR:
      new (&d_bv) BitVector;
      d_bv = other.d_bv;
      break;
    case RATIONAL:
      new (&d_rat) Rational;
      d_rat = other.d_rat;
      break;
    case STRING:
      new (&d_str) String;
      d_str = other.d_str;
      break;
    case INVALID: break;
  }
}

EvalResult& EvalResult::operator=(const EvalResult& other)
{
  if (this != &other)
  {
    d_tag = other.d_tag;
    switch (d_tag)
    {
      case BOOL: d_bool = other.d_bool; break;
      case BITVECTOR:
        new (&d_bv) BitVector;
        d_bv = other.d_bv;
        break;
      case RATIONAL:
        new (&d_rat) Rational;
        d_rat = other.d_rat;
        break;
      case STRING:
        new (&d_str) String;
        d_str = other.d_str;
        break;
      case INVALID: break;
    }
  }
  return *this;
}

EvalResult::~EvalResult()
{
  switch (d_tag)
  {
    case BITVECTOR:
    {
      d_bv.~BitVector();
      break;
    }
    case RATIONAL:
    {
      d_rat.~Rational();
      break;
    }
    case STRING:
    {
      d_str.~String();
      break;

      default: break;
    }
  }
}

Node EvalResult::toNode() const
{
  NodeManager* nm = NodeManager::currentNM();
  switch (d_tag)
  {
    case EvalResult::BOOL: return nm->mkConst(d_bool);
    case EvalResult::BITVECTOR: return nm->mkConst(d_bv);
    case EvalResult::RATIONAL: return nm->mkConst(d_rat);
    case EvalResult::STRING: return nm->mkConst(d_str);
    default:
    {
      Trace("evaluator") << "Missing conversion from " << d_tag << " to node"
                         << std::endl;
      return Node();
    }
  }
}

Node Evaluator::eval(TNode n,
                     const std::vector<Node>& args,
                     const std::vector<Node>& vals) const
{
  std::unordered_map<Node, Node, NodeHashFunction> visited;
  return eval(n, args, vals, visited);
}
Node Evaluator::eval(
    TNode n,
    const std::vector<Node>& args,
    const std::vector<Node>& vals,
    const std::unordered_map<Node, Node, NodeHashFunction>& visited) const
{
  Trace("evaluator") << "Evaluating " << n << " under substitution " << args
                     << " " << vals << " with visited size = " << visited.size()
                     << std::endl;
  std::unordered_map<TNode, Node, NodeHashFunction> evalAsNode;
  std::unordered_map<TNode, EvalResult, TNodeHashFunction> results;
  // add visited to results
  for (const std::pair<const Node, Node>& p : visited)
  {
    Trace("evaluator") << "Add " << p.first << " == " << p.second << std::endl;
    results[p.first] = evalInternal(p.second, args, vals, evalAsNode, results);
    if (results[p.first].d_tag == EvalResult::INVALID)
    {
      // could not evaluate, use the evalAsNode map
      evalAsNode[p.first] = evalAsNode[p.second];
    }
  }
  Trace("evaluator") << "Run eval internal..." << std::endl;
  Node ret = evalInternal(n, args, vals, evalAsNode, results).toNode();
  // if we failed to evaluate
  if (ret.isNull())
  {
    // should be stored in the evaluation-as-node map
    std::unordered_map<TNode, Node, NodeHashFunction>::iterator itn =
        evalAsNode.find(n);
    Assert(itn != evalAsNode.end());
    ret = itn->second;
  }
  // should be the same as substitution + rewriting
  Assert(ret
         == Rewriter::rewrite(
             n.substitute(args.begin(), args.end(), vals.begin(), vals.end())));
  return ret;
}

EvalResult Evaluator::evalInternal(
    TNode n,
    const std::vector<Node>& args,
    const std::vector<Node>& vals,
    std::unordered_map<TNode, Node, NodeHashFunction>& evalAsNode,
    std::unordered_map<TNode, EvalResult, TNodeHashFunction>& results) const
{
  std::vector<TNode> queue;
  queue.emplace_back(n);
  std::unordered_map<TNode, EvalResult, TNodeHashFunction>::iterator itr;

  while (queue.size() != 0)
  {
    TNode currNode = queue.back();

    if (results.find(currNode) != results.end())
    {
      queue.pop_back();
      continue;
    }

    bool doProcess = true;
    bool doEval = true;
    if (currNode.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      TNode op = currNode.getOperator();
      // Certain nodes are parameterized with constant operators, including
      // bitvector extract. These operators do not need to be evaluated.
      if (!op.isConst())
      {
        itr = results.find(op);
        if (itr == results.end())
        {
          queue.emplace_back(op);
          doProcess = false;
        }
        else if (itr->second.d_tag == EvalResult::INVALID)
        {
          doEval = false;
        }
      }
    }
    for (const auto& currNodeChild : currNode)
    {
      itr = results.find(currNodeChild);
      if (itr == results.end())
      {
        queue.emplace_back(currNodeChild);
        doProcess = false;
      }
      else if (itr->second.d_tag == EvalResult::INVALID)
      {
        // we cannot evaluate since there was an invalid child
        doEval = false;
      }
    }
    Trace("evaluator") << "Evaluator: visit " << currNode
                       << ", process = " << doProcess
                       << ", evaluate = " << doEval << std::endl;

    if (doProcess)
    {
      queue.pop_back();

      Node currNodeVal = currNode;
      // whether we need to reconstruct the current node in the case of failure
      bool needsReconstruct = true;

      // The code below should either:
      // (1) store a valid EvalResult into results[currNode], or
      // (2) store an invalid EvalResult into results[currNode] and
      // store the result of substitution + rewriting currNode { args -> vals }
      // into evalAsNode[currNode].

      // If we did not successfully evaluate all children
      if (!doEval)
      {
        // Reconstruct the node with a combination of the children that
        // successfully evaluated, and the children that did not.
        Trace("evaluator") << "Evaluator: collect arguments" << std::endl;
        currNodeVal = reconstruct(currNodeVal, results, evalAsNode);
        needsReconstruct = false;
        Trace("evaluator") << "Evaluator: now after substitution + rewriting: "
                           << currNodeVal << std::endl;
        if (currNodeVal.getNumChildren() > 0)
        {
          // We may continue with a valid EvalResult at this point only if
          // we have no children. We must otherwise fail here since some of
          // our children may not have successful evaluations.
          results[currNode] = EvalResult();
          evalAsNode[currNode] = currNodeVal;
          continue;
        }
        // Otherwise, we may be able to turn the overall result into an
        // valid EvalResult and continue. We fallthrough and continue with the
        // block of code below.
      }

      if (currNode.isVar())
      {
        const auto& it = std::find(args.begin(), args.end(), currNode);
        if (it == args.end())
        {
          // variable with no substitution is itself
          evalAsNode[currNode] = currNode;
          results[currNode] = EvalResult();
          continue;
        }
        ptrdiff_t pos = std::distance(args.begin(), it);
        currNodeVal = vals[pos];
        // Don't need to reconstruct since range of substitution should already
        // be normalized.
        Assert(vals[pos] == Rewriter::rewrite(vals[pos]));
        needsReconstruct = false;
      }
      else if (currNode.getKind() == kind::APPLY_UF)
      {
        Trace("evaluator") << "Evaluate " << currNode << std::endl;
        TNode op = currNode.getOperator();
        Assert(evalAsNode.find(op) != evalAsNode.end());
        // no function can be a valid EvalResult
        op = evalAsNode[op];
        Trace("evaluator") << "Operator evaluated to " << op << std::endl;
        if (op.getKind() != kind::LAMBDA)
        {
          // this node is not evaluatable due to operator, must add to
          // evalAsNode
          results[currNode] = EvalResult();
          evalAsNode[currNode] = reconstruct(currNode, results, evalAsNode);
          continue;
        }
        // Create a copy of the current substitutions
        std::vector<Node> lambdaArgs(args);
        std::vector<Node> lambdaVals(vals);

        // Add the values for the arguments of the lambda as substitutions at
        // the beginning of the vector to shadow variables from outer scopes
        // with the same name
        for (const auto& lambdaArg : op[0])
        {
          lambdaArgs.insert(lambdaArgs.begin(), lambdaArg);
        }

        for (const auto& lambdaVal : currNode)
        {
          lambdaVals.insert(lambdaVals.begin(), results[lambdaVal].toNode());
        }

        // Lambdas are evaluated in a recursive fashion because each evaluation
        // requires different substitutions. We use a fresh cache since the
        // evaluation of op[1] is under a new substitution and thus should not
        // be cached. We could alternatively copy evalAsNode to evalAsNodeC but
        // favor avoiding this copy for performance reasons.
        std::unordered_map<TNode, Node, NodeHashFunction> evalAsNodeC;
        std::unordered_map<TNode, EvalResult, TNodeHashFunction> resultsC;
        results[currNode] =
            evalInternal(op[1], lambdaArgs, lambdaVals, evalAsNodeC, resultsC);
        Trace("evaluator") << "Evaluated via arguments to "
                           << results[currNode].d_tag << std::endl;
        if (results[currNode].d_tag == EvalResult::INVALID)
        {
          // evaluation was invalid, we take the node of op[1] as the result
          evalAsNode[currNode] = evalAsNodeC[op[1]];
          Trace("evaluator")
              << "Take node evaluation: " << evalAsNodeC[op[1]] << std::endl;
        }
        continue;
      }

      switch (currNodeVal.getKind())
      {
        case kind::CONST_BOOLEAN:
          results[currNode] = EvalResult(currNodeVal.getConst<bool>());
          break;

        case kind::NOT:
        {
          results[currNode] = EvalResult(!(results[currNode[0]].d_bool));
          break;
        }

        case kind::AND:
        {
          bool res = results[currNode[0]].d_bool;
          for (size_t i = 1, end = currNode.getNumChildren(); i < end; i++)
          {
            res = res && results[currNode[i]].d_bool;
          }
          results[currNode] = EvalResult(res);
          break;
        }

        case kind::OR:
        {
          bool res = results[currNode[0]].d_bool;
          for (size_t i = 1, end = currNode.getNumChildren(); i < end; i++)
          {
            res = res || results[currNode[i]].d_bool;
          }
          results[currNode] = EvalResult(res);
          break;
        }

        case kind::CONST_RATIONAL:
        {
          const Rational& r = currNodeVal.getConst<Rational>();
          results[currNode] = EvalResult(r);
          break;
        }

        case kind::PLUS:
        {
          Rational res = results[currNode[0]].d_rat;
          for (size_t i = 1, end = currNode.getNumChildren(); i < end; i++)
          {
            res = res + results[currNode[i]].d_rat;
          }
          results[currNode] = EvalResult(res);
          break;
        }

        case kind::MINUS:
        {
          const Rational& x = results[currNode[0]].d_rat;
          const Rational& y = results[currNode[1]].d_rat;
          results[currNode] = EvalResult(x - y);
          break;
        }

        case kind::UMINUS:
        {
          const Rational& x = results[currNode[0]].d_rat;
          results[currNode] = EvalResult(-x);
          break;
        }
        case kind::MULT:
        case kind::NONLINEAR_MULT:
        {
          Rational res = results[currNode[0]].d_rat;
          for (size_t i = 1, end = currNode.getNumChildren(); i < end; i++)
          {
            res = res * results[currNode[i]].d_rat;
          }
          results[currNode] = EvalResult(res);
          break;
        }

        case kind::GEQ:
        {
          const Rational& x = results[currNode[0]].d_rat;
          const Rational& y = results[currNode[1]].d_rat;
          results[currNode] = EvalResult(x >= y);
          break;
        }
        case kind::LEQ:
        {
          const Rational& x = results[currNode[0]].d_rat;
          const Rational& y = results[currNode[1]].d_rat;
          results[currNode] = EvalResult(x <= y);
          break;
        }
        case kind::GT:
        {
          const Rational& x = results[currNode[0]].d_rat;
          const Rational& y = results[currNode[1]].d_rat;
          results[currNode] = EvalResult(x > y);
          break;
        }
        case kind::LT:
        {
          const Rational& x = results[currNode[0]].d_rat;
          const Rational& y = results[currNode[1]].d_rat;
          results[currNode] = EvalResult(x < y);
          break;
        }
        case kind::ABS:
        {
          const Rational& x = results[currNode[0]].d_rat;
          results[currNode] = EvalResult(x.abs());
          break;
        }
        case kind::CONST_STRING:
          results[currNode] = EvalResult(currNodeVal.getConst<String>());
          break;

        case kind::STRING_CONCAT:
        {
          String res = results[currNode[0]].d_str;
          for (size_t i = 1, end = currNode.getNumChildren(); i < end; i++)
          {
            res = res.concat(results[currNode[i]].d_str);
          }
          results[currNode] = EvalResult(res);
          break;
        }

        case kind::STRING_LENGTH:
        {
          const String& s = results[currNode[0]].d_str;
          results[currNode] = EvalResult(Rational(s.size()));
          break;
        }

        case kind::STRING_SUBSTR:
        {
          const String& s = results[currNode[0]].d_str;
          Integer s_len(s.size());
          Integer i = results[currNode[1]].d_rat.getNumerator();
          Integer j = results[currNode[2]].d_rat.getNumerator();

          if (i.strictlyNegative() || j.strictlyNegative() || i >= s_len)
          {
            results[currNode] = EvalResult(String(""));
          }
          else if (i + j > s_len)
          {
            results[currNode] =
                EvalResult(s.suffix((s_len - i).toUnsignedInt()));
          }
          else
          {
            results[currNode] =
                EvalResult(s.substr(i.toUnsignedInt(), j.toUnsignedInt()));
          }
          break;
        }

        case kind::STRING_CHARAT:
        {
          const String& s = results[currNode[0]].d_str;
          Integer s_len(s.size());
          Integer i = results[currNode[1]].d_rat.getNumerator();
          if (i.strictlyNegative() || i >= s_len)
          {
            results[currNode] = EvalResult(String(""));
          }
          else
          {
            results[currNode] = EvalResult(s.substr(i.toUnsignedInt(), 1));
          }
          break;
        }

        case kind::STRING_STRCTN:
        {
          const String& s = results[currNode[0]].d_str;
          const String& t = results[currNode[1]].d_str;
          results[currNode] = EvalResult(s.find(t) != std::string::npos);
          break;
        }

        case kind::STRING_STRIDOF:
        {
          const String& s = results[currNode[0]].d_str;
          Integer s_len(s.size());
          const String& x = results[currNode[1]].d_str;
          Integer i = results[currNode[2]].d_rat.getNumerator();

          if (i.strictlyNegative())
          {
            results[currNode] = EvalResult(Rational(-1));
          }
          else
          {
            size_t r = s.find(x, i.toUnsignedInt());
            if (r == std::string::npos)
            {
              results[currNode] = EvalResult(Rational(-1));
            }
            else
            {
              results[currNode] = EvalResult(Rational(r));
            }
          }
          break;
        }

        case kind::STRING_STRREPL:
        {
          const String& s = results[currNode[0]].d_str;
          const String& x = results[currNode[1]].d_str;
          const String& y = results[currNode[2]].d_str;
          results[currNode] = EvalResult(s.replace(x, y));
          break;
        }

        case kind::STRING_PREFIX:
        {
          const String& t = results[currNode[0]].d_str;
          const String& s = results[currNode[1]].d_str;
          if (s.size() < t.size())
          {
            results[currNode] = EvalResult(false);
          }
          else
          {
            results[currNode] = EvalResult(s.prefix(t.size()) == t);
          }
          break;
        }

        case kind::STRING_SUFFIX:
        {
          const String& t = results[currNode[0]].d_str;
          const String& s = results[currNode[1]].d_str;
          if (s.size() < t.size())
          {
            results[currNode] = EvalResult(false);
          }
          else
          {
            results[currNode] = EvalResult(s.suffix(t.size()) == t);
          }
          break;
        }

        case kind::STRING_ITOS:
        {
          Integer i = results[currNode[0]].d_rat.getNumerator();
          if (i.strictlyNegative())
          {
            results[currNode] = EvalResult(String(""));
          }
          else
          {
            results[currNode] = EvalResult(String(i.toString()));
          }
          break;
        }

        case kind::STRING_STOI:
        {
          const String& s = results[currNode[0]].d_str;
          if (s.isNumber())
          {
            results[currNode] = EvalResult(Rational(s.toNumber()));
          }
          else
          {
            results[currNode] = EvalResult(Rational(-1));
          }
          break;
        }

        case kind::STRING_FROM_CODE:
        {
          Integer i = results[currNode[0]].d_rat.getNumerator();
          if (i >= 0 && i < strings::utils::getAlphabetCardinality())
          {
            std::vector<unsigned> svec = {i.toUnsignedInt()};
            results[currNode] = EvalResult(String(svec));
          }
          else
          {
            results[currNode] = EvalResult(String(""));
          }
          break;
        }

        case kind::STRING_TO_CODE:
        {
          const String& s = results[currNode[0]].d_str;
          if (s.size() == 1)
          {
            results[currNode] = EvalResult(Rational(s.getVec()[0]));
          }
          else
          {
            results[currNode] = EvalResult(Rational(-1));
          }
          break;
        }

        case kind::CONST_BITVECTOR:
          results[currNode] = EvalResult(currNodeVal.getConst<BitVector>());
          break;

        case kind::BITVECTOR_NOT:
          results[currNode] = EvalResult(~results[currNode[0]].d_bv);
          break;

        case kind::BITVECTOR_NEG:
          results[currNode] = EvalResult(-results[currNode[0]].d_bv);
          break;

        case kind::BITVECTOR_EXTRACT:
        {
          unsigned lo = bv::utils::getExtractLow(currNodeVal);
          unsigned hi = bv::utils::getExtractHigh(currNodeVal);
          results[currNode] =
              EvalResult(results[currNode[0]].d_bv.extract(hi, lo));
          break;
        }

        case kind::BITVECTOR_CONCAT:
        {
          BitVector res = results[currNode[0]].d_bv;
          for (size_t i = 1, end = currNode.getNumChildren(); i < end; i++)
          {
            res = res.concat(results[currNode[i]].d_bv);
          }
          results[currNode] = EvalResult(res);
          break;
        }

        case kind::BITVECTOR_PLUS:
        {
          BitVector res = results[currNode[0]].d_bv;
          for (size_t i = 1, end = currNode.getNumChildren(); i < end; i++)
          {
            res = res + results[currNode[i]].d_bv;
          }
          results[currNode] = EvalResult(res);
          break;
        }

        case kind::BITVECTOR_MULT:
        {
          BitVector res = results[currNode[0]].d_bv;
          for (size_t i = 1, end = currNode.getNumChildren(); i < end; i++)
          {
            res = res * results[currNode[i]].d_bv;
          }
          results[currNode] = EvalResult(res);
          break;
        }
        case kind::BITVECTOR_AND:
        {
          BitVector res = results[currNode[0]].d_bv;
          for (size_t i = 1, end = currNode.getNumChildren(); i < end; i++)
          {
            res = res & results[currNode[i]].d_bv;
          }
          results[currNode] = EvalResult(res);
          break;
        }

        case kind::BITVECTOR_OR:
        {
          BitVector res = results[currNode[0]].d_bv;
          for (size_t i = 1, end = currNode.getNumChildren(); i < end; i++)
          {
            res = res | results[currNode[i]].d_bv;
          }
          results[currNode] = EvalResult(res);
          break;
        }

        case kind::BITVECTOR_XOR:
        {
          BitVector res = results[currNode[0]].d_bv;
          for (size_t i = 1, end = currNode.getNumChildren(); i < end; i++)
          {
            res = res ^ results[currNode[i]].d_bv;
          }
          results[currNode] = EvalResult(res);
          break;
        }
        case kind::BITVECTOR_UDIV:
        case kind::BITVECTOR_UDIV_TOTAL:
        {
          if (currNodeVal.getKind() == kind::BITVECTOR_UDIV_TOTAL
              || results[currNode[1]].d_bv.getValue() != 0)
          {
            BitVector res = results[currNode[0]].d_bv;
            res = res.unsignedDivTotal(results[currNode[1]].d_bv);
            results[currNode] = EvalResult(res);
          }
          else
          {
            results[currNode] = EvalResult();
            evalAsNode[currNode] =
                needsReconstruct ? reconstruct(currNode, results, evalAsNode)
                                 : currNodeVal;
          }
          break;
        }
        case kind::BITVECTOR_UREM:
        case kind::BITVECTOR_UREM_TOTAL:
        {
          if (currNodeVal.getKind() == kind::BITVECTOR_UREM_TOTAL
              || results[currNode[1]].d_bv.getValue() != 0)
          {
            BitVector res = results[currNode[0]].d_bv;
            res = res.unsignedRemTotal(results[currNode[1]].d_bv);
            results[currNode] = EvalResult(res);
          }
          else
          {
            results[currNode] = EvalResult();
            evalAsNode[currNode] =
                needsReconstruct ? reconstruct(currNode, results, evalAsNode)
                                 : currNodeVal;
          }
          break;
        }

        case kind::EQUAL:
        {
          EvalResult lhs = results[currNode[0]];
          EvalResult rhs = results[currNode[1]];

          switch (lhs.d_tag)
          {
            case EvalResult::BOOL:
            {
              results[currNode] = EvalResult(lhs.d_bool == rhs.d_bool);
              break;
            }

            case EvalResult::BITVECTOR:
            {
              results[currNode] = EvalResult(lhs.d_bv == rhs.d_bv);
              break;
            }

            case EvalResult::RATIONAL:
            {
              results[currNode] = EvalResult(lhs.d_rat == rhs.d_rat);
              break;
            }

            case EvalResult::STRING:
            {
              results[currNode] = EvalResult(lhs.d_str == rhs.d_str);
              break;
            }

            default:
            {
              Trace("evaluator") << "Theory " << Theory::theoryOf(currNode[0])
                                 << " not supported" << std::endl;
              results[currNode] = EvalResult();
              evalAsNode[currNode] =
                  needsReconstruct ? reconstruct(currNode, results, evalAsNode)
                                   : currNodeVal;
              break;
            }
          }

          break;
        }

        case kind::ITE:
        {
          if (results[currNode[0]].d_bool)
          {
            results[currNode] = results[currNode[1]];
          }
          else
          {
            results[currNode] = results[currNode[2]];
          }
          break;
        }

        default:
        {
          Trace("evaluator") << "Kind " << currNodeVal.getKind()
                             << " not supported" << std::endl;
          results[currNode] = EvalResult();
          evalAsNode[currNode] =
              needsReconstruct ? reconstruct(currNode, results, evalAsNode)
                               : currNodeVal;
        }
      }
    }
  }

  return results[n];
}

Node Evaluator::reconstruct(
    TNode n,
    std::unordered_map<TNode, EvalResult, TNodeHashFunction>& eresults,
    std::unordered_map<TNode, Node, NodeHashFunction>& evalAsNode) const
{
  if (n.getNumChildren() == 0)
  {
    return n;
  }
  Trace("evaluator") << "Evaluator: reconstruct " << n << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<TNode, EvalResult, TNodeHashFunction>::iterator itr;
  std::unordered_map<TNode, Node, NodeHashFunction>::iterator itn;
  std::vector<Node> echildren;
  if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    TNode op = n.getOperator();
    if (op.isConst())
    {
      echildren.push_back(op);
    }
    else
    {
      itr = eresults.find(op);
      Assert(itr != eresults.end());
      if (itr->second.d_tag == EvalResult::INVALID)
      {
        // could not evaluate the operator, look in the node cache
        itn = evalAsNode.find(op);
        Assert(itn != evalAsNode.end());
        echildren.push_back(itn->second);
      }
      else
      {
        // otherwise, use the evaluation of the operator
        echildren.push_back(itr->second.toNode());
      }
    }
  }
  for (const auto& currNodeChild : n)
  {
    itr = eresults.find(currNodeChild);
    Assert(itr != eresults.end());
    if (itr->second.d_tag == EvalResult::INVALID)
    {
      // could not evaluate this child, look in the node cache
      itn = evalAsNode.find(currNodeChild);
      Assert(itn != evalAsNode.end());
      echildren.push_back(itn->second);
    }
    else
    {
      // otherwise, use the evaluation
      echildren.push_back(itr->second.toNode());
    }
  }
  // The value is the result of our (partially) successful evaluation
  // of the children.
  Node nn = nm->mkNode(n.getKind(), echildren);
  Trace("evaluator") << "Evaluator: reconstructed " << nn << std::endl;
  // Use rewriting. Notice we do not need to substitute here since
  // all substitutions should already have been applied recursively.
  return Rewriter::rewrite(nn);
}

}  // namespace theory
}  // namespace CVC4
