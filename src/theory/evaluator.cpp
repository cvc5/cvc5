/*********************                                                        */
/*! \file evaluator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
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
    case ROUNDINGMODE:
      new (&d_rm) RoundingMode;
      d_rm = other.d_rm;
      break;
    case FLOATINGPOINT: new (&d_fp) FloatingPoint(other.d_fp); break;
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
      case ROUNDINGMODE:
        new (&d_rm) RoundingMode;
        d_rm = other.d_rm;
        break;
      case FLOATINGPOINT: new (&d_fp) FloatingPoint(other.d_fp); break;
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
    case ROUNDINGMODE:
    {
      d_rm.~RoundingMode();
      break;
    }
    case FLOATINGPOINT:
    {
      d_fp.~FloatingPoint();
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
    }

    default: break;
  }
}

Node EvalResult::toNode() const
{
  NodeManager* nm = NodeManager::currentNM();
  switch (d_tag)
  {
    case EvalResult::BOOL: return nm->mkConst(d_bool);
    case EvalResult::BITVECTOR: return nm->mkConst(d_bv);
    case EvalResult::ROUNDINGMODE: return nm->mkConst(d_rm);
    case EvalResult::FLOATINGPOINT: return nm->mkConst(d_fp);
    case EvalResult::RATIONAL: return nm->mkConst(d_rat);
    case EvalResult::STRING: return nm->mkConst(d_str);
    default:
    {
      Trace("evaluator") << "Missing conversion from " << d_tag << " to node"
                         << std::endl;
      return Node();
    }
  }

  return Node();
}

Node Evaluator::eval(TNode n,
                     const std::vector<Node>& args,
                     const std::vector<Node>& vals)
{
  Trace("evaluator") << "Evaluating " << n << " under substitution " << args
                     << " " << vals << std::endl;
  Node res = n.isConst() ? Node(n) : evalInternal(n, args, vals).toNode();
  Assert(res.isNull()
         || res
                == Rewriter::rewrite(n.substitute(
                       args.begin(), args.end(), vals.begin(), vals.end())));
  return res;
}

EvalResult Evaluator::evalInternal(TNode n,
                                   const std::vector<Node>& args,
                                   const std::vector<Node>& vals)
{
  std::unordered_map<TNode, EvalResult, TNodeHashFunction> results;
  std::vector<TNode> queue;
  queue.emplace_back(n);

  while (queue.size() != 0)
  {
    TNode currNode = queue.back();

    if (results.find(currNode) != results.end())
    {
      queue.pop_back();
      continue;
    }

    bool doEval = true;
    for (const auto& currNodeChild : currNode)
    {
      if (results.find(currNodeChild) == results.end())
      {
        queue.emplace_back(currNodeChild);
        doEval = false;
      }
    }

    if (doEval)
    {
      queue.pop_back();

      Node currNodeVal = currNode;
      if (currNode.isVar())
      {
        const auto& it = std::find(args.begin(), args.end(), currNode);

        if (it == args.end())
        {
          return EvalResult();
        }

        ptrdiff_t pos = std::distance(args.begin(), it);
        currNodeVal = vals[pos];
      }
      else if (currNode.getKind() == kind::APPLY_UF
               && currNode.getOperator().getKind() == kind::LAMBDA)
      {
        // Create a copy of the current substitutions
        std::vector<Node> lambdaArgs(args);
        std::vector<Node> lambdaVals(vals);

        // Add the values for the arguments of the lambda as substitutions at
        // the beginning of the vector to shadow variables from outer scopes
        // with the same name
        Node op = currNode.getOperator();
        for (const auto& lambdaArg : op[0])
        {
          lambdaArgs.insert(lambdaArgs.begin(), lambdaArg);
        }

        for (const auto& lambdaVal : currNode)
        {
          lambdaVals.insert(lambdaVals.begin(), results[lambdaVal].toNode());
        }

        // Lambdas are evaluated in a recursive fashion because each evaluation
        // requires different substitutions
        results[currNode] = evalInternal(op[1], lambdaArgs, lambdaVals);
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

        case kind::MULT:
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

          if (i.strictlyNegative() || i >= s_len)
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
            results[currNode] = EvalResult(Rational(-1));
          }
          else
          {
            results[currNode] = EvalResult(Rational(s.toNumber()));
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

        case kind::CONST_FLOATINGPOINT:
        {
          results[currNode] = EvalResult(currNodeVal.getConst<FloatingPoint>());
          break;
        }

        case kind::CONST_ROUNDINGMODE:
        {
          results[currNode] = EvalResult(currNodeVal.getConst<RoundingMode>());
          break;
        }

        case kind::FLOATINGPOINT_FP:
        {
          const BitVector& sign = results[currNode[0]].d_bv;
          const BitVector& exp = results[currNode[1]].d_bv;
          const BitVector& sig = results[currNode[2]].d_bv;
          Assert(sign.getSize() == 1);
          unsigned e = exp.getSize();
          unsigned s = sig.getSize() + 1;
          results[currNode] =
              EvalResult(FloatingPoint(e, s, sign.concat(exp.concat(sig))));
          break;
        }

        case kind::FLOATINGPOINT_EQ:
        case kind::FLOATINGPOINT_GEQ:
        case kind::FLOATINGPOINT_GT:
        {
          // These kinds should have been removed by earlier rewrites. In
          // debug, we would like to know about this. In production, we can
          // just return an invalid result and fall back to the full rewriter.
          Assert(false);
          return EvalResult();
        }

        case kind::FLOATINGPOINT_ABS:
        {
          const FloatingPoint& val = results[currNode[0]].d_fp;
          results[currNode] = EvalResult(val.absolute());
          break;
        }

        case kind::FLOATINGPOINT_NEG:
        {
          results[currNode] = EvalResult(results[currNode[0]].d_fp.negate());
          break;
        }

        case kind::FLOATINGPOINT_PLUS:
        {
          const RoundingMode& rm = results[currNode[0]].d_rm;
          const FloatingPoint& lhs = results[currNode[1]].d_fp;
          const FloatingPoint& rhs = results[currNode[2]].d_fp;
          results[currNode] = EvalResult(lhs.plus(rm, rhs));
          break;
        }

        case kind::FLOATINGPOINT_SUB:
        {
          const RoundingMode& rm = results[currNode[0]].d_rm;
          const FloatingPoint& lhs = results[currNode[1]].d_fp;
          const FloatingPoint& rhs = results[currNode[2]].d_fp;
          results[currNode] = EvalResult(lhs.sub(rm, rhs));
          break;
        }

        case kind::FLOATINGPOINT_MULT:
        {
          const RoundingMode& rm = results[currNode[0]].d_rm;
          const FloatingPoint& lhs = results[currNode[1]].d_fp;
          const FloatingPoint& rhs = results[currNode[2]].d_fp;
          results[currNode] = EvalResult(lhs.mult(rm, rhs));
          break;
        }

        case kind::FLOATINGPOINT_DIV:
        {
          const RoundingMode& rm = results[currNode[0]].d_rm;
          const FloatingPoint& lhs = results[currNode[1]].d_fp;
          const FloatingPoint& rhs = results[currNode[2]].d_fp;
          results[currNode] = EvalResult(lhs.div(rm, rhs));
          break;
        }

        case kind::FLOATINGPOINT_FMA:
        {
          const RoundingMode& rm = results[currNode[0]].d_rm;
          const FloatingPoint& val = results[currNode[1]].d_fp;
          const FloatingPoint& fac = results[currNode[2]].d_fp;
          const FloatingPoint& add = results[currNode[3]].d_fp;
          results[currNode] = EvalResult(val.fma(rm, fac, add));
          break;
        }

        case kind::FLOATINGPOINT_SQRT:
        {
          const RoundingMode& rm = results[currNode[0]].d_rm;
          const FloatingPoint& val = results[currNode[1]].d_fp;
          results[currNode] = EvalResult(val.sqrt(rm));
          break;
        }

        case kind::FLOATINGPOINT_REM:
        {
          const FloatingPoint& lhs = results.at(currNode[0]).d_fp;
          const FloatingPoint& rhs = results.at(currNode[1]).d_fp;
          FloatingPoint res = lhs.rem(rhs);
          results[currNode] = EvalResult(lhs.rem(rhs));
          break;
        }

        case kind::FLOATINGPOINT_RTI:
        {
          const RoundingMode& rm = results[currNode[0]].d_rm;
          const FloatingPoint& val = results[currNode[1]].d_fp;
          results[currNode] = EvalResult(val.rti(rm));
          break;
        }

        case kind::FLOATINGPOINT_MIN:
        {
          const FloatingPoint& lhs = results[currNode[0]].d_fp;
          const FloatingPoint& rhs = results[currNode[1]].d_fp;

          FloatingPoint::PartialFloatingPoint res(lhs.min(rhs));

          if (res.second)
          {
            results[currNode] = EvalResult(res.first);
          }
          else
          {
            // Can't constant fold the underspecified case
            return EvalResult();
          }
          break;
        }

        case kind::FLOATINGPOINT_MAX:
        {
          const FloatingPoint& lhs = results[currNode[0]].d_fp;
          const FloatingPoint& rhs = results[currNode[1]].d_fp;

          FloatingPoint::PartialFloatingPoint res(lhs.max(rhs));

          if (res.second)
          {
            results[currNode] = EvalResult(res.first);
          }
          else
          {
            // Can't constant fold the underspecified case
            return EvalResult();
          }
          break;
        }

        case kind::FLOATINGPOINT_MIN_TOTAL:
        {
          const FloatingPoint& lhs = results[currNode[0]].d_fp;
          const FloatingPoint& rhs = results[currNode[1]].d_fp;
          const BitVector& zeroCaseBv = results[currNode[2]].d_bv;
          Assert(zeroCaseBv.getSize() == 1);
          bool zeroCase = zeroCaseBv.isBitSet(0);
          results[currNode] = EvalResult(lhs.minTotal(rhs, zeroCase));
          break;
        }

        case kind::FLOATINGPOINT_MAX_TOTAL:
        {
          const FloatingPoint& lhs = results[currNode[0]].d_fp;
          const FloatingPoint& rhs = results[currNode[1]].d_fp;
          const BitVector& zeroCaseBv = results[currNode[2]].d_bv;
          Assert(zeroCaseBv.getSize() == 1);
          bool zeroCase = zeroCaseBv.isBitSet(0);
          results[currNode] = EvalResult(lhs.maxTotal(rhs, zeroCase));
          break;
        }

        case kind::FLOATINGPOINT_LT:
        {
          const FloatingPoint& lhs = results[currNode[0]].d_fp;
          const FloatingPoint& rhs = results[currNode[1]].d_fp;
          results[currNode] = EvalResult(lhs < rhs);
          break;
        }

        case kind::FLOATINGPOINT_ISN:
        {
          const FloatingPoint& val = results[currNode[0]].d_fp;
          results[currNode] = EvalResult(val.isNormal());
          break;
        }

        case kind::FLOATINGPOINT_ISSN:
        {
          const FloatingPoint& val = results[currNode[0]].d_fp;
          results[currNode] = EvalResult(val.isNormal());
          break;
        }

        case kind::FLOATINGPOINT_ISZ:
        {
          const FloatingPoint& val = results[currNode[0]].d_fp;
          results[currNode] = EvalResult(val.isZero());
          break;
        }

        case kind::FLOATINGPOINT_ISINF:
        {
          const FloatingPoint& val = results[currNode[0]].d_fp;
          results[currNode] = EvalResult(val.isInfinite());
          break;
        }

        case kind::FLOATINGPOINT_ISNAN:
        {
          const FloatingPoint& val = results[currNode[0]].d_fp;
          results[currNode] = EvalResult(val.isNaN());
          break;
        }

        case kind::FLOATINGPOINT_ISNEG:
        {
          const FloatingPoint& val = results[currNode[0]].d_fp;
          results[currNode] = EvalResult(val.isNegative());
          break;
        }

        case kind::FLOATINGPOINT_ISPOS:
        {
          const FloatingPoint& val = results[currNode[0]].d_fp;
          results[currNode] = EvalResult(val.isPositive());
          break;
        }

        case kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR:
        {
          TNode op = currNode.getOperator();
          const FloatingPointToFPIEEEBitVector& param =
              op.getConst<FloatingPointToFPIEEEBitVector>();
          const BitVector& val = results[currNode[0]].d_bv;
          results[currNode] = EvalResult(
              FloatingPoint(param.t.exponent(), param.t.significand(), val));
          break;
        }

        case kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT:
        {
          TNode op = currNode.getOperator();
          const FloatingPointToFPFloatingPoint& param =
              op.getConst<FloatingPointToFPFloatingPoint>();
          const RoundingMode& rm = results[currNode[0]].d_rm;
          const FloatingPoint& val = results[currNode[1]].d_fp;

          results[currNode] = EvalResult(val.convert(param.t, rm));
          break;
        }

        case kind::FLOATINGPOINT_TO_FP_REAL:
        {
          TNode op = currNode.getOperator();
          const FloatingPointToFPFloatingPoint& param =
              op.getConst<FloatingPointToFPFloatingPoint>();
          const RoundingMode& rm = results[currNode[0]].d_rm;
          const FloatingPoint& val = results[currNode[1]].d_fp;

          results[currNode] = EvalResult(val.convert(param.t, rm));
          break;
        }

        case kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR:
        {
          TNode op = currNode.getOperator();
          const FloatingPointToFPFloatingPoint& param =
              op.getConst<FloatingPointToFPSignedBitVector>();
          const RoundingMode& rm = results[currNode[0]].d_rm;
          const BitVector& val = results[currNode[1]].d_bv;

          results[currNode] = EvalResult(FloatingPoint(param.t, rm, val, true));
          break;
        }

        case kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR:
        {
          TNode op = currNode.getOperator();
          const FloatingPointToFPFloatingPoint& param =
              op.getConst<FloatingPointToFPUnsignedBitVector>();
          const RoundingMode& rm = results[currNode[0]].d_rm;
          const BitVector& val = results[currNode[1]].d_bv;

          results[currNode] =
              EvalResult(FloatingPoint(param.t, rm, val, false));
          break;
        }

        case kind::FLOATINGPOINT_TO_UBV:
        {
          TNode op = currNode.getOperator();
          const FloatingPointToUBV& param =
              op.getOperator().getConst<FloatingPointToUBV>();
          const RoundingMode& rm = results[currNode[0]].d_rm;
          const FloatingPoint& val = results[currNode[1]].d_fp;

          FloatingPoint::PartialBitVector res(
              val.convertToBV(param.bvs, rm, false));

          if (res.second)
          {
            results[currNode] = EvalResult(res.first);
          }
          else
          {
            // Can't constant fold the underspecified case
            return EvalResult();
          }

          break;
        }

        case kind::FLOATINGPOINT_TO_UBV_TOTAL:
        {
          TNode op = currNode.getOperator();
          const FloatingPointToUBVTotal& param =
              op.getOperator().getConst<FloatingPointToUBVTotal>();
          const RoundingMode& rm = results[currNode[0]].d_rm;
          const FloatingPoint& val = results[currNode[1]].d_fp;
          const BitVector& partial = results[currNode[2]].d_bv;

          results[currNode] =
              EvalResult(val.convertToBVTotal(param.bvs, rm, false, partial));
          break;
        }

        case kind::FLOATINGPOINT_TO_SBV:
        {
          TNode op = currNode.getOperator();
          const FloatingPointToSBV& param =
              op.getOperator().getConst<FloatingPointToSBV>();
          const RoundingMode& rm = results[currNode[0]].d_rm;
          const FloatingPoint& val = results[currNode[1]].d_fp;

          FloatingPoint::PartialBitVector res(
              val.convertToBV(param.bvs, rm, true));

          if (res.second)
          {
            results[currNode] = EvalResult(res.first);
          }
          else
          {
            // Can't constant fold the underspecified case
            return EvalResult();
          }
          break;
        }

        case kind::FLOATINGPOINT_TO_SBV_TOTAL:
        {
          TNode op = currNode.getOperator();
          const FloatingPointToSBVTotal& param =
              op.getConst<FloatingPointToSBVTotal>();
          const RoundingMode& rm = results[currNode[0]].d_rm;
          const FloatingPoint& val = results[currNode[1]].d_fp;
          const BitVector& partial = results[currNode[2]].d_bv;

          results[currNode] =
              EvalResult(val.convertToBVTotal(param.bvs, rm, true, partial));
          break;
        }

        case kind::FLOATINGPOINT_TO_REAL:
        {
          const FloatingPoint& val = results[currNode[0]].d_fp;

          FloatingPoint::PartialRational res(val.convertToRational());

          if (res.second)
          {
            results[currNode] = EvalResult(res.first);
          }
          else
          {
            // Can't constant fold the underspecified case
            return EvalResult();
          }
          break;
        }

        case kind::FLOATINGPOINT_TO_REAL_TOTAL:
        {
          const FloatingPoint& val = results[currNode[0]].d_fp;
          const Rational& partial = results[currNode[1]].d_rat;

          results[currNode] = EvalResult(val.convertToRationalTotal(partial));
          break;
        }

#ifdef CVC4_USE_SYMFPU
        case kind::FLOATINGPOINT_COMPONENT_NAN:
        {
          const FloatingPoint& val = results[currNode[0]].d_fp;
          results[currNode] = EvalResult(val.getLiteral().nan);
          break;
        }

        case kind::FLOATINGPOINT_COMPONENT_INF:
        {
          const FloatingPoint& val = results[currNode[0]].d_fp;
          results[currNode] = EvalResult(val.getLiteral().inf);
          break;
        }

        case kind::FLOATINGPOINT_COMPONENT_ZERO:
        {
          const FloatingPoint& val = results[currNode[0]].d_fp;
          results[currNode] = EvalResult(val.getLiteral().zero);
          break;
        }

        case kind::FLOATINGPOINT_COMPONENT_SIGN:
        {
          const FloatingPoint& val = results[currNode[0]].d_fp;
          results[currNode] = EvalResult(val.getLiteral().sign);
          break;
        }

        case kind::FLOATINGPOINT_COMPONENT_EXPONENT:
        {
          const FloatingPoint& val = results[currNode[0]].d_fp;
          results[currNode] = EvalResult(val.getLiteral().exponent);
          break;
        }

        case kind::FLOATINGPOINT_COMPONENT_SIGNIFICAND:
        {
          const FloatingPoint& val = results[currNode[0]].d_fp;
          results[currNode] = EvalResult(val.getLiteral().significand);
          break;
        }
#else
        case kind::FLOATINGPOINT_COMPONENT_NAN:
        case kind::FLOATINGPOINT_COMPONENT_INF:
        case kind::FLOATINGPOINT_COMPONENT_ZERO:
        case kind::FLOATINGPOINT_COMPONENT_SIGN:
        case kind::FLOATINGPOINT_COMPONENT_EXPONENT:
        case kind::FLOATINGPOINT_COMPONENT_SIGNIFICAND:
        {
          // symfpu is required for these operators
          return EvalResult();
        }
#endif

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

            case EvalResult::ROUNDINGMODE:
            {
              results[currNode] = EvalResult(lhs.d_rm == rhs.d_rm);
              break;
            }

            case EvalResult::FLOATINGPOINT:
            {
              results[currNode] = EvalResult(lhs.d_fp == rhs.d_fp);
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
              return EvalResult();
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
          return EvalResult();
        }
      }
    }
  }

  return results[n];
}

}  // namespace theory
}  // namespace CVC4
