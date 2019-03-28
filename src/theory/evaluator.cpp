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
                     const std::vector<Node>& vals)
{
  Trace("evaluator") << "Evaluating " << n << " under substitution " << args
                     << " " << vals << std::endl;
  return evalInternal(n, args, vals).toNode();
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
        if (results[currNode].d_tag == EvalResult::INVALID)
        {
          // evaluation was invalid, we fail
          return results[currNode];
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

        case kind::STRING_CODE:
        {
          const String& s = results[currNode[0]].d_str;
          if (s.size() == 1)
          {
            results[currNode] = EvalResult(
                Rational(String::convertUnsignedIntToCode(s.getVec()[0])));
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
