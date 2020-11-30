/*********************                                                        */
/*! \file operator_elim.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of operator elimination for arithmetic
 **/

#include "theory/arith/operator_elim.h"

#include "expr/skolem_manager.h"
#include "options/arith_options.h"
#include "smt/logic_exception.h"
#include "theory/arith/arith_utilities.h"
#include "theory/rewriter.h"
#include "theory/theory.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {

OperatorElim::OperatorElim(ProofNodeManager* pnm, const LogicInfo& info)
    : EagerProofGenerator(pnm), d_info(info)
{
}

void OperatorElim::checkNonLinearLogic(Node term)
{
  if (d_info.isLinear())
  {
    Trace("arith-logic") << "ERROR: Non-linear term in linear logic: " << term
                         << std::endl;
    std::stringstream serr;
    serr << "A non-linear fact was asserted to arithmetic in a linear logic."
         << std::endl;
    serr << "The fact in question: " << term << std::endl;
    throw LogicException(serr.str());
  }
}

TrustNode OperatorElim::eliminate(Node n)
{
  TConvProofGenerator* tg = nullptr;
  Node nn = eliminateOperators(n, tg);
  if (nn != n)
  {
    // since elimination may introduce new operators to eliminate, we must
    // recursively eliminate result
    Node nnr = eliminateOperatorsRec(nn, tg);
    return TrustNode::mkTrustRewrite(n, nnr, nullptr);
  }
  return TrustNode::null();
}

Node OperatorElim::eliminateOperatorsRec(Node n, TConvProofGenerator* tg)
{
  Trace("arith-elim") << "Begin elim: " << n << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<Node, Node, TNodeHashFunction> visited;
  std::unordered_map<Node, Node, TNodeHashFunction>::iterator it;
  std::vector<Node> visit;
  Node cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);
    if (Theory::theoryOf(cur) != THEORY_ARITH)
    {
      visited[cur] = cur;
    }
    else if (it == visited.end())
    {
      visited[cur] = Node::null();
      visit.push_back(cur);
      for (const Node& cn : cur)
      {
        visit.push_back(cn);
      }
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == metakind::PARAMETERIZED)
      {
        children.push_back(cur.getOperator());
      }
      for (const Node& cn : cur)
      {
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      if (childChanged)
      {
        ret = nm->mkNode(cur.getKind(), children);
      }
      Node retElim = eliminateOperators(ret, tg);
      if (retElim != ret)
      {
        // recursively eliminate operators in result, since some eliminations
        // are defined in terms of other non-standard operators.
        ret = eliminateOperatorsRec(retElim, tg);
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
}

Node OperatorElim::eliminateOperators(Node node, TConvProofGenerator* tg)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();

  Kind k = node.getKind();
  switch (k)
  {
    case TANGENT:
    case COSECANT:
    case SECANT:
    case COTANGENT:
    {
      // these are eliminated by rewriting
      return Rewriter::rewrite(node);
      break;
    }
    case TO_INTEGER:
    case IS_INTEGER:
    {
      Node toIntSkolem;
      std::map<Node, Node>::const_iterator it = d_to_int_skolem.find(node[0]);
      if (it == d_to_int_skolem.end())
      {
        // node[0] - 1 < toIntSkolem <= node[0]
        // -1 < toIntSkolem - node[0] <= 0
        // 0 <= node[0] - toIntSkolem < 1
        Node v = nm->mkBoundVar(nm->integerType());
        Node one = mkRationalNode(1);
        Node zero = mkRationalNode(0);
        Node diff = nm->mkNode(MINUS, node[0], v);
        Node lem = mkInRange(diff, zero, one);
        toIntSkolem =
            sm->mkSkolem(v,
                         lem,
                         "toInt",
                         "a conversion of a Real term to its Integer part",
                         NodeManager::SKOLEM_DEFAULT,
                         this,
                         true);
        d_to_int_skolem[node[0]] = toIntSkolem;
      }
      else
      {
        toIntSkolem = (*it).second;
      }
      if (k == IS_INTEGER)
      {
        return nm->mkNode(EQUAL, node[0], toIntSkolem);
      }
      Assert(k == TO_INTEGER);
      return toIntSkolem;
    }

    case INTS_DIVISION_TOTAL:
    case INTS_MODULUS_TOTAL:
    {
      Node den = Rewriter::rewrite(node[1]);
      Node num = Rewriter::rewrite(node[0]);
      Node intVar;
      Node rw = nm->mkNode(k, num, den);
      std::map<Node, Node>::const_iterator it = d_int_div_skolem.find(rw);
      if (it == d_int_div_skolem.end())
      {
        Node v = nm->mkBoundVar(nm->integerType());
        Node lem;
        Node leqNum = nm->mkNode(LEQ, nm->mkNode(MULT, den, v), num);
        if (den.isConst())
        {
          const Rational& rat = den.getConst<Rational>();
          if (num.isConst() || rat == 0)
          {
            // just rewrite
            return Rewriter::rewrite(node);
          }
          if (rat > 0)
          {
            lem = nm->mkNode(
                AND,
                leqNum,
                nm->mkNode(
                    LT,
                    num,
                    nm->mkNode(MULT,
                               den,
                               nm->mkNode(PLUS, v, nm->mkConst(Rational(1))))));
          }
          else
          {
            lem = nm->mkNode(
                AND,
                leqNum,
                nm->mkNode(
                    LT,
                    num,
                    nm->mkNode(
                        MULT,
                        den,
                        nm->mkNode(PLUS, v, nm->mkConst(Rational(-1))))));
          }
        }
        else
        {
          checkNonLinearLogic(node);
          lem = nm->mkNode(
              AND,
              nm->mkNode(
                  IMPLIES,
                  nm->mkNode(GT, den, nm->mkConst(Rational(0))),
                  nm->mkNode(
                      AND,
                      leqNum,
                      nm->mkNode(
                          LT,
                          num,
                          nm->mkNode(
                              MULT,
                              den,
                              nm->mkNode(PLUS, v, nm->mkConst(Rational(1))))))),
              nm->mkNode(
                  IMPLIES,
                  nm->mkNode(LT, den, nm->mkConst(Rational(0))),
                  nm->mkNode(
                      AND,
                      leqNum,
                      nm->mkNode(
                          LT,
                          num,
                          nm->mkNode(
                              MULT,
                              den,
                              nm->mkNode(
                                  PLUS, v, nm->mkConst(Rational(-1))))))));
        }
        intVar = sm->mkSkolem(v,
                              lem,
                              "linearIntDiv",
                              "the result of an intdiv-by-k term",
                              NodeManager::SKOLEM_DEFAULT,
                              this,
                              true);
        d_int_div_skolem[rw] = intVar;
      }
      else
      {
        intVar = (*it).second;
      }
      if (k == INTS_MODULUS_TOTAL)
      {
        Node nn = nm->mkNode(MINUS, num, nm->mkNode(MULT, den, intVar));
        return nn;
      }
      else
      {
        return intVar;
      }
      break;
    }
    case DIVISION_TOTAL:
    {
      Node num = Rewriter::rewrite(node[0]);
      Node den = Rewriter::rewrite(node[1]);
      if (den.isConst())
      {
        // No need to eliminate here, can eliminate via rewriting later.
        // Moreover, rewriting may change the type of this node from real to
        // int, which impacts certain issues with subtyping.
        return node;
      }
      checkNonLinearLogic(node);
      Node var;
      Node rw = nm->mkNode(k, num, den);
      std::map<Node, Node>::const_iterator it = d_div_skolem.find(rw);
      if (it == d_div_skolem.end())
      {
        Node v = nm->mkBoundVar(nm->realType());
        Node lem = nm->mkNode(IMPLIES,
                              den.eqNode(nm->mkConst(Rational(0))).negate(),
                              nm->mkNode(MULT, den, v).eqNode(num));
        var = sm->mkSkolem(v,
                           lem,
                           "nonlinearDiv",
                           "the result of a non-linear div term",
                           NodeManager::SKOLEM_DEFAULT,
                           this,
                           true);
        d_div_skolem[rw] = var;
      }
      else
      {
        var = (*it).second;
      }
      return var;
      break;
    }
    case DIVISION:
    {
      Node num = Rewriter::rewrite(node[0]);
      Node den = Rewriter::rewrite(node[1]);
      Node ret = nm->mkNode(DIVISION_TOTAL, num, den);
      if (!den.isConst() || den.getConst<Rational>().sgn() == 0)
      {
        checkNonLinearLogic(node);
        Node divByZeroNum = getArithSkolemApp(num, ArithSkolemId::DIV_BY_ZERO);
        Node denEq0 = nm->mkNode(EQUAL, den, nm->mkConst(Rational(0)));
        ret = nm->mkNode(ITE, denEq0, divByZeroNum, ret);
      }
      return ret;
      break;
    }

    case INTS_DIVISION:
    {
      // partial function: integer div
      Node num = Rewriter::rewrite(node[0]);
      Node den = Rewriter::rewrite(node[1]);
      Node ret = nm->mkNode(INTS_DIVISION_TOTAL, num, den);
      if (!den.isConst() || den.getConst<Rational>().sgn() == 0)
      {
        checkNonLinearLogic(node);
        Node intDivByZeroNum =
            getArithSkolemApp(num, ArithSkolemId::INT_DIV_BY_ZERO);
        Node denEq0 = nm->mkNode(EQUAL, den, nm->mkConst(Rational(0)));
        ret = nm->mkNode(ITE, denEq0, intDivByZeroNum, ret);
      }
      return ret;
      break;
    }

    case INTS_MODULUS:
    {
      // partial function: mod
      Node num = Rewriter::rewrite(node[0]);
      Node den = Rewriter::rewrite(node[1]);
      Node ret = nm->mkNode(INTS_MODULUS_TOTAL, num, den);
      if (!den.isConst() || den.getConst<Rational>().sgn() == 0)
      {
        checkNonLinearLogic(node);
        Node modZeroNum = getArithSkolemApp(num, ArithSkolemId::MOD_BY_ZERO);
        Node denEq0 = nm->mkNode(EQUAL, den, nm->mkConst(Rational(0)));
        ret = nm->mkNode(ITE, denEq0, modZeroNum, ret);
      }
      return ret;
      break;
    }

    case ABS:
    {
      return nm->mkNode(ITE,
                        nm->mkNode(LT, node[0], nm->mkConst(Rational(0))),
                        nm->mkNode(UMINUS, node[0]),
                        node[0]);
      break;
    }
    case SQRT:
    case ARCSINE:
    case ARCCOSINE:
    case ARCTANGENT:
    case ARCCOSECANT:
    case ARCSECANT:
    case ARCCOTANGENT:
    {
      checkNonLinearLogic(node);
      // eliminate inverse functions here
      std::map<Node, Node>::const_iterator it =
          d_nlin_inverse_skolem.find(node);
      if (it == d_nlin_inverse_skolem.end())
      {
        Node var = nm->mkBoundVar(nm->realType());
        Node lem;
        if (k == SQRT)
        {
          Node skolemApp = getArithSkolemApp(node[0], ArithSkolemId::SQRT);
          Node uf = skolemApp.eqNode(var);
          Node nonNeg =
              nm->mkNode(AND, nm->mkNode(MULT, var, var).eqNode(node[0]), uf);

          // sqrt(x) reduces to:
          // witness y. ite(x >= 0.0, y * y = x ^ y = Uf(x), y = Uf(x))
          //
          // Uf(x) makes sure that the reduction still behaves like a function,
          // otherwise the reduction of (x = 1) ^ (sqrt(x) != sqrt(1)) would be
          // satisfiable. On the original formula, this would require that we
          // simultaneously interpret sqrt(1) as 1 and -1, which is not a valid
          // model.
          lem = nm->mkNode(ITE,
                           nm->mkNode(GEQ, node[0], nm->mkConst(Rational(0))),
                           nonNeg,
                           uf);
        }
        else
        {
          Node pi = mkPi();

          // range of the skolem
          Node rlem;
          if (k == ARCSINE || k == ARCTANGENT || k == ARCCOSECANT)
          {
            Node half = nm->mkConst(Rational(1) / Rational(2));
            Node pi2 = nm->mkNode(MULT, half, pi);
            Node npi2 = nm->mkNode(MULT, nm->mkConst(Rational(-1)), pi2);
            // -pi/2 < var <= pi/2
            rlem = nm->mkNode(
                AND, nm->mkNode(LT, npi2, var), nm->mkNode(LEQ, var, pi2));
          }
          else
          {
            // 0 <= var < pi
            rlem = nm->mkNode(AND,
                              nm->mkNode(LEQ, nm->mkConst(Rational(0)), var),
                              nm->mkNode(LT, var, pi));
          }

          Kind rk = k == ARCSINE
                        ? SINE
                        : (k == ARCCOSINE
                               ? COSINE
                               : (k == ARCTANGENT
                                      ? TANGENT
                                      : (k == ARCCOSECANT
                                             ? COSECANT
                                             : (k == ARCSECANT ? SECANT
                                                               : COTANGENT))));
          Node invTerm = nm->mkNode(rk, var);
          lem = nm->mkNode(AND, rlem, invTerm.eqNode(node[0]));
        }
        Assert(!lem.isNull());
        Node ret = sm->mkSkolem(
            var,
            lem,
            "tfk",
            "Skolem to eliminate a non-standard transcendental function",
            NodeManager::SKOLEM_DEFAULT,
            this,
            true);
        Assert(ret.getKind() == WITNESS);
        d_nlin_inverse_skolem[node] = ret;
        return ret;
      }
      return (*it).second;
      break;
    }

    default: break;
  }
  return node;
}

Node OperatorElim::getAxiomFor(Node n) { return Node::null(); }

Node OperatorElim::getArithSkolem(ArithSkolemId asi)
{
  std::map<ArithSkolemId, Node>::iterator it = d_arith_skolem.find(asi);
  if (it == d_arith_skolem.end())
  {
    NodeManager* nm = NodeManager::currentNM();

    TypeNode tn;
    std::string name;
    std::string desc;
    switch (asi)
    {
      case ArithSkolemId::DIV_BY_ZERO:
        tn = nm->realType();
        name = std::string("divByZero");
        desc = std::string("partial real division");
        break;
      case ArithSkolemId::INT_DIV_BY_ZERO:
        tn = nm->integerType();
        name = std::string("intDivByZero");
        desc = std::string("partial int division");
        break;
      case ArithSkolemId::MOD_BY_ZERO:
        tn = nm->integerType();
        name = std::string("modZero");
        desc = std::string("partial modulus");
        break;
      case ArithSkolemId::SQRT:
        tn = nm->realType();
        name = std::string("sqrtUf");
        desc = std::string("partial sqrt");
        break;
      default: Unhandled();
    }

    Node skolem;
    if (options::arithNoPartialFun())
    {
      // partial function: division
      skolem = nm->mkSkolem(name, tn, desc, NodeManager::SKOLEM_EXACT_NAME);
    }
    else
    {
      // partial function: division
      skolem = nm->mkSkolem(name,
                            nm->mkFunctionType(tn, tn),
                            desc,
                            NodeManager::SKOLEM_EXACT_NAME);
    }
    d_arith_skolem[asi] = skolem;
    return skolem;
  }
  return it->second;
}

Node OperatorElim::getArithSkolemApp(Node n, ArithSkolemId asi)
{
  Node skolem = getArithSkolem(asi);
  if (!options::arithNoPartialFun())
  {
    skolem = NodeManager::currentNM()->mkNode(APPLY_UF, skolem, n);
  }
  return skolem;
}

}  // namespace arith
}  // namespace theory
}  // namespace CVC4
