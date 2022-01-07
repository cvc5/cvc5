#include "theory/arith/arith_evaluator.h"

#include "theory/arith/nl/poly_conversion.h"
#include "theory/rewriter.h"
#include "theory/theory.h"
#include "util/real_algebraic_number.h"

namespace cvc5 {
namespace theory {
namespace arith {

namespace {

RealAlgebraicNumber evaluate(TNode expr,
                             const std::map<Node, RealAlgebraicNumber>& rans)
{
  switch (expr.getKind())
  {
    case Kind::PLUS:
    {
      RealAlgebraicNumber aggr;
      for (const auto& n : expr)
      {
        aggr += evaluate(n, rans);
      }
      return aggr;
    }
    case Kind::MULT:
    case Kind::NONLINEAR_MULT:
    {
      RealAlgebraicNumber aggr(Integer(1));
      for (const auto& n : expr)
      {
        aggr *= evaluate(n, rans);
      }
      return aggr;
    }
    case Kind::MINUS:
      Assert(expr.getNumChildren() == 2);
      return evaluate(expr[0], rans) - evaluate(expr[1], rans);
    case Kind::UMINUS: return -evaluate(expr[0], rans);
    case Kind::CONST_RATIONAL:
      return RealAlgebraicNumber(expr.getConst<Rational>());
    default:
      auto it = rans.find(expr);
      if (it != rans.end())
      {
        return it->second;
      }
      Assert(false) << "Unsupported expression kind for RAN evaluation: "
                    << expr.getKind();
      return RealAlgebraicNumber();
  }
}

}  // namespace

bool isExpressionZero(Env& env, Node expr, const std::map<Node, Node>& model)
{
  // Substitute constants and rewrite
  expr = env.getRewriter()->rewrite(expr);
  if (expr.isConst())
  {
    return expr.getConst<Rational>().isZero();
  }
  std::map<Node, RealAlgebraicNumber> rans;
  std::vector<TNode> nodes;
  std::vector<TNode> repls;
  for (const auto& [node, repl] : model)
  {
    if (repl.getType().isRealOrInt()
        && Theory::isLeafOf(repl, TheoryId::THEORY_ARITH))
    {
      nodes.emplace_back(node);
      repls.emplace_back(repl);
    }
    else
    {
      rans.emplace(node, nl::node_to_ran(repl, node));
    }
  }
  expr =
      expr.substitute(nodes.begin(), nodes.end(), repls.begin(), repls.end());
  expr = env.getRewriter()->rewrite(expr);
  if (expr.isConst())
  {
    return expr.getConst<Rational>().isZero();
  }
  return isZero(evaluate(expr, rans));
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5
