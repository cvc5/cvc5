#include "theory/arith/arith_evaluator.h"

#include "theory/arith/nl/poly_conversion.h"
#include "theory/rewriter.h"
#include "theory/theory.h"
#include "util/real_algebraic_number.h"

namespace cvc5 {
namespace theory {
namespace arith {

std::optional<bool> isExpressionZero(Env& env,
                                     Node expr,
                                     const std::map<Node, Node>& model)
{
  // Substitute constants and rewrite
  expr = env.getRewriter()->rewrite(expr);
  if (expr.isConst())
  {
    return expr.getConst<Rational>().isZero();
  }
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
  }
  expr =
      expr.substitute(nodes.begin(), nodes.end(), repls.begin(), repls.end());
  expr = env.getRewriter()->rewrite(expr);
  if (expr.isConst())
  {
    return expr.getConst<Rational>().isZero();
  }
  if (expr.getKind() == Kind::REAL_ALGEBRAIC_NUMBER)
  {
    return isZero(expr.getOperator().getConst<RealAlgebraicNumber>());
  }
  return std::nullopt;
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5
