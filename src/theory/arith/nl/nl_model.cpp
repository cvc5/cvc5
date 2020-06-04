/*********************                                                        */
/*! \file nl_model.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Model object for the non-linear extension class
 **/

#include "theory/arith/nl/nl_model.h"

#include "expr/node_algorithm.h"
#include "options/arith_options.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_utilities.h"
#include "theory/rewriter.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {

NlModel::NlModel(context::Context* c) : d_used_approx(false)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
  d_zero = NodeManager::currentNM()->mkConst(Rational(0));
  d_one = NodeManager::currentNM()->mkConst(Rational(1));
  d_two = NodeManager::currentNM()->mkConst(Rational(2));
}

NlModel::~NlModel() {}

void NlModel::reset(TheoryModel* m, std::map<Node, Node>& arithModel)
{
  d_model = m;
  d_mv[0].clear();
  d_mv[1].clear();
  d_arithVal.clear();
  // process arithModel
  std::map<Node, Node>::iterator it;
  for (const std::pair<const Node, Node>& m2 : arithModel)
  {
    d_arithVal[m2.first] = m2.second;
  }
}

void NlModel::resetCheck()
{
  d_used_approx = false;
  d_check_model_solved.clear();
  d_check_model_bounds.clear();
  d_check_model_vars.clear();
  d_check_model_subs.clear();
}

Node NlModel::computeConcreteModelValue(Node n)
{
  return computeModelValue(n, true);
}

Node NlModel::computeAbstractModelValue(Node n)
{
  return computeModelValue(n, false);
}

Node NlModel::computeModelValue(Node n, bool isConcrete)
{
  unsigned index = isConcrete ? 0 : 1;
  std::map<Node, Node>::iterator it = d_mv[index].find(n);
  if (it != d_mv[index].end())
  {
    return it->second;
  }
  Trace("nl-ext-mv-debug") << "computeModelValue " << n << ", index=" << index
                           << std::endl;
  Node ret;
  Kind nk = n.getKind();
  if (n.isConst())
  {
    ret = n;
  }
  else if (!isConcrete && hasTerm(n))
  {
    // use model value for abstraction
    ret = getRepresentative(n);
  }
  else if (n.getNumChildren() == 0)
  {
    // we are interested in the exact value of PI, which cannot be computed.
    // hence, we return PI itself when asked for the concrete value.
    if (nk == PI)
    {
      ret = n;
    }
    else
    {
      ret = getValueInternal(n);
    }
  }
  else
  {
    // otherwise, compute true value
    TheoryId ctid = theory::kindToTheoryId(nk);
    if (ctid != THEORY_ARITH && ctid != THEORY_BOOL && ctid != THEORY_BUILTIN)
    {
      // we directly look up terms not belonging to arithmetic
      ret = getValueInternal(n);
    }
    else
    {
      std::vector<Node> children;
      if (n.getMetaKind() == metakind::PARAMETERIZED)
      {
        children.push_back(n.getOperator());
      }
      for (unsigned i = 0, nchild = n.getNumChildren(); i < nchild; i++)
      {
        Node mc = computeModelValue(n[i], isConcrete);
        children.push_back(mc);
      }
      ret = NodeManager::currentNM()->mkNode(nk, children);
      ret = Rewriter::rewrite(ret);
    }
  }
  Trace("nl-ext-mv-debug") << "computed " << (index == 0 ? "M" : "M_A") << "["
                           << n << "] = " << ret << std::endl;
  d_mv[index][n] = ret;
  return ret;
}

bool NlModel::hasTerm(Node n) const
{
  return d_arithVal.find(n) != d_arithVal.end();
}

Node NlModel::getRepresentative(Node n) const
{
  if (n.isConst())
  {
    return n;
  }
  std::map<Node, Node>::const_iterator it = d_arithVal.find(n);
  if (it != d_arithVal.end())
  {
    AlwaysAssert(it->second.isConst());
    return it->second;
  }
  return d_model->getRepresentative(n);
}

Node NlModel::getValueInternal(Node n) const
{
  if (n.isConst())
  {
    return n;
  }
  std::map<Node, Node>::const_iterator it = d_arithVal.find(n);
  if (it != d_arithVal.end())
  {
    AlwaysAssert(it->second.isConst());
    return it->second;
  }
  // It is unconstrained in the model, return 0.
  return d_zero;
}

int NlModel::compare(Node i, Node j, bool isConcrete, bool isAbsolute)
{
  Node ci = computeModelValue(i, isConcrete);
  Node cj = computeModelValue(j, isConcrete);
  if (ci.isConst())
  {
    if (cj.isConst())
    {
      return compareValue(ci, cj, isAbsolute);
    }
    return 1;
  }
  return cj.isConst() ? -1 : 0;
}

int NlModel::compareValue(Node i, Node j, bool isAbsolute) const
{
  Assert(i.isConst() && j.isConst());
  int ret;
  if (i == j)
  {
    ret = 0;
  }
  else if (!isAbsolute)
  {
    ret = i.getConst<Rational>() < j.getConst<Rational>() ? 1 : -1;
  }
  else
  {
    ret = (i.getConst<Rational>().abs() == j.getConst<Rational>().abs()
               ? 0
               : (i.getConst<Rational>().abs() < j.getConst<Rational>().abs()
                      ? 1
                      : -1));
  }
  return ret;
}

bool NlModel::checkModel(const std::vector<Node>& assertions,
                         const std::vector<Node>& false_asserts,
                         unsigned d,
                         std::vector<Node>& lemmas,
                         std::vector<Node>& gs)
{
  Trace("nl-ext-cm-debug") << "  solve for equalities..." << std::endl;
  for (const Node& atom : false_asserts)
  {
    // see if it corresponds to a univariate polynomial equation of degree two
    if (atom.getKind() == EQUAL)
    {
      if (!solveEqualitySimple(atom, d, lemmas))
      {
        // no chance we will satisfy this equality
        Trace("nl-ext-cm") << "...check-model : failed to solve equality : "
                           << atom << std::endl;
      }
    }
  }

  // all remaining variables are constrained to their exact model values
  Trace("nl-ext-cm-debug") << "  set exact bounds for remaining variables..."
                           << std::endl;
  std::unordered_set<TNode, TNodeHashFunction> visited;
  std::vector<TNode> visit;
  TNode cur;
  for (const Node& a : assertions)
  {
    visit.push_back(a);
    do
    {
      cur = visit.back();
      visit.pop_back();
      if (visited.find(cur) == visited.end())
      {
        visited.insert(cur);
        if (cur.getType().isReal() && !cur.isConst())
        {
          Kind k = cur.getKind();
          if (k != MULT && k != PLUS && k != NONLINEAR_MULT
              && !isTranscendentalKind(k))
          {
            // if we have not set an approximate bound for it
            if (!hasCheckModelAssignment(cur))
            {
              // set its exact model value in the substitution
              Node curv = computeConcreteModelValue(cur);
              Trace("nl-ext-cm")
                  << "check-model-bound : exact : " << cur << " = ";
              printRationalApprox("nl-ext-cm", curv);
              Trace("nl-ext-cm") << std::endl;
              bool ret = addCheckModelSubstitution(cur, curv);
              AlwaysAssert(ret);
            }
          }
        }
        for (const Node& cn : cur)
        {
          visit.push_back(cn);
        }
      }
    } while (!visit.empty());
  }

  Trace("nl-ext-cm-debug") << "  check assertions..." << std::endl;
  std::vector<Node> check_assertions;
  for (const Node& a : assertions)
  {
    // don't have to check tautological literals
    if (d_tautology.find(a) != d_tautology.end())
    {
      continue;
    }
    if (d_check_model_solved.find(a) == d_check_model_solved.end())
    {
      Node av = a;
      // apply the substitution to a
      if (!d_check_model_vars.empty())
      {
        av = arithSubstitute(av, d_check_model_vars, d_check_model_subs);
        av = Rewriter::rewrite(av);
      }
      // simple check literal
      if (!simpleCheckModelLit(av))
      {
        Trace("nl-ext-cm") << "...check-model : assertion failed : " << a
                           << std::endl;
        check_assertions.push_back(av);
        Trace("nl-ext-cm-debug")
            << "...check-model : failed assertion, value : " << av << std::endl;
      }
    }
  }

  if (!check_assertions.empty())
  {
    Trace("nl-ext-cm") << "...simple check failed." << std::endl;
    // TODO (#1450) check model for general case
    return false;
  }
  Trace("nl-ext-cm") << "...simple check succeeded!" << std::endl;

  // must assert and re-check if produce models is true
  if (options::produceModels())
  {
    NodeManager* nm = NodeManager::currentNM();
    // model guard whose semantics is "the model we constructed holds"
    Node mg = nm->mkSkolem("model", nm->booleanType());
    gs.push_back(mg);
    // assert the constructed model as assertions
    for (const std::pair<const Node, std::pair<Node, Node>> cb :
         d_check_model_bounds)
    {
      Node l = cb.second.first;
      Node u = cb.second.second;
      Node v = cb.first;
      Node pred = nm->mkNode(AND, nm->mkNode(GEQ, v, l), nm->mkNode(GEQ, u, v));
      pred = nm->mkNode(OR, mg.negate(), pred);
      lemmas.push_back(pred);
    }
  }
  return true;
}

bool NlModel::addCheckModelSubstitution(TNode v, TNode s)
{
  // should not substitute the same variable twice
  Trace("nl-ext-model") << "* check model substitution : " << v << " -> " << s
                        << std::endl;
  // should not set exact bound more than once
  if (std::find(d_check_model_vars.begin(), d_check_model_vars.end(), v)
      != d_check_model_vars.end())
  {
    Trace("nl-ext-model") << "...ERROR: already has value." << std::endl;
    // this should never happen since substitutions should be applied eagerly
    Assert(false);
    return false;
  }
  // if we previously had an approximate bound, the exact bound should be in its
  // range
  std::map<Node, std::pair<Node, Node>>::iterator itb =
      d_check_model_bounds.find(v);
  if (itb != d_check_model_bounds.end())
  {
    if (s.getConst<Rational>() >= itb->second.first.getConst<Rational>()
        || s.getConst<Rational>() <= itb->second.second.getConst<Rational>())
    {
      Trace("nl-ext-model")
          << "...ERROR: already has bound which is out of range." << std::endl;
      return false;
    }
  }
  std::vector<Node> varsTmp;
  varsTmp.push_back(v);
  std::vector<Node> subsTmp;
  subsTmp.push_back(s);
  for (unsigned i = 0, size = d_check_model_subs.size(); i < size; i++)
  {
    Node ms = d_check_model_subs[i];
    Node mss = arithSubstitute(ms, varsTmp, subsTmp);
    if (mss != ms)
    {
      mss = Rewriter::rewrite(mss);
    }
    d_check_model_subs[i] = mss;
  }
  d_check_model_vars.push_back(v);
  d_check_model_subs.push_back(s);
  return true;
}

bool NlModel::addCheckModelBound(TNode v, TNode l, TNode u)
{
  Trace("nl-ext-model") << "* check model bound : " << v << " -> [" << l << " "
                        << u << "]" << std::endl;
  if (l == u)
  {
    // bound is exact, can add as substitution
    return addCheckModelSubstitution(v, l);
  }
  // should not set a bound for a value that is exact
  if (std::find(d_check_model_vars.begin(), d_check_model_vars.end(), v)
      != d_check_model_vars.end())
  {
    Trace("nl-ext-model")
        << "...ERROR: setting bound for variable that already has exact value."
        << std::endl;
    Assert(false);
    return false;
  }
  Assert(l.isConst());
  Assert(u.isConst());
  Assert(l.getConst<Rational>() <= u.getConst<Rational>());
  d_check_model_bounds[v] = std::pair<Node, Node>(l, u);
  if (Trace.isOn("nl-ext-cm"))
  {
    Trace("nl-ext-cm") << "check-model-bound : approximate : ";
    printRationalApprox("nl-ext-cm", l);
    Trace("nl-ext-cm") << " <= " << v << " <= ";
    printRationalApprox("nl-ext-cm", u);
    Trace("nl-ext-cm") << std::endl;
  }
  return true;
}

bool NlModel::hasCheckModelAssignment(Node v) const
{
  if (d_check_model_bounds.find(v) != d_check_model_bounds.end())
  {
    return true;
  }
  return std::find(d_check_model_vars.begin(), d_check_model_vars.end(), v)
         != d_check_model_vars.end();
}

void NlModel::setUsedApproximate() { d_used_approx = true; }

bool NlModel::usedApproximate() const { return d_used_approx; }

void NlModel::addTautology(Node n)
{
  // ensure rewritten
  n = Rewriter::rewrite(n);
  std::unordered_set<TNode, TNodeHashFunction> visited;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      if (cur.getKind() == AND)
      {
        // children of AND are also implied
        for (const Node& cn : cur)
        {
          visit.push_back(cn);
        }
      }
      else
      {
        // is this an arithmetic literal?
        Node atom = cur.getKind() == NOT ? cur[0] : cur;
        if ((atom.getKind() == EQUAL && atom[0].getType().isReal())
            || atom.getKind() == LEQ)
        {
          // Add to tautological literals if it does not contain
          // non-linear multiplication. We cannot consider literals
          // with non-linear multiplication to be tautological since this
          // model object is responsible for checking whether they hold.
          // (TODO, cvc4-projects #113: revisit this).
          if (!expr::hasSubtermKind(NONLINEAR_MULT, atom))
          {
            Trace("nl-taut") << "Tautological literal: " << atom << std::endl;
            d_tautology.insert(cur);
          }
        }
      }
    }
  } while (!visit.empty());
}

bool NlModel::solveEqualitySimple(Node eq,
                                  unsigned d,
                                  std::vector<Node>& lemmas)
{
  Node seq = eq;
  if (!d_check_model_vars.empty())
  {
    seq = arithSubstitute(eq, d_check_model_vars, d_check_model_subs);
    seq = Rewriter::rewrite(seq);
    if (seq.isConst())
    {
      if (seq.getConst<bool>())
      {
        d_check_model_solved[eq] = Node::null();
        return true;
      }
      return false;
    }
  }
  Trace("nl-ext-cms") << "simple solve equality " << seq << "..." << std::endl;
  Assert(seq.getKind() == EQUAL);
  std::map<Node, Node> msum;
  if (!ArithMSum::getMonomialSumLit(seq, msum))
  {
    Trace("nl-ext-cms") << "...fail, could not determine monomial sum."
                        << std::endl;
    return false;
  }
  bool is_valid = true;
  // the variable we will solve a quadratic equation for
  Node var;
  Node a = d_zero;
  Node b = d_zero;
  Node c = d_zero;
  NodeManager* nm = NodeManager::currentNM();
  // the list of variables that occur as a monomial in msum, and whose value
  // is so far unconstrained in the model.
  std::unordered_set<Node, NodeHashFunction> unc_vars;
  // the list of variables that occur as a factor in a monomial, and whose
  // value is so far unconstrained in the model.
  std::unordered_set<Node, NodeHashFunction> unc_vars_factor;
  for (std::pair<const Node, Node>& m : msum)
  {
    Node v = m.first;
    Node coeff = m.second.isNull() ? d_one : m.second;
    if (v.isNull())
    {
      c = coeff;
    }
    else if (v.getKind() == NONLINEAR_MULT)
    {
      if (v.getNumChildren() == 2 && v[0].isVar() && v[0] == v[1]
          && (var.isNull() || var == v[0]))
      {
        // may solve quadratic
        a = coeff;
        var = v[0];
      }
      else
      {
        is_valid = false;
        Trace("nl-ext-cms-debug")
            << "...invalid due to non-linear monomial " << v << std::endl;
        // may wish to set an exact bound for a factor and repeat
        for (const Node& vc : v)
        {
          unc_vars_factor.insert(vc);
        }
      }
    }
    else if (!v.isVar() || (!var.isNull() && var != v))
    {
      Trace("nl-ext-cms-debug")
          << "...invalid due to factor " << v << std::endl;
      // cannot solve multivariate
      if (is_valid)
      {
        is_valid = false;
        // if b is non-zero, then var is also an unconstrained variable
        if (b != d_zero)
        {
          unc_vars.insert(var);
          unc_vars_factor.insert(var);
        }
      }
      // if v is unconstrained, we may turn this equality into a substitution
      unc_vars.insert(v);
      unc_vars_factor.insert(v);
    }
    else
    {
      // set the variable to solve for
      b = coeff;
      var = v;
    }
  }
  if (!is_valid)
  {
    // see if we can solve for a variable?
    for (const Node& uv : unc_vars)
    {
      Trace("nl-ext-cm-debug") << "check subs var : " << uv << std::endl;
      // cannot already have a bound
      if (uv.isVar() && !hasCheckModelAssignment(uv))
      {
        Node slv;
        Node veqc;
        if (ArithMSum::isolate(uv, msum, veqc, slv, EQUAL) != 0)
        {
          Assert(!slv.isNull());
          // Currently do not support substitution-with-coefficients.
          // We also ensure types are correct here, which avoids substituting
          // a term of non-integer type for a variable of integer type.
          if (veqc.isNull() && !expr::hasSubterm(slv, uv)
              && slv.getType().isSubtypeOf(uv.getType()))
          {
            Trace("nl-ext-cm")
                << "check-model-subs : " << uv << " -> " << slv << std::endl;
            bool ret = addCheckModelSubstitution(uv, slv);
            if (ret)
            {
              Trace("nl-ext-cms") << "...success, model substitution " << uv
                                  << " -> " << slv << std::endl;
              d_check_model_solved[eq] = uv;
            }
            return ret;
          }
        }
      }
    }
    // see if we can assign a variable to a constant
    for (const Node& uvf : unc_vars_factor)
    {
      Trace("nl-ext-cm-debug") << "check set var : " << uvf << std::endl;
      // cannot already have a bound
      if (uvf.isVar() && !hasCheckModelAssignment(uvf))
      {
        Node uvfv = computeConcreteModelValue(uvf);
        Trace("nl-ext-cm") << "check-model-bound : exact : " << uvf << " = ";
        printRationalApprox("nl-ext-cm", uvfv);
        Trace("nl-ext-cm") << std::endl;
        bool ret = addCheckModelSubstitution(uvf, uvfv);
        // recurse
        return ret ? solveEqualitySimple(eq, d, lemmas) : false;
      }
    }
    Trace("nl-ext-cms") << "...fail due to constrained invalid terms."
                        << std::endl;
    return false;
  }
  else if (var.isNull() || var.getType().isInteger())
  {
    // cannot solve quadratic equations for integer variables
    Trace("nl-ext-cms") << "...fail due to variable to solve for." << std::endl;
    return false;
  }

  // we are linear, it is simple
  if (a == d_zero)
  {
    if (b == d_zero)
    {
      Trace("nl-ext-cms") << "...fail due to zero a/b." << std::endl;
      Assert(false);
      return false;
    }
    Node val = nm->mkConst(-c.getConst<Rational>() / b.getConst<Rational>());
    Trace("nl-ext-cm") << "check-model-bound : exact : " << var << " = ";
    printRationalApprox("nl-ext-cm", val);
    Trace("nl-ext-cm") << std::endl;
    bool ret = addCheckModelSubstitution(var, val);
    if (ret)
    {
      Trace("nl-ext-cms") << "...success, solved linear." << std::endl;
      d_check_model_solved[eq] = var;
    }
    return ret;
  }
  Trace("nl-ext-quad") << "Solve quadratic : " << seq << std::endl;
  Trace("nl-ext-quad") << "  a : " << a << std::endl;
  Trace("nl-ext-quad") << "  b : " << b << std::endl;
  Trace("nl-ext-quad") << "  c : " << c << std::endl;
  Node two_a = nm->mkNode(MULT, d_two, a);
  two_a = Rewriter::rewrite(two_a);
  Node sqrt_val = nm->mkNode(
      MINUS, nm->mkNode(MULT, b, b), nm->mkNode(MULT, d_two, two_a, c));
  sqrt_val = Rewriter::rewrite(sqrt_val);
  Trace("nl-ext-quad") << "Will approximate sqrt " << sqrt_val << std::endl;
  Assert(sqrt_val.isConst());
  // if it is negative, then we are in conflict
  if (sqrt_val.getConst<Rational>().sgn() == -1)
  {
    Node conf = seq.negate();
    Trace("nl-ext-lemma") << "NlModel::Lemma : quadratic no root : " << conf
                          << std::endl;
    lemmas.push_back(conf);
    Trace("nl-ext-cms") << "...fail due to negative discriminant." << std::endl;
    return false;
  }
  if (hasCheckModelAssignment(var))
  {
    Trace("nl-ext-cms") << "...fail due to bounds on variable to solve for."
                        << std::endl;
    // two quadratic equations for same variable, give up
    return false;
  }
  // approximate the square root of sqrt_val
  Node l, u;
  if (!getApproximateSqrt(sqrt_val, l, u, 15 + d))
  {
    Trace("nl-ext-cms") << "...fail, could not approximate sqrt." << std::endl;
    return false;
  }
  d_used_approx = true;
  Trace("nl-ext-quad") << "...got " << l << " <= sqrt(" << sqrt_val
                       << ") <= " << u << std::endl;
  Node negb = nm->mkConst(-b.getConst<Rational>());
  Node coeffa = nm->mkConst(Rational(1) / two_a.getConst<Rational>());
  // two possible bound regions
  Node bounds[2][2];
  Node diff_bound[2];
  Node m_var = computeConcreteModelValue(var);
  Assert(m_var.isConst());
  for (unsigned r = 0; r < 2; r++)
  {
    for (unsigned b2 = 0; b2 < 2; b2++)
    {
      Node val = b2 == 0 ? l : u;
      // (-b +- approx_sqrt( b^2 - 4ac ))/2a
      Node approx = nm->mkNode(
          MULT, coeffa, nm->mkNode(r == 0 ? MINUS : PLUS, negb, val));
      approx = Rewriter::rewrite(approx);
      bounds[r][b2] = approx;
      Assert(approx.isConst());
    }
    if (bounds[r][0].getConst<Rational>() > bounds[r][1].getConst<Rational>())
    {
      // ensure bound is (lower, upper)
      Node tmp = bounds[r][0];
      bounds[r][0] = bounds[r][1];
      bounds[r][1] = tmp;
    }
    Node diff =
        nm->mkNode(MINUS,
                   m_var,
                   nm->mkNode(MULT,
                              nm->mkConst(Rational(1) / Rational(2)),
                              nm->mkNode(PLUS, bounds[r][0], bounds[r][1])));
    Trace("nl-ext-cm-debug") << "Bound option #" << r << " : ";
    printRationalApprox("nl-ext-cm-debug", bounds[r][0]);
    Trace("nl-ext-cm-debug") << "...";
    printRationalApprox("nl-ext-cm-debug", bounds[r][1]);
    Trace("nl-ext-cm-debug") << std::endl;
    diff = Rewriter::rewrite(diff);
    Assert(diff.isConst());
    diff = nm->mkConst(diff.getConst<Rational>().abs());
    diff_bound[r] = diff;
    Trace("nl-ext-cm-debug") << "...diff from model value (";
    printRationalApprox("nl-ext-cm-debug", m_var);
    Trace("nl-ext-cm-debug") << ") is ";
    printRationalApprox("nl-ext-cm-debug", diff_bound[r]);
    Trace("nl-ext-cm-debug") << std::endl;
  }
  // take the one that var is closer to in the model
  Node cmp = nm->mkNode(GEQ, diff_bound[0], diff_bound[1]);
  cmp = Rewriter::rewrite(cmp);
  Assert(cmp.isConst());
  unsigned r_use_index = cmp == d_true ? 1 : 0;
  Trace("nl-ext-cm") << "check-model-bound : approximate (sqrt) : ";
  printRationalApprox("nl-ext-cm", bounds[r_use_index][0]);
  Trace("nl-ext-cm") << " <= " << var << " <= ";
  printRationalApprox("nl-ext-cm", bounds[r_use_index][1]);
  Trace("nl-ext-cm") << std::endl;
  bool ret =
      addCheckModelBound(var, bounds[r_use_index][0], bounds[r_use_index][1]);
  if (ret)
  {
    d_check_model_solved[eq] = var;
    Trace("nl-ext-cms") << "...success, solved quadratic." << std::endl;
  }
  return ret;
}

bool NlModel::simpleCheckModelLit(Node lit)
{
  Trace("nl-ext-cms") << "*** Simple check-model lit for " << lit << "..."
                      << std::endl;
  if (lit.isConst())
  {
    Trace("nl-ext-cms") << "  return constant." << std::endl;
    return lit.getConst<bool>();
  }
  NodeManager* nm = NodeManager::currentNM();
  bool pol = lit.getKind() != kind::NOT;
  Node atom = lit.getKind() == kind::NOT ? lit[0] : lit;

  if (atom.getKind() == EQUAL)
  {
    // x = a is ( x >= a ^ x <= a )
    for (unsigned i = 0; i < 2; i++)
    {
      Node lit2 = nm->mkNode(GEQ, atom[i], atom[1 - i]);
      if (!pol)
      {
        lit2 = lit2.negate();
      }
      lit2 = Rewriter::rewrite(lit2);
      bool success = simpleCheckModelLit(lit2);
      if (success != pol)
      {
        // false != true -> one conjunct of equality is false, we fail
        // true != false -> one disjunct of disequality is true, we succeed
        return success;
      }
    }
    // both checks passed and polarity is true, or both checks failed and
    // polarity is false
    return pol;
  }
  else if (atom.getKind() != GEQ)
  {
    Trace("nl-ext-cms") << "  failed due to unknown literal." << std::endl;
    return false;
  }
  // get the monomial sum
  std::map<Node, Node> msum;
  if (!ArithMSum::getMonomialSumLit(atom, msum))
  {
    Trace("nl-ext-cms") << "  failed due to get msum." << std::endl;
    return false;
  }
  // simple interval analysis
  if (simpleCheckModelMsum(msum, pol))
  {
    return true;
  }
  // can also try reasoning about univariate quadratic equations
  Trace("nl-ext-cms-debug")
      << "* Try univariate quadratic analysis..." << std::endl;
  std::vector<Node> vs_invalid;
  std::unordered_set<Node, NodeHashFunction> vs;
  std::map<Node, Node> v_a;
  std::map<Node, Node> v_b;
  // get coefficients...
  for (std::pair<const Node, Node>& m : msum)
  {
    Node v = m.first;
    if (!v.isNull())
    {
      if (v.isVar())
      {
        v_b[v] = m.second.isNull() ? d_one : m.second;
        vs.insert(v);
      }
      else if (v.getKind() == NONLINEAR_MULT && v.getNumChildren() == 2
               && v[0] == v[1] && v[0].isVar())
      {
        v_a[v[0]] = m.second.isNull() ? d_one : m.second;
        vs.insert(v[0]);
      }
      else
      {
        vs_invalid.push_back(v);
      }
    }
  }
  // solve the valid variables...
  Node invalid_vsum = vs_invalid.empty() ? d_zero
                                         : (vs_invalid.size() == 1
                                                ? vs_invalid[0]
                                                : nm->mkNode(PLUS, vs_invalid));
  // substitution to try
  std::vector<Node> qvars;
  std::vector<Node> qsubs;
  for (const Node& v : vs)
  {
    // is it a valid variable?
    std::map<Node, std::pair<Node, Node>>::iterator bit =
        d_check_model_bounds.find(v);
    if (!expr::hasSubterm(invalid_vsum, v) && bit != d_check_model_bounds.end())
    {
      std::map<Node, Node>::iterator it = v_a.find(v);
      if (it != v_a.end())
      {
        Node a = it->second;
        Assert(a.isConst());
        int asgn = a.getConst<Rational>().sgn();
        Assert(asgn != 0);
        Node t = nm->mkNode(MULT, a, v, v);
        Node b = d_zero;
        it = v_b.find(v);
        if (it != v_b.end())
        {
          b = it->second;
          t = nm->mkNode(PLUS, t, nm->mkNode(MULT, b, v));
        }
        t = Rewriter::rewrite(t);
        Trace("nl-ext-cms-debug") << "Trying to find min/max for quadratic "
                                  << t << "..." << std::endl;
        Trace("nl-ext-cms-debug") << "    a = " << a << std::endl;
        Trace("nl-ext-cms-debug") << "    b = " << b << std::endl;
        // find maximal/minimal value on the interval
        Node apex = nm->mkNode(
            DIVISION, nm->mkNode(UMINUS, b), nm->mkNode(MULT, d_two, a));
        apex = Rewriter::rewrite(apex);
        Assert(apex.isConst());
        // for lower, upper, whether we are greater than the apex
        bool cmp[2];
        Node boundn[2];
        for (unsigned r = 0; r < 2; r++)
        {
          boundn[r] = r == 0 ? bit->second.first : bit->second.second;
          Node cmpn = nm->mkNode(GT, boundn[r], apex);
          cmpn = Rewriter::rewrite(cmpn);
          Assert(cmpn.isConst());
          cmp[r] = cmpn.getConst<bool>();
        }
        Trace("nl-ext-cms-debug") << "  apex " << apex << std::endl;
        Trace("nl-ext-cms-debug")
            << "  lower " << boundn[0] << ", cmp: " << cmp[0] << std::endl;
        Trace("nl-ext-cms-debug")
            << "  upper " << boundn[1] << ", cmp: " << cmp[1] << std::endl;
        Assert(boundn[0].getConst<Rational>()
               <= boundn[1].getConst<Rational>());
        Node s;
        qvars.push_back(v);
        if (cmp[0] != cmp[1])
        {
          Assert(!cmp[0] && cmp[1]);
          // does the sign match the bound?
          if ((asgn == 1) == pol)
          {
            // the apex is the max/min value
            s = apex;
            Trace("nl-ext-cms-debug") << "  ...set to apex." << std::endl;
          }
          else
          {
            // it is one of the endpoints, plug in and compare
            Node tcmpn[2];
            for (unsigned r = 0; r < 2; r++)
            {
              qsubs.push_back(boundn[r]);
              Node ts = arithSubstitute(t, qvars, qsubs);
              tcmpn[r] = Rewriter::rewrite(ts);
              qsubs.pop_back();
            }
            Node tcmp = nm->mkNode(LT, tcmpn[0], tcmpn[1]);
            Trace("nl-ext-cms-debug")
                << "  ...both sides of apex, compare " << tcmp << std::endl;
            tcmp = Rewriter::rewrite(tcmp);
            Assert(tcmp.isConst());
            unsigned bindex_use = (tcmp.getConst<bool>() == pol) ? 1 : 0;
            Trace("nl-ext-cms-debug")
                << "  ...set to " << (bindex_use == 1 ? "upper" : "lower")
                << std::endl;
            s = boundn[bindex_use];
          }
        }
        else
        {
          // both to one side of the apex
          // we figure out which bound to use (lower or upper) based on
          // three factors:
          // (1) whether a's sign is positive,
          // (2) whether we are greater than the apex of the parabola,
          // (3) the polarity of the constraint, i.e. >= or <=.
          // there are 8 cases of these factors, which we test here.
          unsigned bindex_use = (((asgn == 1) == cmp[0]) == pol) ? 0 : 1;
          Trace("nl-ext-cms-debug")
              << "  ...set to " << (bindex_use == 1 ? "upper" : "lower")
              << std::endl;
          s = boundn[bindex_use];
        }
        Assert(!s.isNull());
        qsubs.push_back(s);
        Trace("nl-ext-cms") << "* set bound based on quadratic : " << v
                            << " -> " << s << std::endl;
      }
    }
  }
  if (!qvars.empty())
  {
    Assert(qvars.size() == qsubs.size());
    Node slit = arithSubstitute(lit, qvars, qsubs);
    slit = Rewriter::rewrite(slit);
    return simpleCheckModelLit(slit);
  }
  return false;
}

bool NlModel::simpleCheckModelMsum(const std::map<Node, Node>& msum, bool pol)
{
  Trace("nl-ext-cms-debug") << "* Try simple interval analysis..." << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  // map from transcendental functions to whether they were set to lower
  // bound
  bool simpleSuccess = true;
  std::map<Node, bool> set_bound;
  std::vector<Node> sum_bound;
  for (const std::pair<const Node, Node>& m : msum)
  {
    Node v = m.first;
    if (v.isNull())
    {
      sum_bound.push_back(m.second.isNull() ? d_one : m.second);
    }
    else
    {
      Trace("nl-ext-cms-debug") << "- monomial : " << v << std::endl;
      // --- whether we should set a lower bound for this monomial
      bool set_lower =
          (m.second.isNull() || m.second.getConst<Rational>().sgn() == 1)
          == pol;
      Trace("nl-ext-cms-debug")
          << "set bound to " << (set_lower ? "lower" : "upper") << std::endl;

      // --- Collect variables and factors in v
      std::vector<Node> vars;
      std::vector<unsigned> factors;
      if (v.getKind() == NONLINEAR_MULT)
      {
        unsigned last_start = 0;
        for (unsigned i = 0, nchildren = v.getNumChildren(); i < nchildren; i++)
        {
          // are we at the end?
          if (i + 1 == nchildren || v[i + 1] != v[i])
          {
            unsigned vfact = 1 + (i - last_start);
            last_start = (i + 1);
            vars.push_back(v[i]);
            factors.push_back(vfact);
          }
        }
      }
      else
      {
        vars.push_back(v);
        factors.push_back(1);
      }

      // --- Get the lower and upper bounds and sign information.
      // Whether we have an (odd) number of negative factors in vars, apart
      // from the variable at choose_index.
      bool has_neg_factor = false;
      int choose_index = -1;
      std::vector<Node> ls;
      std::vector<Node> us;
      // the relevant sign information for variables with odd exponents:
      //   1: both signs of the interval of this variable are positive,
      //  -1: both signs of the interval of this variable are negative.
      std::vector<int> signs;
      Trace("nl-ext-cms-debug") << "get sign information..." << std::endl;
      for (unsigned i = 0, size = vars.size(); i < size; i++)
      {
        Node vc = vars[i];
        unsigned vcfact = factors[i];
        if (Trace.isOn("nl-ext-cms-debug"))
        {
          Trace("nl-ext-cms-debug") << "-- " << vc;
          if (vcfact > 1)
          {
            Trace("nl-ext-cms-debug") << "^" << vcfact;
          }
          Trace("nl-ext-cms-debug") << " ";
        }
        std::map<Node, std::pair<Node, Node>>::iterator bit =
            d_check_model_bounds.find(vc);
        // if there is a model bound for this term
        if (bit != d_check_model_bounds.end())
        {
          Node l = bit->second.first;
          Node u = bit->second.second;
          ls.push_back(l);
          us.push_back(u);
          int vsign = 0;
          if (vcfact % 2 == 1)
          {
            vsign = 1;
            int lsgn = l.getConst<Rational>().sgn();
            int usgn = u.getConst<Rational>().sgn();
            Trace("nl-ext-cms-debug")
                << "bound_sign(" << lsgn << "," << usgn << ") ";
            if (lsgn == -1)
            {
              if (usgn < 1)
              {
                // must have a negative factor
                has_neg_factor = !has_neg_factor;
                vsign = -1;
              }
              else if (choose_index == -1)
              {
                // set the choose index to this
                choose_index = i;
                vsign = 0;
              }
              else
              {
                // ambiguous, can't determine the bound
                Trace("nl-ext-cms")
                    << "  failed due to ambiguious monomial." << std::endl;
                return false;
              }
            }
          }
          Trace("nl-ext-cms-debug") << " -> " << vsign << std::endl;
          signs.push_back(vsign);
        }
        else
        {
          Trace("nl-ext-cms-debug") << std::endl;
          Trace("nl-ext-cms")
              << "  failed due to unknown bound for " << vc << std::endl;
          // should either assign a model bound or eliminate the variable
          // via substitution
          Assert(false);
          return false;
        }
      }
      // whether we will try to minimize/maximize (-1/1) the absolute value
      int setAbs = (set_lower == has_neg_factor) ? 1 : -1;
      Trace("nl-ext-cms-debug")
          << "set absolute value to " << (setAbs == 1 ? "maximal" : "minimal")
          << std::endl;

      std::vector<Node> vbs;
      Trace("nl-ext-cms-debug") << "set bounds..." << std::endl;
      for (unsigned i = 0, size = vars.size(); i < size; i++)
      {
        Node vc = vars[i];
        unsigned vcfact = factors[i];
        Node l = ls[i];
        Node u = us[i];
        bool vc_set_lower;
        int vcsign = signs[i];
        Trace("nl-ext-cms-debug")
            << "Bounds for " << vc << " : " << l << ", " << u
            << ", sign : " << vcsign << ", factor : " << vcfact << std::endl;
        if (l == u)
        {
          // by convention, always say it is lower if they are the same
          vc_set_lower = true;
          Trace("nl-ext-cms-debug")
              << "..." << vc << " equal bound, set to lower" << std::endl;
        }
        else
        {
          if (vcfact % 2 == 0)
          {
            // minimize or maximize its absolute value
            Rational la = l.getConst<Rational>().abs();
            Rational ua = u.getConst<Rational>().abs();
            if (la == ua)
            {
              // by convention, always say it is lower if abs are the same
              vc_set_lower = true;
              Trace("nl-ext-cms-debug")
                  << "..." << vc << " equal abs, set to lower" << std::endl;
            }
            else
            {
              vc_set_lower = (la > ua) == (setAbs == 1);
            }
          }
          else if (signs[i] == 0)
          {
            // we choose this index to match the overall set_lower
            vc_set_lower = set_lower;
          }
          else
          {
            vc_set_lower = (signs[i] != setAbs);
          }
          Trace("nl-ext-cms-debug")
              << "..." << vc << " set to " << (vc_set_lower ? "lower" : "upper")
              << std::endl;
        }
        // check whether this is a conflicting bound
        std::map<Node, bool>::iterator itsb = set_bound.find(vc);
        if (itsb == set_bound.end())
        {
          set_bound[vc] = vc_set_lower;
        }
        else if (itsb->second != vc_set_lower)
        {
          Trace("nl-ext-cms")
              << "  failed due to conflicting bound for " << vc << std::endl;
          return false;
        }
        // must over/under approximate based on vc_set_lower, computed above
        Node vb = vc_set_lower ? l : u;
        for (unsigned i2 = 0; i2 < vcfact; i2++)
        {
          vbs.push_back(vb);
        }
      }
      if (!simpleSuccess)
      {
        break;
      }
      Node vbound = vbs.size() == 1 ? vbs[0] : nm->mkNode(MULT, vbs);
      sum_bound.push_back(ArithMSum::mkCoeffTerm(m.second, vbound));
    }
  }
  // if the exact bound was computed via simple analysis above
  // make the bound
  Node bound;
  if (sum_bound.size() > 1)
  {
    bound = nm->mkNode(kind::PLUS, sum_bound);
  }
  else if (sum_bound.size() == 1)
  {
    bound = sum_bound[0];
  }
  else
  {
    bound = d_zero;
  }
  // make the comparison
  Node comp = nm->mkNode(kind::GEQ, bound, d_zero);
  if (!pol)
  {
    comp = comp.negate();
  }
  Trace("nl-ext-cms") << "  comparison is : " << comp << std::endl;
  comp = Rewriter::rewrite(comp);
  Assert(comp.isConst());
  Trace("nl-ext-cms") << "  returned : " << comp << std::endl;
  return comp == d_true;
}

bool NlModel::getApproximateSqrt(Node c, Node& l, Node& u, unsigned iter) const
{
  Assert(c.isConst());
  if (c == d_one || c == d_zero)
  {
    l = c;
    u = c;
    return true;
  }
  Rational rc = c.getConst<Rational>();

  Rational rl = rc < Rational(1) ? rc : Rational(1);
  Rational ru = rc < Rational(1) ? Rational(1) : rc;
  unsigned count = 0;
  Rational half = Rational(1) / Rational(2);
  while (count < iter)
  {
    Rational curr = half * (rl + ru);
    Rational curr_sq = curr * curr;
    if (curr_sq == rc)
    {
      rl = curr;
      ru = curr;
      break;
    }
    else if (curr_sq < rc)
    {
      rl = curr;
    }
    else
    {
      ru = curr;
    }
    count++;
  }

  NodeManager* nm = NodeManager::currentNM();
  l = nm->mkConst(rl);
  u = nm->mkConst(ru);
  return true;
}

void NlModel::printModelValue(const char* c, Node n, unsigned prec) const
{
  if (Trace.isOn(c))
  {
    Trace(c) << "  " << n << " -> ";
    for (int i = 1; i >= 0; --i)
    {
      std::map<Node, Node>::const_iterator it = d_mv[i].find(n);
      Assert(it != d_mv[i].end());
      if (it->second.isConst())
      {
        printRationalApprox(c, it->second, prec);
      }
      else
      {
        Trace(c) << "?";
      }
      Trace(c) << (i == 1 ? " [actual: " : " ]");
    }
    Trace(c) << std::endl;
  }
}

void NlModel::getModelValueRepair(
    std::map<Node, Node>& arithModel,
    std::map<Node, std::pair<Node, Node>>& approximations)
{
  Trace("nl-model") << "NlModel::getModelValueRepair:" << std::endl;

  // Record the approximations we used. This code calls the
  // recordApproximation method of the model, which overrides the model
  // values for variables that we solved for, using techniques specific to
  // this class.
  NodeManager* nm = NodeManager::currentNM();
  for (const std::pair<const Node, std::pair<Node, Node>>& cb :
       d_check_model_bounds)
  {
    Node l = cb.second.first;
    Node u = cb.second.second;
    Node pred;
    Node v = cb.first;
    if (l != u)
    {
      pred = nm->mkNode(AND, nm->mkNode(GEQ, v, l), nm->mkNode(GEQ, u, v));
      Trace("nl-model") << v << " approximated as " << pred << std::endl;
      Node witness;
      if (options::modelWitnessValue())
      {
        // witness is the midpoint
        witness = nm->mkNode(
            MULT, nm->mkConst(Rational(1, 2)), nm->mkNode(PLUS, l, u));
        witness = Rewriter::rewrite(witness);
        Trace("nl-model") << v << " witness is " << witness << std::endl;
      }
      approximations[v] = std::pair<Node, Node>(pred, witness);
    }
    else
    {
      // overwrite
      arithModel[v] = l;
      Trace("nl-model") << v << " exact approximation is " << l << std::endl;
    }
  }
  // Also record the exact values we used. An exact value can be seen as a
  // special kind approximation of the form (witness x. x = exact_value).
  // Notice that the above term gets rewritten such that the choice function
  // is eliminated.
  for (size_t i = 0, num = d_check_model_vars.size(); i < num; i++)
  {
    Node v = d_check_model_vars[i];
    Node s = d_check_model_subs[i];
    // overwrite
    arithModel[v] = s;
    Trace("nl-model") << v << " solved is " << s << std::endl;
  }

  // multiplication terms should not be given values; their values are
  // implied by the monomials that they consist of
  std::vector<Node> amErase;
  for (const std::pair<const Node, Node>& am : arithModel)
  {
    if (am.first.getKind() == NONLINEAR_MULT)
    {
      amErase.push_back(am.first);
    }
  }
  for (const Node& ae : amErase)
  {
    arithModel.erase(ae);
  }
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4
