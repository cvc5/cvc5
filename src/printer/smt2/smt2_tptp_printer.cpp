/*
Read model content
Build finite domain view of each uninterpreted sort
For each uninterpreted sort S, create:
- a TPTP type symbol "s"
- a finite domain carrier type "d_s"
- a promotion function "d2s : d_s > s"
Domain axioms per sort: surjectivity onto original sort, finite enumeration, distinctness of domain elements, injectivity of promotion function.
Interpretation from model values
*/

#include "printer/smt2/smt2_tptp_printer.h"

#include <algorithm>
#include <cctype>
#include <cstddef>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

#include "expr/node.h"
#include "expr/type_node.h"
#include "smt/model.h"
#include "theory/evaluator.h"
#include "theory/uf/function_const.h"

namespace cvc5::internal {
namespace printer {
namespace smt2 {

namespace {

std::string stripLeadingTptpPrefix(const std::string& in)
{
  const std::string dotPrefix = "tptp.";
  const std::string usPrefix = "tptp_";
  if (in.rfind(dotPrefix, 0) == 0)
  {
    return in.substr(dotPrefix.size());
  }
  if (in.rfind(usPrefix, 0) == 0)
  {
    return in.substr(usPrefix.size());
  }
  return in;
}

std::string stripPath(const std::string& in)
{
  size_t p = in.find_last_of("/\\");
  if (p == std::string::npos)
  {
    return in;
  }
  return in.substr(p + 1);
}

// Convert solver symbols to TPTP lowercase identifiers.
std::string sanitizeLower(const std::string& in)
{
  const std::string normalized = stripLeadingTptpPrefix(in);
  std::string out;
  out.reserve(normalized.size() + 4);
  bool prevUnderscore = false;
  for (char c : normalized)
  {
    char next = '_';
    if (std::isalnum(static_cast<unsigned char>(c)) || c == '_')
    {
      next = static_cast<char>(std::tolower(static_cast<unsigned char>(c)));
    }
    if (next == '_')
    {
      if (prevUnderscore)
      {
        continue;
      }
      prevUnderscore = true;
    }
    else
    {
      prevUnderscore = false;
    }
    out.push_back(next);
  }
  // Remove leading/trailing underscores introduced by normalization.
  while (!out.empty() && out.front() == '_')
  {
    out.erase(out.begin());
  }
  while (!out.empty() && out.back() == '_')
  {
    out.pop_back();
  }
  // TPTP lower-word symbols must begin with a lowercase letter.
  if (out.empty()
      || !std::isalpha(static_cast<unsigned char>(out[0]))
      || std::isupper(static_cast<unsigned char>(out[0])))
  {
    out = "x" + out;
  }
  return out;
}

std::string sanitizeUpper(const std::string& in)
{
  std::string out = sanitizeLower(in);
  out[0] = static_cast<char>(std::toupper(static_cast<unsigned char>(out[0])));
  return out;
}

std::string join(const std::vector<std::string>& xs, const std::string& sep);

void printTypeDecl(std::ostream& out,
                   const char* ff,
                   const std::string& id,
                   const std::string& symbol,
                   const std::string& type)
{
  out << ff << "(" << id << ",type,\n";
  out << "    " << symbol << ": " << type << " ).\n\n";
}

bool isBuiltinIndividualSort(TypeNode tn)
{
  if (!tn.isUninterpretedSort())
  {
    return false;
  }
  // TPTP's builtin individual type $i is represented internally as
  // the default unsorted uninterpreted sort.
  return sanitizeLower(tn.toString()) == "unsorted";
}

std::string typeToTptp(TypeNode tn, bool useThfTuple = false)
{
  if (tn.isBoolean())
  {
    return "$o";
  }
  if (tn.isInteger())
  {
    return "$int";
  }
  if (tn.isReal())
  {
    return "$real";
  }
  if (isBuiltinIndividualSort(tn))
  {
    return "$i";
  }
  if (tn.isFunction())
  {
    std::vector<TypeNode> args = tn.getArgTypes();
    std::vector<std::string> argStrs;
    argStrs.reserve(args.size());
    for (const TypeNode& at : args)
    {
      std::string atStr = typeToTptp(at, useThfTuple);
      if (at.isFunction())
      {
        atStr = "( " + atStr + " )";
      }
      argStrs.push_back(atStr);
    }
    std::string r = typeToTptp(tn.getRangeType(), useThfTuple);
    if (args.size() == 1)
    {
      return argStrs[0] + " > " + r;
    }
    if (useThfTuple)
    {
      // THF: prefer curried arrows for n-ary functions to avoid legacy
      // product types and tuple-argument application mismatches.
      std::vector<std::string> chain = argStrs;
      chain.push_back(r);
      return join(chain, " > ");
    }
    return "( " + join(argStrs, " * ") + " ) > " + r;
  }
  return sanitizeLower(tn.toString());
}

std::string join(const std::vector<std::string>& xs, const std::string& sep)
{
  std::stringstream ss;
  for (size_t i = 0, n = xs.size(); i < n; i++)
  {
    if (i > 0)
    {
      ss << sep;
    }
    ss << xs[i];
  }
  return ss.str();
}

std::string mkApplyString(const std::string& op,
                          const std::vector<std::string>& args,
                          bool useThf)
{
  if (args.empty())
  {
    return op;
  }
  if (useThf)
  {
    std::string cur = op;
    for (const std::string& a : args)
    {
      cur = "(" + cur + " @ " + a + ")";
    }
    return cur;
  }
  return op + "(" + join(args, ",") + ")";
}

void cartesianProduct(const std::vector<std::vector<Node>>& doms,
                      size_t index,
                      std::vector<Node>& current,
                      std::vector<std::vector<Node>>& out)
{
  if (index == doms.size())
  {
    out.push_back(current);
    return;
  }
  for (const Node& e : doms[index])
  {
    current[index] = e;
    cartesianProduct(doms, index + 1, current, out);
  }
}

bool typeUsesSort(TypeNode type, TypeNode sort)
{
  if (type == sort)
  {
    return true;
  }
  if (!type.isFunction())
  {
    return false;
  }
  for (const TypeNode& at : type.getArgTypes())
  {
    if (typeUsesSort(at, sort))
    {
      return true;
    }
  }
  return typeUsesSort(type.getRangeType(), sort);
}

bool isHigherOrderType(TypeNode tn)
{
  if (!tn.isFunction())
  {
    return false;
  }
  for (const TypeNode& at : tn.getArgTypes())
  {
    if (at.isFunction())
    {
      return true;
    }
  }
  return tn.getRangeType().isFunction();
}

bool hasFunctionArgType(TypeNode tn)
{
  if (!tn.isFunction())
  {
    return false;
  }
  for (const TypeNode& at : tn.getArgTypes())
  {
    if (at.isFunction())
    {
      return true;
    }
  }
  return false;
}

void collectFunctionTypes(Node n, std::set<TypeNode>& out)
{
  std::vector<Node> visit;
  std::set<Node> seen;
  visit.push_back(n);
  while (!visit.empty())
  {
    Node cur = visit.back();
    visit.pop_back();
    if (seen.find(cur) != seen.end())
    {
      continue;
    }
    seen.insert(cur);
    TypeNode tn = cur.getType();
    if (tn.isFunction())
    {
      out.insert(tn);
    }
    for (const Node& c : cur)
    {
      visit.push_back(c);
    }
  }
}

size_t boundedPow(size_t base, size_t exp, size_t bound, bool& ok)
{
  ok = true;
  size_t acc = 1;
  for (size_t i = 0; i < exp; i++)
  {
    if (base != 0 && acc > bound / base)
    {
      ok = false;
      return bound + 1;
    }
    acc *= base;
    if (acc > bound)
    {
      ok = false;
      return acc;
    }
  }
  return acc;
}

Node mkTupleCondition(NodeManager* nm,
                      const std::vector<Node>& vars,
                      const std::vector<Node>& tup)
{
  Assert(vars.size() == tup.size());
  if (vars.empty())
  {
    return nm->mkConst(true);
  }
  if (vars.size() == 1)
  {
    return nm->mkNode(Kind::EQUAL, vars[0], tup[0]);
  }
  std::vector<Node> conj;
  conj.reserve(vars.size());
  for (size_t i = 0, n = vars.size(); i < n; i++)
  {
    conj.push_back(nm->mkNode(Kind::EQUAL, vars[i], tup[i]));
  }
  return nm->mkNode(Kind::AND, conj);
}

bool getFiniteDomainValues(TypeNode tn,
                           NodeManager* nm,
                           const std::map<TypeNode, std::vector<Node>>& baseElems,
                           std::map<TypeNode, std::vector<Node>>& cache,
                           size_t maxFuncSpace)
{
  if (cache.find(tn) != cache.end())
  {
    return true;
  }
  std::vector<Node> vals;
  if (tn.isBoolean())
  {
    vals.push_back(nm->mkConst(true));
    vals.push_back(nm->mkConst(false));
    cache[tn] = vals;
    return true;
  }
  if (tn.isUninterpretedSort())
  {
    auto it = baseElems.find(tn);
    if (it == baseElems.end())
    {
      return false;
    }
    cache[tn] = it->second;
    return true;
  }
  if (!tn.isFunction())
  {
    return false;
  }

  std::vector<TypeNode> argTypes = tn.getArgTypes();
  std::vector<std::vector<Node>> argDomains;
  argDomains.reserve(argTypes.size());
  for (const TypeNode& at : argTypes)
  {
    if (!getFiniteDomainValues(at, nm, baseElems, cache, maxFuncSpace))
    {
      return false;
    }
    const std::vector<Node>& ad = cache[at];
    if (ad.empty())
    {
      return false;
    }
    argDomains.push_back(ad);
  }
  if (!getFiniteDomainValues(tn.getRangeType(), nm, baseElems, cache, maxFuncSpace))
  {
    return false;
  }
  const std::vector<Node>& rangeVals = cache[tn.getRangeType()];
  if (rangeVals.empty())
  {
    return false;
  }

  size_t tupleCount = 1;
  for (const std::vector<Node>& d : argDomains)
  {
    if (!d.empty() && tupleCount > maxFuncSpace / d.size())
    {
      return false;
    }
    tupleCount *= d.size();
  }
  bool okPow = false;
  size_t funcCount = boundedPow(rangeVals.size(), tupleCount, maxFuncSpace, okPow);
  if (!okPow || funcCount == 0)
  {
    return false;
  }

  std::vector<std::vector<Node>> tuples;
  std::vector<Node> current(argTypes.size());
  cartesianProduct(argDomains, 0, current, tuples);
  Assert(tuples.size() == tupleCount);

  std::vector<Node> bvs;
  bvs.reserve(argTypes.size());
  for (size_t i = 0, n = argTypes.size(); i < n; i++)
  {
    std::stringstream ss;
    ss << "A" << i;
    bvs.push_back(nm->mkBoundVar(ss.str(), argTypes[i]));
  }
  Node bvl = nm->mkNode(Kind::BOUND_VAR_LIST, bvs);

  vals.reserve(funcCount);
  for (size_t fid = 0; fid < funcCount; fid++)
  {
    size_t code = fid;
    std::vector<Node> outs(tupleCount);
    for (size_t i = 0; i < tupleCount; i++)
    {
      outs[i] = rangeVals[code % rangeVals.size()];
      code /= rangeVals.size();
    }
    Node body = outs.back();
    for (size_t i = tupleCount; i > 1; i--)
    {
      Node cond = mkTupleCondition(nm, bvs, tuples[i - 2]);
      body = nm->mkNode(Kind::ITE, cond, outs[i - 2], body);
    }
    vals.push_back(nm->mkNode(Kind::LAMBDA, bvl, body));
  }
  cache[tn] = vals;
  return true;
}

bool tryGetModelValue(const smt::Model& m,
                      const std::map<Node, bool>& isDeclared,
                      Node n,
                      Node& value)
{
  (void)isDeclared;
  value = m.getValueOrNull(n);
  return !value.isNull();
}

Node resolveModelValue(const smt::Model& m,
                       const std::map<Node, bool>& isDeclared,
                       Node n)
{
  Node cur = n;
  for (size_t i = 0; i < 8; i++)
  {
    Node v;
    if (!tryGetModelValue(m, isDeclared, cur, v))
    {
      return Node::null();
    }
    cur = v;
    if (cur.isConst() || isDeclared.find(cur) == isDeclared.end())
    {
      return cur;
    }
  }
  return cur;
}

Node evaluateAppValue(const smt::Model& m,
                      const std::map<Node, bool>& isDeclared,
                      Node fun,
                      const std::vector<Node>& args)
{
  Node fval = resolveModelValue(m, isDeclared, fun);
  if (fval.isNull())
  {
    return Node::null();
  }
  Node lam = theory::uf::FunctionConst::toLambda(fval);
  if (lam.isNull() || lam.getKind() != Kind::LAMBDA)
  {
    return Node::null();
  }
  Node bvl = lam[0];
  if (bvl.getNumChildren() != args.size())
  {
    return Node::null();
  }
  std::vector<Node> vars;
  vars.reserve(args.size());
  for (const Node& v : bvl)
  {
    vars.push_back(v);
  }
  theory::Evaluator ev(nullptr);
  return ev.eval(lam[1], vars, args);
}

bool getTypeDomainValues(TypeNode tn,
                         const std::map<TypeNode, std::vector<Node>>& finiteTypeElems,
                         std::vector<Node>& vals)
{
  vals.clear();
  if (tn.isBoolean())
  {
    NodeManager* nm = tn.getNodeManager();
    vals.push_back(nm->mkConst(true));
    vals.push_back(nm->mkConst(false));
    return true;
  }
  auto it = finiteTypeElems.find(tn);
  if (it == finiteTypeElems.end() || it->second.empty())
  {
    return false;
  }
  vals = it->second;
  return true;
}

Node evalFiniteTerm(const Node& n,
                    const smt::Model& m,
                    const std::map<Node, bool>& isDeclared,
                    const std::map<TypeNode, std::vector<Node>>& finiteTypeElems,
                    const std::map<Node, Node>& subst);

Node evalFiniteApply(const Node& app,
                     const smt::Model& m,
                     const std::map<Node, bool>& isDeclared,
                     const std::map<TypeNode, std::vector<Node>>& finiteTypeElems,
                     const std::map<Node, Node>& subst)
{
  if (app.getNumChildren() == 0)
  {
    return Node::null();
  }
  Node op = evalFiniteTerm(app[0], m, isDeclared, finiteTypeElems, subst);
  if (op.isNull())
  {
    return Node::null();
  }
  std::vector<Node> args;
  args.reserve(app.getNumChildren() - 1);
  for (size_t i = 1, n = app.getNumChildren(); i < n; i++)
  {
    Node av = evalFiniteTerm(app[i], m, isDeclared, finiteTypeElems, subst);
    if (av.isNull())
    {
      return Node::null();
    }
    args.push_back(av);
  }
  // Prefer direct model query for instantiated applications.
  Node qval = Node::null();
  if (app.getKind() == Kind::APPLY_UF)
  {
    if (app[0].getType().isFunction())
    {
      std::vector<Node> qchildren;
      qchildren.reserve(app.getNumChildren());
      qchildren.push_back(app[0]);
      for (const Node& a : args)
      {
        qchildren.push_back(a);
      }
      Node qapp = app.getNodeManager()->mkNode(Kind::APPLY_UF, qchildren);
      qval = m.getValueOrNull(qapp);
    }
  }
  else if (app.getKind() == Kind::HO_APPLY)
  {
    Node qop = app[0];
    auto qit = subst.find(qop);
    if (qit != subst.end())
    {
      qop = qit->second;
    }
    if (qop.getType().isFunction())
    {
      std::vector<Node> qchildren;
      qchildren.reserve(app.getNumChildren());
      qchildren.push_back(qop);
      for (const Node& a : args)
      {
        qchildren.push_back(a);
      }
      Node qapp = app.getNodeManager()->mkNode(Kind::HO_APPLY, qchildren);
      qval = m.getValueOrNull(qapp);
    }
  }
  if (!qval.isNull())
  {
    return qval;
  }
  Node lam = theory::uf::FunctionConst::toLambda(op);
  if (lam.isNull() || lam.getKind() != Kind::LAMBDA)
  {
    // Try declared-model lookup for function symbols.
    Node lv = resolveModelValue(m, isDeclared, op);
    lam = theory::uf::FunctionConst::toLambda(lv);
    if (lam.isNull() || lam.getKind() != Kind::LAMBDA)
    {
      return Node::null();
    }
  }
  Node bvl = lam[0];
  if (bvl.getNumChildren() < args.size())
  {
    return Node::null();
  }
  std::vector<Node> svars;
  svars.reserve(args.size());
  for (size_t i = 0, n = args.size(); i < n; i++)
  {
    svars.push_back(bvl[i]);
  }
  Node bodySub = lam[1].substitute(svars.begin(), svars.end(), args.begin(), args.end());
  if (bvl.getNumChildren() == args.size())
  {
    return evalFiniteTerm(bodySub, m, isDeclared, finiteTypeElems, subst);
  }
  std::vector<Node> rbvs;
  for (size_t i = args.size(), n = bvl.getNumChildren(); i < n; i++)
  {
    rbvs.push_back(bvl[i]);
  }
  Node rbvl = app.getNodeManager()->mkNode(Kind::BOUND_VAR_LIST, rbvs);
  return app.getNodeManager()->mkNode(Kind::LAMBDA, rbvl, bodySub);
}

Node evalFiniteQuant(const Node& q,
                     bool isForall,
                     const smt::Model& m,
                     const std::map<Node, bool>& isDeclared,
                     const std::map<TypeNode, std::vector<Node>>& finiteTypeElems,
                     const std::map<Node, Node>& subst)
{
  Node bvl = q[0];
  Node body = q[1];
  std::vector<std::vector<Node>> domains;
  domains.reserve(bvl.getNumChildren());
  for (size_t i = 0, n = bvl.getNumChildren(); i < n; i++)
  {
    std::vector<Node> d;
    if (!getTypeDomainValues(bvl[i].getType(), finiteTypeElems, d))
    {
      return Node::null();
    }
    domains.push_back(d);
  }
  std::vector<std::vector<Node>> tuples;
  std::vector<Node> current(bvl.getNumChildren());
  cartesianProduct(domains, 0, current, tuples);
  NodeManager* nm = q.getNodeManager();
  for (const std::vector<Node>& tup : tuples)
  {
    std::map<Node, Node> nsubst = subst;
    for (size_t i = 0, n = tup.size(); i < n; i++)
    {
      nsubst[bvl[i]] = tup[i];
    }
    Node bv = evalFiniteTerm(body, m, isDeclared, finiteTypeElems, nsubst);
    if (bv.isNull() || bv.getKind() != Kind::CONST_BOOLEAN)
    {
      return Node::null();
    }
    const bool b = bv.getConst<bool>();
    if (isForall && !b)
    {
      return nm->mkConst(false);
    }
    if (!isForall && b)
    {
      return nm->mkConst(true);
    }
  }
  return nm->mkConst(isForall);
}

Node evalFiniteTerm(const Node& n,
                    const smt::Model& m,
                    const std::map<Node, bool>& isDeclared,
                    const std::map<TypeNode, std::vector<Node>>& finiteTypeElems,
                    const std::map<Node, Node>& subst)
{
  auto sit = subst.find(n);
  if (sit != subst.end())
  {
    return sit->second;
  }
  if (n.isConst())
  {
    return n;
  }
  if (n.getKind() == Kind::APPLY_UF || n.getKind() == Kind::HO_APPLY)
  {
    return evalFiniteApply(n, m, isDeclared, finiteTypeElems, subst);
  }
  if (n.getKind() == Kind::FORALL)
  {
    return evalFiniteQuant(n, true, m, isDeclared, finiteTypeElems, subst);
  }
  if (n.getKind() == Kind::EXISTS)
  {
    return evalFiniteQuant(n, false, m, isDeclared, finiteTypeElems, subst);
  }
  if (n.getKind() == Kind::NOT)
  {
    Node c = evalFiniteTerm(n[0], m, isDeclared, finiteTypeElems, subst);
    if (c.isNull() || c.getKind() != Kind::CONST_BOOLEAN)
    {
      return Node::null();
    }
    return n.getNodeManager()->mkConst(!c.getConst<bool>());
  }
  if (n.getKind() == Kind::AND || n.getKind() == Kind::OR)
  {
    const bool isAnd = n.getKind() == Kind::AND;
    bool acc = isAnd;
    for (size_t i = 0, nc = n.getNumChildren(); i < nc; i++)
    {
      Node c = evalFiniteTerm(n[i], m, isDeclared, finiteTypeElems, subst);
      if (c.isNull() || c.getKind() != Kind::CONST_BOOLEAN)
      {
        return Node::null();
      }
      bool b = c.getConst<bool>();
      if (isAnd)
      {
        acc = acc && b;
        if (!acc)
        {
          break;
        }
      }
      else
      {
        acc = acc || b;
        if (acc)
        {
          break;
        }
      }
    }
    return n.getNodeManager()->mkConst(acc);
  }
  if (n.getKind() == Kind::IMPLIES)
  {
    Node a = evalFiniteTerm(n[0], m, isDeclared, finiteTypeElems, subst);
    Node b = evalFiniteTerm(n[1], m, isDeclared, finiteTypeElems, subst);
    if (a.isNull() || b.isNull() || a.getKind() != Kind::CONST_BOOLEAN
        || b.getKind() != Kind::CONST_BOOLEAN)
    {
      return Node::null();
    }
    return n.getNodeManager()->mkConst(!a.getConst<bool>() || b.getConst<bool>());
  }
  if (n.getKind() == Kind::ITE)
  {
    Node c = evalFiniteTerm(n[0], m, isDeclared, finiteTypeElems, subst);
    if (c.isNull() || c.getKind() != Kind::CONST_BOOLEAN)
    {
      return Node::null();
    }
    return evalFiniteTerm(
        c.getConst<bool>() ? n[1] : n[2], m, isDeclared, finiteTypeElems, subst);
  }
  if (n.getKind() == Kind::EQUAL)
  {
    Node a = evalFiniteTerm(n[0], m, isDeclared, finiteTypeElems, subst);
    Node b = evalFiniteTerm(n[1], m, isDeclared, finiteTypeElems, subst);
    if (a.isNull() || b.isNull())
    {
      return Node::null();
    }
    return n.getNodeManager()->mkConst(a == b);
  }
  // fall back to declared-model lookup for unresolved symbols/aliases
  if (isDeclared.find(n) != isDeclared.end())
  {
    return resolveModelValue(m, isDeclared, n);
  }
  return Node::null();
}

std::string resolveElemName(const smt::Model& m,
                            const std::map<Node, bool>& isDeclared,
                            Node value,
                            const std::map<Node, std::string>& elemNames)
{
  Node v = value;
  if (isDeclared.find(v) != isDeclared.end())
  {
    v = resolveModelValue(m, isDeclared, v);
  }
  if (v.isNull())
  {
    return "";
  }
  auto it = elemNames.find(v);
  if (it != elemNames.end())
  {
    return it->second;
  }
  return "";
}

bool getBoolValueFinite(const smt::Model& m,
                        const std::map<Node, bool>& isDeclared,
                        const std::map<TypeNode, std::vector<Node>>& finiteTypeElems,
                        Node n,
                        bool& value)
{
  std::map<Node, Node> subst;
  Node v = evalFiniteTerm(n, m, isDeclared, finiteTypeElems, subst);
  if (v.isNull() || v.getKind() != Kind::CONST_BOOLEAN)
  {
    return false;
  }
  value = v.getConst<bool>();
  return true;
}

bool resolveBoolValue(const smt::Model& m,
                      const std::map<Node, bool>& isDeclared,
                      const std::map<TypeNode, std::vector<Node>>& finiteTypeElems,
                      Node n,
                      bool& value)
{
  if (m.getBooleanValue(n, value))
  {
    return true;
  }
  return getBoolValueFinite(m, isDeclared, finiteTypeElems, n, value);
}

bool modelNodeToTptp(const Node& n,
                     const std::map<Node, bool>& isDeclared,
                     const std::map<Node, std::string>& elemNames,
                     const std::map<TypeNode, std::string>& promoteNames,
                     bool useThfTuple,
                     std::map<Node, std::string>& bvarNames,
                     std::string& out)
{
  Node nconv = theory::uf::FunctionConst::toLambda(n);
  if (!nconv.isNull() && nconv != n)
  {
    return modelNodeToTptp(nconv,
                           isDeclared,
                           elemNames,
                           promoteNames,
                           useThfTuple,
                           bvarNames,
                           out);
  }
  auto bvit = bvarNames.find(n);
  if (bvit != bvarNames.end())
  {
    out = bvit->second;
    return true;
  }
  if (n.getKind() == Kind::CONST_BOOLEAN)
  {
    out = n.getConst<bool>() ? "$true" : "$false";
    return true;
  }
  auto eit = elemNames.find(n);
  if (eit != elemNames.end() && n.getType().isUninterpretedSort())
  {
    auto pit = promoteNames.find(n.getType());
    if (pit == promoteNames.end())
    {
      return false;
    }
    out = mkApplyString(pit->second, std::vector<std::string>{eit->second}, useThfTuple);
    return true;
  }
  if (isDeclared.find(n) != isDeclared.end())
  {
    out = sanitizeLower(n.toString());
    return true;
  }
  if (n.getKind() == Kind::BOUND_VARIABLE || n.getKind() == Kind::VARIABLE)
  {
    out = sanitizeUpper(n.toString());
    return true;
  }
  if (n.getKind() == Kind::LAMBDA)
  {
    Node bvl = n[0];
    std::vector<std::pair<Node, bool>> oldSet;
    std::vector<std::string> binds;
    binds.reserve(bvl.getNumChildren());
    for (const Node& bv : bvl)
    {
      bool had = bvarNames.find(bv) != bvarNames.end();
      oldSet.emplace_back(bv, had);
      std::string bvn = sanitizeUpper(bv.toString());
      bvarNames[bv] = bvn;
      binds.push_back(bvn + ": " + typeToTptp(bv.getType(), useThfTuple));
    }
    std::string body;
    bool ok = modelNodeToTptp(n[1],
                              isDeclared,
                              elemNames,
                              promoteNames,
                              useThfTuple,
                              bvarNames,
                              body);
    for (const std::pair<Node, bool>& p : oldSet)
    {
      if (!p.second)
      {
        bvarNames.erase(p.first);
      }
    }
    if (!ok)
    {
      return false;
    }
    out = "( ^ [" + join(binds, ",") + "] : " + body + " )";
    return true;
  }
  if (n.getKind() == Kind::APPLY_UF || n.getKind() == Kind::HO_APPLY)
  {
    if (n.getNumChildren() == 0)
    {
      return false;
    }
    std::string head;
    if (!modelNodeToTptp(n[0],
                         isDeclared,
                         elemNames,
                         promoteNames,
                         useThfTuple,
                         bvarNames,
                         head))
    {
      return false;
    }
    std::vector<std::string> args;
    args.reserve(n.getNumChildren() - 1);
    for (size_t i = 1, nc = n.getNumChildren(); i < nc; i++)
    {
      std::string a;
      if (!modelNodeToTptp(n[i],
                           isDeclared,
                           elemNames,
                           promoteNames,
                           useThfTuple,
                           bvarNames,
                           a))
      {
        return false;
      }
      args.push_back(a);
    }
    out = mkApplyString(head, args, useThfTuple);
    return true;
  }
  if (n.getKind() == Kind::EQUAL)
  {
    std::string a;
    std::string b;
    if (!modelNodeToTptp(n[0],
                         isDeclared,
                         elemNames,
                         promoteNames,
                         useThfTuple,
                         bvarNames,
                         a)
        || !modelNodeToTptp(n[1],
                            isDeclared,
                            elemNames,
                            promoteNames,
                            useThfTuple,
                            bvarNames,
                            b))
    {
      return false;
    }
    out = "( " + a + " = " + b + " )";
    return true;
  }
  if (n.getKind() == Kind::NOT)
  {
    std::string c;
    if (!modelNodeToTptp(n[0],
                         isDeclared,
                         elemNames,
                         promoteNames,
                         useThfTuple,
                         bvarNames,
                         c))
    {
      return false;
    }
    out = "~ ( " + c + " )";
    return true;
  }
  if (n.getKind() == Kind::AND || n.getKind() == Kind::OR)
  {
    if (n.getNumChildren() == 0)
    {
      out = n.getKind() == Kind::AND ? "$true" : "$false";
      return true;
    }
    const std::string op = n.getKind() == Kind::AND ? " & " : " | ";
    std::vector<std::string> cs;
    cs.reserve(n.getNumChildren());
    for (const Node& c : n)
    {
      std::string s;
      if (!modelNodeToTptp(c,
                           isDeclared,
                           elemNames,
                           promoteNames,
                           useThfTuple,
                           bvarNames,
                           s))
      {
        return false;
      }
      cs.push_back(s);
    }
    out = "( " + join(cs, op) + " )";
    return true;
  }
  if (n.getKind() == Kind::IMPLIES)
  {
    std::string a;
    std::string b;
    if (!modelNodeToTptp(n[0],
                         isDeclared,
                         elemNames,
                         promoteNames,
                         useThfTuple,
                         bvarNames,
                         a)
        || !modelNodeToTptp(n[1],
                            isDeclared,
                            elemNames,
                            promoteNames,
                            useThfTuple,
                            bvarNames,
                            b))
    {
      return false;
    }
    out = "( ( " + a + " ) => ( " + b + " ) )";
    return true;
  }
  if (n.getKind() == Kind::ITE)
  {
    // Keep output in formula-only connectives for compatibility with current
    // THF/TFF printer style.
    if (!n.getType().isBoolean())
    {
      return false;
    }
    std::string c;
    std::string t;
    std::string e;
    if (!modelNodeToTptp(n[0],
                         isDeclared,
                         elemNames,
                         promoteNames,
                         useThfTuple,
                         bvarNames,
                         c)
        || !modelNodeToTptp(n[1],
                            isDeclared,
                            elemNames,
                            promoteNames,
                            useThfTuple,
                            bvarNames,
                            t)
        || !modelNodeToTptp(n[2],
                            isDeclared,
                            elemNames,
                            promoteNames,
                            useThfTuple,
                            bvarNames,
                            e))
    {
      return false;
    }
    out = "( ( ( " + c + " ) & ( " + t + " ) ) | ( ~ ( " + c + " ) & ( " + e
          + " ) ) )";
    return true;
  }
  if (n.getKind() == Kind::FORALL || n.getKind() == Kind::EXISTS)
  {
    Node bvl = n[0];
    std::vector<std::pair<Node, bool>> oldSet;
    std::vector<std::string> binds;
    binds.reserve(bvl.getNumChildren());
    for (const Node& bv : bvl)
    {
      bool had = bvarNames.find(bv) != bvarNames.end();
      oldSet.emplace_back(bv, had);
      std::string bvn = sanitizeUpper(bv.toString());
      bvarNames[bv] = bvn;
      binds.push_back(bvn + ": " + typeToTptp(bv.getType(), useThfTuple));
    }
    std::string body;
    bool ok = modelNodeToTptp(n[1],
                              isDeclared,
                              elemNames,
                              promoteNames,
                              useThfTuple,
                              bvarNames,
                              body);
    for (const std::pair<Node, bool>& p : oldSet)
    {
      if (!p.second)
      {
        bvarNames.erase(p.first);
      }
    }
    if (!ok)
    {
      return false;
    }
    out = std::string(n.getKind() == Kind::FORALL ? "! " : "? ") + "["
          + join(binds, ",") + "] : ( " + body + " )";
    return true;
  }
  return false;
}

}  // namespace

void Smt2TptpPrinter::toStream(std::ostream& out, const smt::Model& m) const
{
  const std::vector<TypeNode>& allSorts = m.getDeclaredSorts();
  const std::vector<Node>& terms = m.getDeclaredTerms();
  std::vector<TypeNode> sorts;
  for (const TypeNode& s : allSorts)
  {
    bool used = false;
    for (const Node& t : terms)
    {
      if (typeUsesSort(t.getType(), s))
      {
        used = true;
        break;
      }
    }
    if (used)
    {
      sorts.push_back(s);
    }
  }
  std::map<Node, bool> isDeclared;
  for (const Node& t : terms)
  {
    isDeclared[t] = true;
  }

  std::map<TypeNode, std::string> sortNames;
  std::map<TypeNode, std::string> sortTypeNames;
  std::map<TypeNode, std::string> dSortNames;
  std::map<TypeNode, std::string> promoteNames;
  std::map<TypeNode, std::vector<Node>> elems;
  std::map<Node, std::string> elemNames;
  std::map<TypeNode, std::vector<Node>> finiteTypeElems;
  std::map<Node, std::string> hoElemNames;

  for (const TypeNode& s : sorts)
  {
    // For each uninterpreted sort S, we create:
    // - a TPTP type symbol "s"
    // - a finite domain carrier type "d_s"
    // - a promotion function "d2s : d_s > s"
    sortNames[s] = sanitizeLower(s.toString());
    sortTypeNames[s] = typeToTptp(s);
    dSortNames[s] = "d_" + sortNames[s];
    promoteNames[s] = "d2" + sortNames[s];
    elems[s] = m.getDomainElements(s);
    finiteTypeElems[s] = elems[s];
  }

  // Prefer stable domain element names from declared constants
  // (e.g. d_jon) before falling back to d_<sort>_<index>.
  for (const Node& t : terms)
  {
    TypeNode tt = t.getType();
    if (!tt.isFunction() && tt.isUninterpretedSort())
    {
      Node v = m.getValue(t);
      if (elemNames.find(v) == elemNames.end())
      {
        elemNames[v] = "d_" + sanitizeLower(t.toString());
      }
    }
  }
  // Reorder each domain by the order of declared constants of that sort
  // (when available), and append any remaining elements afterwards.
  for (const TypeNode& s : sorts)
  {
    const std::vector<Node>& se = elems[s];
    std::vector<Node> ordered;
    std::map<Node, bool> seen;
    for (const Node& t : terms)
    {
      TypeNode tt = t.getType();
      if (tt.isFunction() || tt != s)
      {
        continue;
      }
      Node v = m.getValue(t);
      if (seen.find(v) != seen.end())
      {
        continue;
      }
      bool inDomain = false;
      for (const Node& e : se)
      {
        if (e == v)
        {
          inDomain = true;
          break;
        }
      }
      if (inDomain)
      {
        ordered.push_back(v);
        seen[v] = true;
      }
    }
    for (const Node& e : se)
    {
      if (seen.find(e) == seen.end())
      {
        ordered.push_back(e);
      }
    }
    elems[s] = ordered;
  }
  for (const TypeNode& s : sorts)
  {
    size_t i = 0;
    for (const Node& e : elems[s])
    {
      if (elemNames.find(e) == elemNames.end())
      {
        std::stringstream ss;
        ss << "d_" << sortNames[s] << "_" << i;
        elemNames[e] = ss.str();
      }
      i++;
    }
  }

  // Build finite domains for function types that occur as arguments.
  // Also seed from declared Boolean bodies, which may quantify over HO types.
  const size_t kMaxHoFunctionDomain = 256;
  std::set<TypeNode> hoSeedTypes;
  for (const Node& t : terms)
  {
    TypeNode tt = t.getType();
    if (!tt.isFunction())
    {
      Node tv = m.getValueOrNull(t);
      if (!tv.isNull() && tt.isBoolean())
      {
        collectFunctionTypes(tv, hoSeedTypes);
      }
      continue;
    }
    for (const TypeNode& at : tt.getArgTypes())
    {
      if (!at.isFunction())
      {
        continue;
      }
      hoSeedTypes.insert(at);
    }
  }
  for (const TypeNode& ht : hoSeedTypes)
  {
    (void)getFiniteDomainValues(
        ht, ht.getNodeManager(), elems, finiteTypeElems, kMaxHoFunctionDomain);
  }

  bool useThf = false;
  for (const Node& t : terms)
  {
    if (isHigherOrderType(t.getType()))
    {
      useThf = true;
      break;
    }
  }
  if (!useThf)
  {
    for (const std::pair<const TypeNode, std::vector<Node>>& p : finiteTypeElems)
    {
      if (isHigherOrderType(p.first))
      {
        useThf = true;
        break;
      }
    }
  }
  std::map<Node, std::string> hoDirectInterp;
  bool needHoFiniteDomain = false;
  for (const Node& t : terms)
  {
    TypeNode tt = t.getType();
    if (!tt.isFunction() || !hasFunctionArgType(tt))
    {
      continue;
    }
    Node tv = resolveModelValue(m, isDeclared, t);
    if (tv.isNull())
    {
      needHoFiniteDomain = true;
      continue;
    }
    std::map<Node, std::string> bvarNames;
    std::string rhs;
    if (!modelNodeToTptp(tv,
                         isDeclared,
                         elemNames,
                         promoteNames,
                         useThf,
                         bvarNames,
                         rhs))
    {
      needHoFiniteDomain = true;
      continue;
    }
    const std::string lhs = sanitizeLower(t.toString());
    if (rhs.rfind("( ^ [", 0) == 0)
    {
      hoDirectInterp[t] = "( " + lhs + "\n      = " + rhs + " )";
    }
    else
    {
      hoDirectInterp[t] = "( " + lhs + " = " + rhs + " )";
    }
  }
  if (needHoFiniteDomain)
  {
    // Name higher-order finite-domain elements only as a fallback when
    // direct HO interpretations cannot be printed.
    for (const std::pair<const TypeNode, std::vector<Node>>& p : finiteTypeElems)
    {
      if (!p.first.isFunction())
      {
        continue;
      }
      std::string pref = "d_f_" + sanitizeLower(p.first.toString());
      if (pref.empty() || pref.back() != '_')
      {
        pref.push_back('_');
      }
      for (size_t i = 0, n = p.second.size(); i < n; i++)
      {
        if (hoElemNames.find(p.second[i]) != hoElemNames.end())
        {
          continue;
        }
        std::stringstream ss;
        ss << pref << i;
        hoElemNames[p.second[i]] = sanitizeLower(ss.str());
      }
    }
  }
  if (!useThf && (!hoElemNames.empty() || !hoDirectInterp.empty()))
  {
    useThf = true;
  }
  const char* ff = useThf ? "thf" : "tff";

  out << "%--------------------------------------------------------\n";
  // 1) Top-level symbol declarations (original signature).
  for (const TypeNode& s : sorts)
  {
    printTypeDecl(out, ff, sortNames[s] + "_type", sortNames[s], "$tType");
  }
  for (const Node& t : terms)
  {
    TypeNode tt = t.getType();
    std::string tn = sanitizeLower(t.toString());
    printTypeDecl(out, ff, tn + "_decl", tn, typeToTptp(tt, useThf));
  }
  out << "%----Types of the domains\n";
  // 2) Finite-domain helper declarations used by the interpretation block.
  for (const TypeNode& s : sorts)
  {
    printTypeDecl(out, ff, dSortNames[s] + "_type", dSortNames[s], "$tType");
  }
  out << "%----Types of the promotion functions\n";
  for (const TypeNode& s : sorts)
  {
    printTypeDecl(out,
                  ff,
                  promoteNames[s] + "_decl",
                  promoteNames[s],
                  dSortNames[s] + " > " + sortTypeNames[s]);
  }
  out << "%----Types of the domain elements\n";
  for (const TypeNode& s : sorts)
  {
    for (const Node& e : elems[s])
    {
      printTypeDecl(
          out, ff, elemNames[e] + "_decl", elemNames[e], dSortNames[s]);
    }
  }
  if (!hoElemNames.empty())
  {
    out << "%----Types of higher-order domain elements\n";
    for (const std::pair<const TypeNode, std::vector<Node>>& p : finiteTypeElems)
    {
      if (!p.first.isFunction())
      {
        continue;
      }
      for (const Node& e : p.second)
      {
        printTypeDecl(out,
                      ff,
                      hoElemNames[e] + "_decl",
                      hoElemNames[e],
                      typeToTptp(p.first, useThf));
      }
    }
  }

  const std::string inputName = m.getInputName();
  std::string modelName = sanitizeLower(stripPath(inputName));
  if (inputName == "_stdin_")
  {
    modelName = "model";
  }
  const std::string domainName = modelName;
  out << ff << "(" << domainName << ",interpretation,\n";
  out << "    ( ";
  // 3) Domain axioms: surjectivity, finite enumeration, distinctness,
  //    and injectivity of each promotion function.
  bool firstDomain = true;
  for (const TypeNode& s : sorts)
  {
    if (!firstDomain)
    {
      out << "\n    & ";
    }
    firstDomain = false;
    std::string sN = sortNames[s];
    std::string stN = sortTypeNames[s];
    std::string dsN = dSortNames[s];
    std::string pN = promoteNames[s];
    std::string vS = sanitizeUpper(sN.substr(0, 1)); // variable of the original sort
    std::string vDS = "D" + vS; // variable of the domain sort
    out << "! [" << vS << ": " << stN << "] :\n";
    out << "      ? [" << vDS << ": " << dsN << "] : ( " << vS << " = "
        << mkApplyString(pN, std::vector<std::string>{vDS}, useThf) << " )";

    const std::vector<Node>& se = elems[s];
    if (se.size() == 2)
    {
      out << "\n    & ! [" << vDS << ": " << dsN << "] :\n";
      out << "        ( ( " << vDS << " = " << elemNames[se[0]] << " )\n";
      out << "        | ( " << vDS << " = " << elemNames[se[1]] << " ) )";
    }
    else if (se.size() > 1)
    {
      out << "\n    & ! [" << vDS << ": " << dsN << "] :\n          ( ";
    }
    else
    {
      out << "\n    & ! [" << vDS << ": " << dsN << "] : ( ";
    }
    if (se.size() != 2)
    {
      for (size_t i = 0, n = se.size(); i < n; i++)
      {
        if (i > 0)
        {
          out << " | ";
        }
        out << vDS << " = " << elemNames[se[i]];
      }
      out << " )";
    }
    if (se.size() == 2)
    {
      out << "\n    & " << elemNames[se[0]] << " != " << elemNames[se[1]];
    }
    else if (se.size() > 2)
    {
      out << "\n    & $distinct(";
      for (size_t i = 0, n = se.size(); i < n; i++)
      {
        if (i > 0)
        {
          out << ",";
        }
        out << elemNames[se[i]];
      }
      out << ")";
    }
    out << "\n    & ! [" << vDS << "1: " << dsN << "," << vDS << "2: " << dsN
        << "] :\n";
    out << "        ( ( "
        << mkApplyString(pN, std::vector<std::string>{vDS + "1"}, useThf)
        << " = "
        << mkApplyString(pN, std::vector<std::string>{vDS + "2"}, useThf)
        << " )\n";
    out << "       => ( " << vDS << "1 = " << vDS << "2 ) )";
  }
  if (!hoElemNames.empty())
  {
    // Finite-domain axioms for higher-order function types we materialize.
    size_t hoTypeIndex = 0;
    for (const std::pair<const TypeNode, std::vector<Node>>& p : finiteTypeElems)
    {
      if (!p.first.isFunction())
      {
        continue;
      }
      if (p.second.empty())
      {
        continue;
      }
      if (!firstDomain)
      {
        out << "\n    & ";
      }
      firstDomain = false;
      std::stringstream fv;
      fv << "F" << hoTypeIndex++;
      out << "! [" << fv.str() << ": (" << typeToTptp(p.first, useThf)
          << ")] : ( ";
      for (size_t i = 0, n = p.second.size(); i < n; i++)
      {
        if (i > 0)
        {
          out << " | ";
        }
        auto hit = hoElemNames.find(p.second[i]);
        if (hit == hoElemNames.end())
        {
          continue;
        }
        out << fv.str() << " = " << hit->second;
      }
      out << " )";
      if (p.second.size() == 2)
      {
        auto h0 = hoElemNames.find(p.second[0]);
        auto h1 = hoElemNames.find(p.second[1]);
        if (h0 != hoElemNames.end() && h1 != hoElemNames.end())
        {
          out << "\n    & " << h0->second << " != " << h1->second;
        }
      }
      else if (p.second.size() > 2)
      {
        out << "\n    & $distinct(";
        bool first = true;
        for (const Node& e : p.second)
        {
          auto hit = hoElemNames.find(e);
          if (hit == hoElemNames.end())
          {
            continue;
          }
          if (!first)
          {
            out << ",";
          }
          first = false;
          out << hit->second;
        }
        out << ")";
      }
    }
  }
  if (firstDomain)
  {
    out << "$true";
  }

  // 4) Interpret constants and total function/predicate tables by
  //    exhaustively evaluating all tuples of finite-domain elements.
  std::vector<std::string> mappingConjs;
  std::vector<std::string> atomConjs;
  for (const Node& t : terms)
  {
    TypeNode tt = t.getType();
    std::string tn = sanitizeLower(t.toString());
    auto hdi = hoDirectInterp.find(t);
    if (hdi != hoDirectInterp.end())
    {
      mappingConjs.push_back(hdi->second);
      continue;
    }
    if (!tt.isFunction())
    {
      Node v = m.getValue(t);
      if (tt.isBoolean())
      {
        bool b = false;
        const bool resolved =
            resolveBoolValue(m, isDeclared, finiteTypeElems, t, b)
            || resolveBoolValue(m, isDeclared, finiteTypeElems, v, b);
        if (!resolved)
        {
          // Fallback for unresolved propositional constants: keep the symbol in
          // the interpretation while preserving satisfiability.
          atomConjs.push_back("( " + tn + " | ~ " + tn + " )");
          continue;
        }
        atomConjs.push_back((b ? "" : "~ ") + tn);
        continue;
      }
      std::string evn = resolveElemName(m, isDeclared, v, elemNames);
      if (evn.empty())
      {
        continue;
      }
      std::stringstream ss;
      ss << "( " << tn << " = "
         << mkApplyString(promoteNames[tt], std::vector<std::string>{evn}, useThf)
         << " )";
      mappingConjs.push_back(ss.str());
      continue;
    }
    std::vector<TypeNode> argTypes = tt.getArgTypes();
    bool ok = true;
    std::vector<std::vector<Node>> domains;
    domains.reserve(argTypes.size());
    for (const TypeNode& at : argTypes)
    {
      if (at.isUninterpretedSort())
      {
        domains.push_back(elems[at]);
        continue;
      }
      auto it = finiteTypeElems.find(at);
      if (it == finiteTypeElems.end() || it->second.empty())
      {
        ok = false;
        break;
      }
      domains.push_back(it->second);
    }
    if (!ok
        || (!tt.getRangeType().isUninterpretedSort()
            && !tt.getRangeType().isBoolean()))
    {
      // Print rows only for finite argument domains and Bool/USort codomains.
      continue;
    }
    std::vector<std::vector<Node>> tuples;
    std::vector<Node> current(argTypes.size());
    cartesianProduct(domains, 0, current, tuples);
    for (const std::vector<Node>& tup : tuples)
    {
      std::vector<Node> children;
      children.push_back(t);
      children.insert(children.end(), tup.begin(), tup.end());
      Node app = t.getNodeManager()->mkNode(Kind::APPLY_UF, children);
      Node val;
      if (!tryGetModelValue(m, isDeclared, app, val))
      {
        val = evaluateAppValue(m, isDeclared, t, tup);
        if (val.isNull())
        {
          std::map<Node, Node> emptySubst;
          val = evalFiniteTerm(app, m, isDeclared, finiteTypeElems, emptySubst);
          if (val.isNull())
          {
            continue;
          }
        }
      }
      const bool isPred = tt.getRangeType().isBoolean();
      bool emitNeg = false;
      if (isPred)
      {
        bool bval = false;
        if (!resolveBoolValue(m, isDeclared, finiteTypeElems, app, bval)
            && !resolveBoolValue(m, isDeclared, finiteTypeElems, val, bval))
        {
          // If model value cannot be resolved to true/false, skip this row
          // rather than emitting an unsound negation.
          continue;
        }
        emitNeg = !bval;
      }
      std::string vname;
      if (!isPred)
      {
        vname = resolveElemName(m, isDeclared, val, elemNames);
        if (vname.empty())
        {
          // Skip rows whose codomain value cannot be mapped to a finite-domain
          // representative.
          continue;
        }
      }
      std::stringstream ss;
      if (emitNeg)
      {
        ss << "~ ";
      }
      std::vector<std::string> argVals;
      argVals.reserve(tup.size());
      bool tupleOk = true;
      for (size_t i = 0, n = tup.size(); i < n; i++)
      {
        TypeNode at = argTypes[i];
        if (at.isUninterpretedSort())
        {
          argVals.push_back(
              mkApplyString(promoteNames[at],
                            std::vector<std::string>{elemNames[tup[i]]},
                            useThf));
        }
        else
        {
          auto hit = hoElemNames.find(tup[i]);
          if (hit == hoElemNames.end())
          {
            tupleOk = false;
            break;
          }
          argVals.push_back(hit->second);
        }
      }
      if (!tupleOk)
      {
        continue;
      }
      ss << mkApplyString(tn, argVals, useThf);
      if (!isPred)
      {
        ss << " = "
           << mkApplyString(promoteNames[tt.getRangeType()],
                            std::vector<std::string>{vname},
                            useThf);
        mappingConjs.push_back("( " + ss.str() + " )");
      }
      else
      {
        atomConjs.push_back(ss.str());
      }
    }
  }

  bool hasConj = false;
  for (const std::string& c : mappingConjs)
  {
    out << "\n    & " << c;
    hasConj = true;
  }
  if (!atomConjs.empty())
  {
    out << "\n    & ( " << atomConjs[0];
    for (size_t i = 1, n = atomConjs.size(); i < n; i++)
    {
      out << "\n    & " << atomConjs[i];
    }
    out << " )";
    hasConj = true;
  }
  if (!hasConj)
  {
    out << "\n    & $true";
  }
  out << " ) ).\n";
  out << "%--------------------------------------------------------\n";
}

void Smt2TptpPrinter::toStream(std::ostream& out, TNode n) const
{
  Smt2Printer::toStream(out, n);
}

void Smt2TptpPrinter::toStream(std::ostream& out, Kind k) const
{
  Smt2Printer::toStream(out, k);
}

void Smt2TptpPrinter::toStreamCmdAssert(std::ostream& out, Node n) const
{
  Smt2Printer::toStreamCmdAssert(out, n);
}

void Smt2TptpPrinter::toStreamCmdDeclareFunction(
    std::ostream& out,
    const std::string& id,
    const std::vector<TypeNode>& argTypes,
    TypeNode type) const
{
  Smt2Printer::toStreamCmdDeclareFunction(out, id, argTypes, type);
}

void Smt2TptpPrinter::toStreamCmdCheckSat(std::ostream& out) const
{
  Smt2Printer::toStreamCmdCheckSat(out);
}

}  // namespace smt2
}  // namespace printer
}  // namespace cvc5::internal
