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
#include <map>
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

std::string typeToTptp(TypeNode tn)
{
  if (tn.isBoolean())
  {
    return "$o";
  }
  if (tn.isFunction())
  {
    std::vector<TypeNode> args = tn.getArgTypes();
    std::vector<std::string> argStrs;
    argStrs.reserve(args.size());
    for (const TypeNode& at : args)
    {
      std::string atStr = typeToTptp(at);
      if (at.isFunction())
      {
        atStr = "( " + atStr + " )";
      }
      argStrs.push_back(atStr);
    }
    std::string r = typeToTptp(tn.getRangeType());
    return args.size() == 1 ? argStrs[0] + " > " + r
                            : "( " + join(argStrs, " * ") + " ) > " + r;
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

bool tryGetModelValue(const smt::Model& m,
                      const std::map<Node, bool>& isDeclared,
                      Node n,
                      Node& value)
{
  if (isDeclared.find(n) == isDeclared.end())
  {
    return false;
  }
  value = m.getValue(n);
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

bool getBoolValue(const smt::Model& m,
                  const std::map<Node, bool>& isDeclared,
                  Node n,
                  bool& value)
{
  Node v = n;
  if (isDeclared.find(v) != isDeclared.end())
  {
    v = resolveModelValue(m, isDeclared, v);
  }
  if (v.isNull())
  {
    return false;
  }
  if (v.getKind() == Kind::CONST_BOOLEAN)
  {
    value = v.getConst<bool>();
    return true;
  }
  return false;
}

std::string resolveElemName(const smt::Model& m,
                            const std::map<Node, bool>& isDeclared,
                            TypeNode sort,
                            Node value,
                            const std::map<TypeNode, std::vector<Node>>& elems,
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
  std::map<TypeNode, std::string> dSortNames;
  std::map<TypeNode, std::string> promoteNames;
  std::map<TypeNode, std::vector<Node>> elems;
  std::map<Node, std::string> elemNames;

  for (const TypeNode& s : sorts)
  {
    // For each uninterpreted sort S, we create:
    // - a TPTP type symbol "s"
    // - a finite domain carrier type "d_s"
    // - a promotion function "d2s : d_s > s"
    sortNames[s] = sanitizeLower(s.toString());
    dSortNames[s] = "d_" + sortNames[s];
    promoteNames[s] = "d2" + sortNames[s];
    elems[s] = m.getDomainElements(s);
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

  out << "%--------------------------------------------------------\n";
  // 1) Top-level symbol declarations (original signature).
  for (const TypeNode& s : sorts)
  {
    out << "tff(" << sortNames[s] << "_type,type,      " << sortNames[s]
        << ": $tType ).\n";
  }
  for (const Node& t : terms)
  {
    TypeNode tt = t.getType();
    std::string tn = sanitizeLower(t.toString());
    if (!tt.isFunction())
    {
      out << "tff(" << tn << "_decl,type,      " << tn << ": "
          << typeToTptp(tt) << " ).\n";
      continue;
    }
    out << "tff(" << tn << "_decl,type,      " << tn << ": " << typeToTptp(tt)
        << " ).\n";
  }
  out << "\n%----Types of the domains\n";
  // 2) Finite-domain helper declarations used by the interpretation block.
  for (const TypeNode& s : sorts)
  {
    out << "tff(" << dSortNames[s] << "_type,type,    " << dSortNames[s]
        << ": $tType ).\n";
  }
  out << "%----Types of the promotion functions\n";
  for (const TypeNode& s : sorts)
  {
    out << "tff(" << promoteNames[s] << "_decl,type,    " << promoteNames[s]
        << ": " << dSortNames[s] << " > " << sortNames[s] << " ).\n";
  }
  out << "%----Types of the domain elements\n";
  for (const TypeNode& s : sorts)
  {
    for (const Node& e : elems[s])
    {
      out << "tff(" << elemNames[e] << "_decl,type,      " << elemNames[e]
          << ": " << dSortNames[s] << " ).\n";
    }
  }

  const std::string inputName = m.getInputName();
  std::string modelName = sanitizeLower(inputName);
  if (inputName == "_stdin_")
  {
    modelName = "model";
  }
  out << "\ntff(" << modelName << ",interpretation,\n";
  out << "%----The domains\n    ( ";
  // 3) Domain axioms: surjectivity, finite enumeration, distinctness,
  //    and injectivity of each promotion function.
  bool firstDomain = true;
  for (const TypeNode& s : sorts)
  {
    if (!firstDomain)
    {
      out << "\n      & ";
    }
    firstDomain = false;
    std::string sN = sortNames[s];
    std::string dsN = dSortNames[s];
    std::string pN = promoteNames[s];
    std::string vS = sanitizeUpper(sN.substr(0, 1)); // variable of the original sort
    std::string vDS = "D" + vS; // variable of the domain sort
    out << "! [" << vS << ": " << sN << "] : ? [" << vDS << ": " << dsN << "] : "
        << vS << " = " << pN << "(" << vDS << ")";

    out << "\n      & ! [" << vDS << ": " << dsN << "]: ( ";
    const std::vector<Node>& se = elems[s];
    for (size_t i = 0, n = se.size(); i < n; i++)
    {
      if (i > 0)
      {
        out << " | ";
      }
      out << vDS << " = " << elemNames[se[i]];
    }
    out << " )";
    if (se.size() > 1)
    {
      out << "\n      & $distinct(";
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
    out << "\n      & ! [" << vDS << "1: " << dsN << "," << vDS << "2: " << dsN
        << "] : (" << pN << "(" << vDS << "1) = " << pN << "(" << vDS
        << "2) => " << vDS << "1 = " << vDS << "2)";
  }
  out << " )\n";

  // 4) Interpret constants and total function/predicate tables by
  //    exhaustively evaluating all tuples of finite-domain elements.
  out << "%----Interpret terms and atoms\n    & ( ";
  bool firstEq = true;
  for (const Node& t : terms)
  {
    TypeNode tt = t.getType();
    std::string tn = sanitizeLower(t.toString());
    if (!tt.isFunction())
    {
      Node v = m.getValue(t);
      std::string evn = resolveElemName(m, isDeclared, tt, v, elems, elemNames);
      if (evn.empty())
      {
        continue;
      }
      if (!firstEq)
      {
        out << "\n      & ";
      }
      firstEq = false;
      out << tn << " = " << promoteNames[tt] << "(" << evn << ")";
      continue;
    }
    std::vector<TypeNode> argTypes = tt.getArgTypes();
    bool ok = std::all_of(argTypes.begin(),
                          argTypes.end(),
                          [](TypeNode at) { return at.isUninterpretedSort(); });
    if (!ok || (!tt.getRangeType().isUninterpretedSort() && !tt.getRangeType().isBoolean()))
    {
      // Focuses on uninterpretd sorts and Bool codomains.
      continue;
    }
    std::vector<std::vector<Node>> domains;
    for (const TypeNode& at : argTypes)
    {
      domains.push_back(elems[at]);
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
          continue;
        }
      }
      const bool isPred = tt.getRangeType().isBoolean();
      bool emitNeg = false;
      if (isPred)
      {
        bool bval = false;
        if (!getBoolValue(m, isDeclared, val, bval))
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
        vname = resolveElemName(
            m, isDeclared, tt.getRangeType(), val, elems, elemNames);
        if (vname.empty())
        {
          // Skip rows whose codomain value cannot be mapped to a finite-domain
          // representative.
          continue;
        }
      }
      if (!firstEq)
      {
        out << "\n      & ";
      }
      firstEq = false;
      if (emitNeg)
      {
        out << "~ ";
      }
      out << tn << "(";
      for (size_t i = 0, n = tup.size(); i < n; i++)
      {
        if (i > 0)
        {
          out << ",";
        }
        out << promoteNames[argTypes[i]] << "(" << elemNames[tup[i]] << ")";
      }
      out << ")";
      if (!isPred)
      {
        out << " = " << promoteNames[tt.getRangeType()] << "(" << vname << ")";
      }
    }
  }
  if (firstEq)
  {
    out << "$true";
  }
  out << " )\n";
  out << "  ).\n";
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
