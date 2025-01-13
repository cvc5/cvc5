/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The printer for the AletheLF format.
 */

#include "proof/alf/alf_printer.h"

#include <cctype>
#include <iostream>
#include <memory>
#include <ostream>
#include <sstream>

#include "expr/node_algorithm.h"
#include "expr/subs.h"
#include "options/main_options.h"
#include "options/strings_options.h"
#include "printer/printer.h"
#include "printer/smt2/smt2_printer.h"
#include "proof/alf/alf_dependent_type_converter.h"
#include "proof/proof_node_to_sexpr.h"
#include "rewriter/rewrite_db.h"
#include "smt/print_benchmark.h"
#include "theory/strings/theory_strings_utils.h"
#include "util/string.h"

namespace cvc5::internal {

namespace proof {

AlfPrinter::AlfPrinter(Env& env,
                       BaseAlfNodeConverter& atp,
                       rewriter::RewriteDb* rdb,
                       uint32_t letThresh)
    : EnvObj(env),
      d_tproc(atp),
      d_pfIdCounter(0),
      d_alreadyPrinted(&d_passumeCtx),
      d_passumeMap(&d_passumeCtx),
      d_termLetPrefix("@t"),
      d_rdb(rdb),
      // Use a let binding if proofDagGlobal is true. We can traverse binders
      // due to the way we print global declare-var, since terms beneath
      // binders will always have their variables in scope and hence can be
      // printed in define commands. We additionally traverse skolems with this
      // utility.
      d_lbind(d_termLetPrefix, letThresh, true, true),
      d_lbindUse(options().proof.proofDagGlobal ? &d_lbind : nullptr),
      d_aletify(d_lbindUse)
{
  d_pfType = nodeManager()->mkSort("proofType");
  d_false = nodeManager()->mkConst(false);
  d_absType = nodeManager()->mkAbstractType(Kind::ABSTRACT_TYPE);
}

bool AlfPrinter::isHandled(const Options& opts, const ProofNode* pfn)
{
  const std::vector<Node> pargs = pfn->getArguments();
  switch (pfn->getRule())
  {
    // List of handled rules
    case ProofRule::ASSUME:
    case ProofRule::SCOPE:
    case ProofRule::REFL:
    case ProofRule::SYMM:
    case ProofRule::TRANS:
    case ProofRule::CONG:
    case ProofRule::NARY_CONG:
    case ProofRule::HO_CONG:
    case ProofRule::TRUE_INTRO:
    case ProofRule::TRUE_ELIM:
    case ProofRule::FALSE_INTRO:
    case ProofRule::FALSE_ELIM:
    case ProofRule::SPLIT:
    case ProofRule::EQ_RESOLVE:
    case ProofRule::MODUS_PONENS:
    case ProofRule::NOT_NOT_ELIM:
    case ProofRule::CONTRA:
    case ProofRule::AND_ELIM:
    case ProofRule::AND_INTRO:
    case ProofRule::NOT_OR_ELIM:
    case ProofRule::IMPLIES_ELIM:
    case ProofRule::NOT_IMPLIES_ELIM1:
    case ProofRule::NOT_IMPLIES_ELIM2:
    case ProofRule::EQUIV_ELIM1:
    case ProofRule::EQUIV_ELIM2:
    case ProofRule::NOT_EQUIV_ELIM1:
    case ProofRule::NOT_EQUIV_ELIM2:
    case ProofRule::XOR_ELIM1:
    case ProofRule::XOR_ELIM2:
    case ProofRule::NOT_XOR_ELIM1:
    case ProofRule::NOT_XOR_ELIM2:
    case ProofRule::ITE_ELIM1:
    case ProofRule::ITE_ELIM2:
    case ProofRule::NOT_ITE_ELIM1:
    case ProofRule::NOT_ITE_ELIM2:
    case ProofRule::NOT_AND:
    case ProofRule::CNF_AND_NEG:
    case ProofRule::CNF_OR_POS:
    case ProofRule::CNF_OR_NEG:
    case ProofRule::CNF_IMPLIES_POS:
    case ProofRule::CNF_IMPLIES_NEG1:
    case ProofRule::CNF_IMPLIES_NEG2:
    case ProofRule::CNF_EQUIV_POS1:
    case ProofRule::CNF_EQUIV_POS2:
    case ProofRule::CNF_EQUIV_NEG1:
    case ProofRule::CNF_EQUIV_NEG2:
    case ProofRule::CNF_XOR_POS1:
    case ProofRule::CNF_XOR_POS2:
    case ProofRule::CNF_XOR_NEG1:
    case ProofRule::CNF_XOR_NEG2:
    case ProofRule::CNF_ITE_POS1:
    case ProofRule::CNF_ITE_POS2:
    case ProofRule::CNF_ITE_POS3:
    case ProofRule::CNF_ITE_NEG1:
    case ProofRule::CNF_ITE_NEG2:
    case ProofRule::CNF_ITE_NEG3:
    case ProofRule::CNF_AND_POS:
    case ProofRule::FACTORING:
    case ProofRule::REORDERING:
    case ProofRule::RESOLUTION:
    case ProofRule::CHAIN_RESOLUTION:
    case ProofRule::ARRAYS_READ_OVER_WRITE:
    case ProofRule::ARRAYS_READ_OVER_WRITE_CONTRA:
    case ProofRule::ARRAYS_READ_OVER_WRITE_1:
    case ProofRule::ARRAYS_EXT:
    case ProofRule::ARITH_SUM_UB:
    case ProofRule::ARITH_MULT_POS:
    case ProofRule::ARITH_MULT_NEG:
    case ProofRule::ARITH_MULT_TANGENT:
    case ProofRule::ARITH_TRICHOTOMY:
    case ProofRule::ARITH_TRANS_EXP_NEG:
    case ProofRule::ARITH_TRANS_EXP_POSITIVITY:
    case ProofRule::ARITH_TRANS_EXP_SUPER_LIN:
    case ProofRule::ARITH_TRANS_EXP_ZERO:
    case ProofRule::ARITH_TRANS_SINE_BOUNDS:
    case ProofRule::ARITH_TRANS_SINE_SYMMETRY:
    case ProofRule::ARITH_TRANS_SINE_TANGENT_ZERO:
    case ProofRule::ARITH_TRANS_SINE_TANGENT_PI:
    case ProofRule::INT_TIGHT_LB:
    case ProofRule::INT_TIGHT_UB:
    case ProofRule::SKOLEM_INTRO:
    case ProofRule::SETS_SINGLETON_INJ:
    case ProofRule::SETS_EXT:
    case ProofRule::SETS_FILTER_UP:
    case ProofRule::SETS_FILTER_DOWN:
    case ProofRule::CONCAT_EQ:
    case ProofRule::CONCAT_UNIFY:
    case ProofRule::CONCAT_CSPLIT:
    case ProofRule::CONCAT_CPROP:
    case ProofRule::CONCAT_CONFLICT:
    case ProofRule::CONCAT_CONFLICT_DEQ:
    case ProofRule::CONCAT_SPLIT:
    case ProofRule::CONCAT_LPROP:
    case ProofRule::STRING_LENGTH_POS:
    case ProofRule::STRING_LENGTH_NON_EMPTY:
    case ProofRule::RE_INTER:
    case ProofRule::RE_UNFOLD_POS:
    case ProofRule::RE_UNFOLD_NEG_CONCAT_FIXED:
    case ProofRule::RE_UNFOLD_NEG:
    case ProofRule::STRING_CODE_INJ:
    case ProofRule::STRING_SEQ_UNIT_INJ:
    case ProofRule::STRING_DECOMPOSE:
    case ProofRule::STRING_EXT:
    case ProofRule::DT_SPLIT:
    case ProofRule::ITE_EQ:
    case ProofRule::INSTANTIATE:
    case ProofRule::SKOLEMIZE:
    case ProofRule::ALPHA_EQUIV:
    case ProofRule::QUANT_VAR_REORDERING:
    case ProofRule::ENCODE_EQ_INTRO:
    case ProofRule::HO_APP_ENCODE:
    case ProofRule::BV_EAGER_ATOM:
    case ProofRule::ACI_NORM:
    case ProofRule::ARITH_POLY_NORM:
    case ProofRule::ARITH_POLY_NORM_REL:
    case ProofRule::DSL_REWRITE: return true;
    case ProofRule::BV_BITBLAST_STEP:
    {
      return isHandledBitblastStep(pfn->getArguments()[0]);
    }
    break;
    case ProofRule::THEORY_REWRITE:
    {
      ProofRewriteRule id;
      rewriter::getRewriteRule(pfn->getArguments()[0], id);
      return isHandledTheoryRewrite(id, pfn->getArguments()[1]);
    }
    break;
    case ProofRule::ARITH_REDUCTION:
    {
      Kind k = pargs[0].getKind();
      return k == Kind::TO_INTEGER || k == Kind::IS_INTEGER
             || k == Kind::DIVISION || k == Kind::DIVISION_TOTAL
             || k == Kind::INTS_DIVISION || k == Kind::INTS_DIVISION_TOTAL
             || k == Kind::INTS_MODULUS || k == Kind::INTS_MODULUS_TOTAL
             || k == Kind::ABS;
    }
    break;
    case ProofRule::STRING_REDUCTION:
    {
      // depends on the operator
      Assert(!pargs.empty());
      Kind k = pargs[0].getKind();
      switch (k)
      {
        case Kind::STRING_SUBSTR:
        case Kind::STRING_INDEXOF:
        case Kind::STRING_REPLACE:
        case Kind::STRING_STOI:
        case Kind::STRING_ITOS:
        case Kind::SEQ_NTH:
          return true;
        default:
          break;
      }
      Trace("alf-printer-debug") << "Cannot STRING_REDUCTION " << k << std::endl;
      return false;
    }
    break;
    case ProofRule::STRING_EAGER_REDUCTION:
    {
      // depends on the operator
      Assert(!pargs.empty());
      Kind k = pargs[0].getKind();
      if (k == Kind::STRING_TO_CODE || k == Kind::STRING_FROM_CODE)
      {
        // must use standard alphabet size
        return opts.strings.stringsAlphaCard == String::num_codes();
      }
      return k == Kind::STRING_CONTAINS || k == Kind::STRING_INDEXOF
             || k == Kind::STRING_INDEXOF_RE || k == Kind::STRING_IN_REGEXP
             || k == Kind::STRING_STOI;
    }
    break;
    //
    case ProofRule::EVALUATE:
    {
      if (canEvaluate(pargs[0]))
      {
        Trace("alf-printer-debug") << "Can evaluate " << pargs[0] << std::endl;
        return true;
      }
    }
    break;
    // otherwise not handled
    default: break;
  }
  return false;
}

bool AlfPrinter::isHandledTheoryRewrite(ProofRewriteRule id, const Node& n)
{
  switch (id)
  {
    case ProofRewriteRule::DISTINCT_ELIM:
    case ProofRewriteRule::BETA_REDUCE:
    case ProofRewriteRule::LAMBDA_ELIM:
    case ProofRewriteRule::ARITH_POW_ELIM:
    case ProofRewriteRule::ARITH_STRING_PRED_ENTAIL:
    case ProofRewriteRule::ARITH_STRING_PRED_SAFE_APPROX:
    case ProofRewriteRule::EXISTS_ELIM:
    case ProofRewriteRule::QUANT_UNUSED_VARS:
    case ProofRewriteRule::ARRAYS_SELECT_CONST:
    case ProofRewriteRule::DT_INST:
    case ProofRewriteRule::DT_COLLAPSE_SELECTOR:
    case ProofRewriteRule::DT_COLLAPSE_TESTER:
    case ProofRewriteRule::DT_COLLAPSE_TESTER_SINGLETON:
    case ProofRewriteRule::DT_CONS_EQ:
    case ProofRewriteRule::DT_CONS_EQ_CLASH:
    case ProofRewriteRule::DT_CYCLE:
    case ProofRewriteRule::QUANT_MERGE_PRENEX:
    case ProofRewriteRule::QUANT_MINISCOPE_AND:
    case ProofRewriteRule::QUANT_MINISCOPE_OR:
    case ProofRewriteRule::QUANT_MINISCOPE_ITE:
    case ProofRewriteRule::QUANT_VAR_ELIM_EQ:
    case ProofRewriteRule::RE_LOOP_ELIM:
    case ProofRewriteRule::SETS_IS_EMPTY_EVAL:
    case ProofRewriteRule::SETS_INSERT_ELIM:
    case ProofRewriteRule::STR_IN_RE_CONCAT_STAR_CHAR:
    case ProofRewriteRule::STR_IN_RE_SIGMA:
    case ProofRewriteRule::STR_IN_RE_SIGMA_STAR:
    case ProofRewriteRule::STR_IN_RE_CONSUME:
    case ProofRewriteRule::RE_INTER_UNION_INCLUSION:
    case ProofRewriteRule::BV_REPEAT_ELIM:
    case ProofRewriteRule::BV_BITWISE_SLICING: return true;
    case ProofRewriteRule::STR_IN_RE_EVAL:
      Assert(n[0].getKind() == Kind::STRING_IN_REGEXP && n[0][0].isConst());
      return canEvaluateRegExp(n[0][1]);
    default: break;
  }
  return false;
}

bool AlfPrinter::isHandledBitblastStep(const Node& eq)
{
  Assert(eq.getKind() == Kind::EQUAL);
  if (eq[0].isVar())
  {
    return true;
  }
  switch (eq[0].getKind())
  {
    case Kind::CONST_BITVECTOR:
    case Kind::BITVECTOR_EXTRACT:
    case Kind::BITVECTOR_CONCAT:
    case Kind::EQUAL: return true;
    default:
      Trace("alf-printer-debug") << "Cannot bitblast  " << eq[0] << std::endl;
      break;
  }
  return false;
}

bool AlfPrinter::canEvaluate(Node n)
{
  std::unordered_set<TNode> visited;
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
      switch (cur.getKind())
      {
        case Kind::ITE:
        case Kind::NOT:
        case Kind::AND:
        case Kind::OR:
        case Kind::XOR:
        case Kind::CONST_BOOLEAN:
        case Kind::CONST_INTEGER:
        case Kind::CONST_RATIONAL:
        case Kind::CONST_STRING:
        case Kind::CONST_BITVECTOR:
        case Kind::ADD:
        case Kind::SUB:
        case Kind::NEG:
        case Kind::LT:
        case Kind::GT:
        case Kind::GEQ:
        case Kind::LEQ:
        case Kind::MULT:
        case Kind::NONLINEAR_MULT:
        case Kind::INTS_MODULUS:
        case Kind::INTS_MODULUS_TOTAL:
        case Kind::DIVISION:
        case Kind::DIVISION_TOTAL:
        case Kind::INTS_DIVISION:
        case Kind::INTS_DIVISION_TOTAL:
        case Kind::INTS_ISPOW2:
        case Kind::INTS_LOG2:
        case Kind::POW2:
        case Kind::TO_REAL:
        case Kind::TO_INTEGER:
        case Kind::IS_INTEGER:
        case Kind::ABS:
        case Kind::STRING_CONCAT:
        case Kind::STRING_SUBSTR:
        case Kind::STRING_LENGTH:
        case Kind::STRING_CONTAINS:
        case Kind::STRING_REPLACE:
        case Kind::STRING_INDEXOF:
        case Kind::STRING_TO_CODE:
        case Kind::STRING_FROM_CODE:
        case Kind::STRING_PREFIX:
        case Kind::STRING_ITOS:
        case Kind::STRING_STOI:
        case Kind::BITVECTOR_EXTRACT:
        case Kind::BITVECTOR_CONCAT:
        case Kind::BITVECTOR_ADD:
        case Kind::BITVECTOR_SUB:
        case Kind::BITVECTOR_NEG:
        case Kind::BITVECTOR_NOT:
        case Kind::BITVECTOR_MULT:
        case Kind::BITVECTOR_UDIV:
        case Kind::BITVECTOR_UREM:
        case Kind::BITVECTOR_SHL:
        case Kind::BITVECTOR_LSHR:
        case Kind::BITVECTOR_ASHR:
        case Kind::BITVECTOR_AND:
        case Kind::BITVECTOR_OR:
        case Kind::BITVECTOR_XOR:
        case Kind::BITVECTOR_ULT:
        case Kind::BITVECTOR_ULE:
        case Kind::BITVECTOR_UGT:
        case Kind::BITVECTOR_UGE:
        case Kind::BITVECTOR_SLT:
        case Kind::BITVECTOR_SLE:
        case Kind::BITVECTOR_SGT:
        case Kind::BITVECTOR_SGE:
        case Kind::BITVECTOR_REPEAT:
        case Kind::BITVECTOR_SIGN_EXTEND:
        case Kind::BITVECTOR_ZERO_EXTEND:
        case Kind::CONST_BITVECTOR_SYMBOLIC:
        case Kind::BITVECTOR_TO_NAT:
        case Kind::INT_TO_BITVECTOR: break;
        case Kind::EQUAL:
        {
          TypeNode tn = cur[0].getType();
          if (!tn.isBoolean() && !tn.isReal() && !tn.isInteger()
              && !tn.isString() && !tn.isBitVector())
          {
            return false;
          }
        }
        break;
        case Kind::BITVECTOR_SIZE:
          // special case, evaluates no matter what is inside
          continue;
        default:
          Trace("alf-printer-debug")
              << "Cannot evaluate " << cur.getKind() << std::endl;
          return false;
      }
      for (const Node& cn : cur)
      {
        visit.push_back(cn);
      }
    }
  } while (!visit.empty());
  return true;
}

bool AlfPrinter::canEvaluateRegExp(Node r)
{
  Assert(r.getType().isRegExp());
  Trace("alf-printer-debug") << "canEvaluateRegExp? " << r << std::endl;
  std::unordered_set<TNode> visited;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(r);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      switch (cur.getKind())
      {
        case Kind::REGEXP_ALL:
        case Kind::REGEXP_ALLCHAR:
        case Kind::REGEXP_COMPLEMENT:
        case Kind::REGEXP_NONE:
        case Kind::REGEXP_UNION:
        case Kind::REGEXP_INTER:
        case Kind::REGEXP_CONCAT:
        case Kind::REGEXP_STAR: break;
        case Kind::REGEXP_RANGE:
          if (!theory::strings::utils::isCharacterRange(cur))
          {
            Trace("alf-printer-debug") << "Non-char range" << std::endl;
            return false;
          }
          continue;
        case Kind::STRING_TO_REGEXP:
          if (!canEvaluate(cur[0]))
          {
            Trace("alf-printer-debug") << "Non-evaluatable string" << std::endl;
            return false;
          }
          continue;
        default:
          Trace("alf-printer-debug") << "Cannot evaluate " << cur.getKind()
                                     << " in regular expressions" << std::endl;
          return false;
      }
      for (const Node& cn : cur)
      {
        visit.push_back(cn);
      }
    }
  } while (!visit.empty());
  return true;
}

std::string AlfPrinter::getRuleName(const ProofNode* pfn) const
{
  ProofRule r = pfn->getRule();
  if (r == ProofRule::DSL_REWRITE)
  {
    ProofRewriteRule id;
    rewriter::getRewriteRule(pfn->getArguments()[0], id);
    std::stringstream ss;
    ss << id;
    return ss.str();
  }
  else if (r == ProofRule::THEORY_REWRITE)
  {
    ProofRewriteRule id;
    rewriter::getRewriteRule(pfn->getArguments()[0], id);
    std::stringstream ss;
    ss << id;
    return ss.str();
  }
  else if (r == ProofRule::ENCODE_EQ_INTRO || r == ProofRule::HO_APP_ENCODE
           || r == ProofRule::BV_EAGER_ATOM)
  {
    // ENCODE_EQ_INTRO proves (= t (convert t)) from argument t,
    // where (convert t) is indistinguishable from t according to the proof.
    // Similarly, HO_APP_ENCODE proves an equality between a term of kind
    // Kind::HO_APPLY and Kind::APPLY_UF, which denotes the same term in ALF.
    return "refl";
  }
  std::string name = toString(r);
  std::transform(name.begin(), name.end(), name.begin(), [](unsigned char c) {
    return std::tolower(c);
  });
  return name;
}

void AlfPrinter::printDslRule(std::ostream& out, ProofRewriteRule r)
{
  options::ioutils::applyPrintArithLitToken(out, true);
  options::ioutils::applyPrintSkolemDefinitions(out, true);
  const rewriter::RewriteProofRule& rpr = d_rdb->getRule(r);
  const std::vector<Node>& varList = rpr.getVarList();
  const std::vector<Node>& uvarList = rpr.getUserVarList();
  const std::vector<Node>& conds = rpr.getConditions();
  Node conc = rpr.getConclusion(true);
  // We must map variables of the rule to internal symbols (via
  // mkInternalSymbol) so that the ALF node converter will not treat the
  // BOUND_VARIABLE of this rule as user provided variables. The substitution
  // su stores this mapping.
  Subs su;
  out << "(declare-rule " << r << " (";
  AlfDependentTypeConverter adtc(nodeManager(), d_tproc);
  std::stringstream ssExplicit;
  std::map<std::string, size_t> nameCount;
  std::vector<Node> uviList;
  std::map<Node, Node> adtcConvMap;
  for (size_t i = 0, nvars = uvarList.size(); i < nvars; i++)
  {
    if (i > 0)
    {
      ssExplicit << " ";
    }
    const Node& uv = uvarList[i];
    std::stringstream sss;
    sss << uv;
    // Use a consistent variable name, which e.g. ensures that minor changes
    // to the RARE rules do not induce major changes in the CPC definition.
    // Below, we have a variable when the user has named x (which itself may
    // contain digits), and the cvc5 RARE parser has renamed to xN where N is
    // <numeral>+. We rename this to xM where M is the number of times we have
    // seen a variable with prefix M. For example, the variable `x1s2` may be
    // renamed to `x1s2123`, which will be renamed to `x1s1` here.
    std::string str = sss.str();
    size_t index = str.find_last_not_of("0123456789");
    std::string result = str.substr(0, index + 1);
    sss.str("");
    nameCount[result]++;
    sss << result << nameCount[result];
    Node uvi = d_tproc.mkInternalSymbol(sss.str(), uv.getType());
    uviList.emplace_back(uvi);
    su.add(varList[i], uvi);
    ssExplicit << "(" << sss.str() << " ";
    TypeNode uvt = uv.getType();
    Node uvtp = adtc.process(uvt);
    adtcConvMap[uvi] = uvtp;
    ssExplicit << uvtp;
    if (expr::isListVar(uv))
    {
      // carry over whether it is a list variable
      expr::markListVar(uvi);
      ssExplicit << " :list";
    }
    ssExplicit << ")";
  }
  // print implicit parameters introduced in dependent type conversion
  const std::vector<Node>& params = adtc.getFreeParameters();
  for (const Node& p : params)
  {
    out << "(" << p << " " << p.getType() << ") ";
  }
  // carry the mapping from symbols to their types, which is used when
  // eliminating internal-only operators for representing empty set and sequence
  AlfListNodeConverter ltproc(nodeManager(), d_tproc, adtcConvMap);
  // now print variables of the proof rule
  out << ssExplicit.str();
  out << ")" << std::endl;
  if (!conds.empty())
  {
    out << "  :premises (";
    bool firstTime = true;
    for (const Node& c : conds)
    {
      if (firstTime)
      {
        firstTime = false;
      }
      else
      {
        out << " ";
      }
      // note we apply list conversion to premises as well.
      Node cc = d_tproc.convert(su.apply(c));
      cc = ltproc.convert(cc);
      out << cc;
    }
    out << ")" << std::endl;
  }
  out << "  :args (";
  bool printedArg = false;
  for (const Node& v : uviList)
  {
    out << (printedArg ? " " : "");
    printedArg = true;
    out << v;
  }
  // Special case: must print explicit types.
  // This is to handle rules where Kind::TYPE_OF appears in the conclusion
  // or in the premises. Since RARE rules do not take types as arguments,
  // we must add them here. The printer for proof steps will add them in
  // a similar manner.
  std::vector<Node> explictTypeOf = rpr.getExplicitTypeOfList();
  std::map<Node, Node>::iterator itet;
  for (const Node& et : explictTypeOf)
  {
    out << (printedArg ? " " : "");
    printedArg = true;
    Assert(et.getKind() == Kind::TYPE_OF);
    Node v = su.apply(et[0]);
    itet = adtcConvMap.find(v);
    Assert(itet != adtcConvMap.end());
    out << itet->second;
  }
  out << ")" << std::endl;
  Node sconc = d_tproc.convert(su.apply(conc));
  sconc = ltproc.convert(sconc);
  Assert(sconc.getKind() == Kind::EQUAL);
  out << "  :conclusion (= " << sconc[0] << " " << sconc[1] << ")" << std::endl;
  out << ")" << std::endl;
}

LetBinding* AlfPrinter::getLetBinding() { return d_lbindUse; }

void AlfPrinter::printLetList(std::ostream& out, LetBinding& lbind)
{
  std::vector<Node> letList;
  lbind.letify(letList);
  std::map<Node, size_t>::const_iterator it;
  for (size_t i = 0, nlets = letList.size(); i < nlets; i++)
  {
    Node n = letList[i];
    // use define command which does not invoke type checking
    out << "(define " << d_termLetPrefix << lbind.getId(n);
    out << " () ";
    Printer::getPrinter(out)->toStream(out, n, &lbind, false);
    out << ")" << std::endl;
  }
}

void AlfPrinter::print(std::ostream& out,
                       std::shared_ptr<ProofNode> pfn,
                       ProofScopeMode psm)
{
  // ensures options are set once and for all
  options::ioutils::applyOutputLanguage(out, Language::LANG_SMTLIB_V2_6);
  options::ioutils::applyPrintArithLitToken(out, true);
  options::ioutils::applyPrintSkolemDefinitions(out, true);
  // allocate a print channel
  AlfPrintChannelOut aprint(out, d_lbindUse, d_termLetPrefix, true);
  print(aprint, pfn, psm);
}

void AlfPrinter::print(AlfPrintChannelOut& aout,
                       std::shared_ptr<ProofNode> pfn,
                       ProofScopeMode psm)
{
  std::ostream& out = aout.getOStream();
  Assert(d_pletMap.empty());
  d_pfIdCounter = 0;

  const ProofNode* ascope = nullptr;
  const ProofNode* dscope = nullptr;
  const ProofNode* pnBody = nullptr;
  if (psm == ProofScopeMode::NONE)
  {
    pnBody = pfn.get();
  }
  else if (psm == ProofScopeMode::UNIFIED)
  {
    ascope = pfn.get();
    Assert(ascope->getRule() == ProofRule::SCOPE);
    pnBody = pfn->getChildren()[0].get();
  }
  else if (psm == ProofScopeMode::DEFINITIONS_AND_ASSERTIONS)
  {
    dscope = pfn.get();
    Assert(dscope->getRule() == ProofRule::SCOPE);
    ascope = pfn->getChildren()[0].get();
    Assert(ascope->getRule() == ProofRule::SCOPE);
    pnBody = pfn->getChildren()[0]->getChildren()[0].get();
  }

  // Get the definitions and assertions and print the declarations from them
  const std::vector<Node>& definitions =
      dscope != nullptr ? dscope->getArguments() : d_emptyVec;
  const std::vector<Node>& assertions =
      ascope != nullptr ? ascope->getArguments() : d_emptyVec;

  bool wasAlloc;
  for (size_t i = 0; i < 2; i++)
  {
    AlfPrintChannel* ao;
    if (i == 0)
    {
      ao = &d_aletify;
    }
    else
    {
      ao = &aout;
    }
    if (i == 1)
    {
      // do not need to print DSL rules
      if (!options().proof.proofPrintReference)
      {
        // [1] print the declarations
        printer::smt2::Smt2Printer alfp(printer::smt2::Variant::alf_variant);
        // we do not print declarations in a sorted manner to reduce overhead
        smt::PrintBenchmark pb(nodeManager(), &alfp, false, &d_tproc);
        std::stringstream outDecl;
        std::stringstream outDef;
        options::ioutils::applyPrintArithLitToken(outDef, true);
        pb.printDeclarationsFrom(outDecl, outDef, definitions, assertions);
        out << outDecl.str();
        // [2] print the definitions
        out << outDef.str();
      }
      // [3] print proof-level term bindings
      printLetList(out, d_lbind);
    }
    // [4] print (unique) assumptions, including definitions
    std::unordered_set<Node> processed;
    for (const Node& n : assertions)
    {
      if (processed.find(n) != processed.end())
      {
        continue;
      }
      processed.insert(n);
      size_t id = allocateAssumeId(n, wasAlloc);
      Node nc = d_tproc.convert(n);
      ao->printAssume(nc, id, false);
    }
    for (const Node& n : definitions)
    {
      if (n.getKind() != Kind::EQUAL)
      {
        // skip define-fun-rec?
        continue;
      }
      if (processed.find(n) != processed.end())
      {
        continue;
      }
      processed.insert(n);
      // define-fun are HO equalities that can be proven by refl
      size_t id = allocateAssumeId(n, wasAlloc);
      Node f = d_tproc.convert(n[0]);
      Node lam = d_tproc.convert(n[1]);
      ao->printStep("refl", f.eqNode(lam), id, {}, {lam});
    }
    // [5] print proof body
    printProofInternal(ao, pnBody, i == 1);
  }
}

void AlfPrinter::printNext(AlfPrintChannelOut& aout,
                           std::shared_ptr<ProofNode> pfn)
{
  const ProofNode* pnBody = pfn.get();
  // print with letification
  printProofInternal(&d_aletify, pnBody, false);
  // print the new let bindings
  std::ostream& out = aout.getOStream();
  // Print new terms from the let binding. note that this should print only
  // the terms we have yet to see so far.
  printLetList(out, d_lbind);
  // print the proof
  printProofInternal(&aout, pnBody, true);
}

void AlfPrinter::printProofInternal(AlfPrintChannel* out,
                                    const ProofNode* pn,
                                    bool addToCache)
{
  // the stack
  std::vector<const ProofNode*> visit;
  // Whether we have to process children.
  // This map is dependent on the proof assumption context, e.g. subproofs of
  // SCOPE are reprocessed if they happen to occur in different proof scopes.
  context::CDHashMap<const ProofNode*, bool> processingChildren(&d_passumeCtx);
  // helper iterators
  context::CDHashMap<const ProofNode*, bool>::iterator pit;
  const ProofNode* cur;
  visit.push_back(pn);
  do
  {
    cur = visit.back();
    if (d_alreadyPrinted.find(cur) != d_alreadyPrinted.end())
    {
      visit.pop_back();
      continue;
    }
    pit = processingChildren.find(cur);
    if (pit == processingChildren.end())
    {
      ProofRule r = cur->getRule();
      if (r == ProofRule::ASSUME)
      {
        // ignore
        visit.pop_back();
        continue;
      }
      // print preorder traversal
      printStepPre(out, cur);
      processingChildren[cur] = true;
      // will revisit this proof node
      std::vector<std::shared_ptr<ProofNode>> children;
      getChildrenFromProofRule(cur, children);
      // visit each child
      for (const std::shared_ptr<ProofNode>& c : children)
      {
        visit.push_back(c.get());
      }
      continue;
    }
    visit.pop_back();
    if (pit->second)
    {
      processingChildren[cur] = false;
      // print postorder traversal
      printStepPost(out, cur);
      if (addToCache)
      {
        d_alreadyPrinted.insert(cur);
      }
    }
  } while (!visit.empty());
}

void AlfPrinter::printStepPre(AlfPrintChannel* out, const ProofNode* pn)
{
  // if we haven't yet allocated a proof id, do it now
  ProofRule r = pn->getRule();
  if (r == ProofRule::SCOPE)
  {
    // The assumptions only are valid within the body of the SCOPE, thus
    // we push a context scope.
    d_passumeCtx.push();
    const std::vector<Node>& args = pn->getArguments();
    for (const Node& a : args)
    {
      size_t aid = allocateAssumePushId(pn, a);
      Node aa = d_tproc.convert(a);
      // print a push
      out->printAssume(aa, aid, true);
    }
  }
}

void AlfPrinter::getChildrenFromProofRule(
    const ProofNode* pn, std::vector<std::shared_ptr<ProofNode>>& children)
{
  const std::vector<std::shared_ptr<ProofNode>>& cc = pn->getChildren();
  switch (pn->getRule())
  {
    case ProofRule::CONG:
    {
      Node res = pn->getResult();
      if (res[0].isClosure())
      {
        // Ignore the children after the required arguments.
        // This ensures that we ignore e.g. equalities between patterns
        // which can appear in term conversion proofs.
        size_t arity = kind::metakind::getMinArityForKind(res[0].getKind());
        children.insert(children.end(), cc.begin(), cc.begin() + arity - 1);
        return;
      }
    }
    break;
    default: break;
  }
  children.insert(children.end(), cc.begin(), cc.end());
}

void AlfPrinter::getArgsFromProofRule(const ProofNode* pn,
                                      std::vector<Node>& args)
{
  Node res = pn->getResult();
  const std::vector<Node> pargs = pn->getArguments();
  ProofRule r = pn->getRule();
  switch (r)
  {
    case ProofRule::CONG:
    case ProofRule::NARY_CONG:
    case ProofRule::ARITH_POLY_NORM_REL:
    {
      Node op = d_tproc.getOperatorOfTerm(res[0], true);
      args.push_back(d_tproc.convert(op));
      return;
    }
    break;
    case ProofRule::HO_CONG:
    {
      // argument is ignored
      return;
    }
    case ProofRule::INSTANTIATE:
    {
      // ignore arguments past the term vector
      Node ts = d_tproc.convert(pargs[0]);
      args.push_back(ts);
      return;
    }
    case ProofRule::DSL_REWRITE:
    {
      ProofRewriteRule dr;
      if (!rewriter::getRewriteRule(pargs[0], dr))
      {
        Unhandled() << "Failed to get DSL proof rule";
      }
      Trace("alf-printer-debug") << "Get args for " << dr << std::endl;
      const rewriter::RewriteProofRule& rpr = d_rdb->getRule(dr);
      std::vector<Node> ss(pargs.begin() + 1, pargs.end());
      std::vector<std::pair<Kind, std::vector<Node>>> witnessTerms;
      rpr.getConclusionFor(ss, witnessTerms);
      // the arguments are the computed witness terms
      for (const std::pair<Kind, std::vector<Node>>& w : witnessTerms)
      {
        if (w.first == Kind::UNDEFINED_KIND)
        {
          Assert(w.second.size() == 1);
          args.push_back(d_tproc.convert(w.second[0]));
        }
        else
        {
          std::vector<Node> wargs;
          for (const Node& wc : w.second)
          {
            wargs.push_back(d_tproc.convert(wc));
          }
          args.push_back(d_tproc.mkInternalApp(
              printer::smt2::Smt2Printer::smtKindString(w.first),
              wargs,
              d_absType));
        }
      }
      // special case: explicit type-of terms, which require explicit type
      // arguments
      std::map<ProofRewriteRule, std::vector<Node>>::iterator it =
          d_explicitTypeOf.find(dr);
      if (it == d_explicitTypeOf.end())
      {
        d_explicitTypeOf[dr] = rpr.getExplicitTypeOfList();
        it = d_explicitTypeOf.find(dr);
      }
      if (!it->second.empty())
      {
        const std::vector<Node>& fvs = rpr.getVarList();
        AlwaysAssert(fvs.size() == ss.size());
        for (const Node& t : it->second)
        {
          Assert(t.getKind() == Kind::TYPE_OF);
          Node tts =
              t[0].substitute(fvs.begin(), fvs.end(), ss.begin(), ss.end());
          args.push_back(d_tproc.typeAsNode(tts.getType()));
        }
      }
      return;
    }
    case ProofRule::THEORY_REWRITE:
    {
      // ignore the identifier
      Assert(pargs.size() == 2);
      args.push_back(d_tproc.convert(pargs[1]));
      return;
    }
    break;
    default: break;
  }
  for (size_t i = 0, nargs = pargs.size(); i < nargs; i++)
  {
    Node av = d_tproc.convert(pargs[i]);
    args.push_back(av);
  }
}

void AlfPrinter::printStepPost(AlfPrintChannel* out, const ProofNode* pn)
{
  Assert(pn->getRule() != ProofRule::ASSUME);
  // if we have yet to allocate a proof id, do it now
  bool wasAlloc = false;
  TNode conclusion = d_tproc.convert(pn->getResult());
  TNode conclusionPrint;
  // print conclusion only if option is set, or this is false
  if (options().proof.proofPrintConclusion || conclusion == d_false)
  {
    conclusionPrint = conclusion;
  }
  ProofRule r = pn->getRule();
  std::vector<std::shared_ptr<ProofNode>> children;
  getChildrenFromProofRule(pn, children);
  std::vector<Node> args;
  bool handled = isHandled(options(), pn);
  if (handled)
  {
    getArgsFromProofRule(pn, args);
  }
  size_t id = allocateProofId(pn, wasAlloc);
  std::vector<size_t> premises;
  // get the premises
  context::CDHashMap<Node, size_t>::iterator ita;
  std::map<const ProofNode*, size_t>::iterator itp;
  for (const std::shared_ptr<ProofNode>& c : children)
  {
    size_t pid;
    // if assume, lookup in passumeMap
    if (c->getRule() == ProofRule::ASSUME)
    {
      ita = d_passumeMap.find(c->getResult());
      Assert(ita != d_passumeMap.end());
      pid = ita->second;
    }
    else
    {
      itp = d_pletMap.find(c.get());
      Assert(itp != d_pletMap.end());
      pid = itp->second;
    }
    premises.push_back(pid);
  }
  // if we don't handle the rule, print trust
  if (!handled)
  {
    if (!options().proof.proofAllowTrust)
    {
      std::stringstream ss;
      ss << pn->getRule();
      if (pn->getRule() == ProofRule::THEORY_REWRITE)
      {
        ProofRewriteRule prid;
        rewriter::getRewriteRule(pn->getArguments()[0], prid);
        ss << " (" << prid << ")";
      }
      else if (pn->getRule() == ProofRule::TRUST)
      {
        TrustId tid;
        getTrustId(pn->getArguments()[0], tid);
        ss << " (" << tid << ")";
      }
      Trace("alf-pf-hole") << "Proof rule " << ss.str() << ": "
                           << pn->getResult() << std::endl;
      Unreachable() << "An ALF proof equires a trust step for " << ss.str()
                    << ", but --" << options::proof::longName::proofAllowTrust
                    << " is false" << std::endl;
    }
    out->printTrustStep(pn->getRule(),
                        conclusionPrint,
                        id,
                        premises,
                        pn->getArguments(),
                        conclusion);
    return;
  }
  std::string rname = getRuleName(pn);
  if (r == ProofRule::SCOPE)
  {
    if (args.empty())
    {
      // If there are no premises, any reference to this proof can just refer to
      // the body.
      d_pletMap[pn] = premises[0];
    }
    else
    {
      // Assuming the body of the scope has identifier id_0, the following prints:
      // (step-pop id_1 :rule scope :premises (id_0))
      // ...
      // (step-pop id_n :rule scope :premises (id_{n-1}))
      // (step id :rule process_scope :premises (id_n) :args (C))
      size_t tmpId;
      for (size_t i = 0, nargs = args.size(); i < nargs; i++)
      {
        // Manually increment proof id counter and premises. Note they will only be
        // used locally here to chain together the pops mentioned above.
        tmpId = d_pfIdCounter;
        d_pfIdCounter++;
        out->printStep(rname, Node::null(), tmpId, premises, {}, true);
        // The current id is the premises of the next.
        premises.clear();
        premises.push_back(tmpId);
      }
      // Finish with the process scope step.
      std::vector<Node> pargs;
      pargs.push_back(d_tproc.convert(children[0]->getResult()));
      out->printStep("process_scope", conclusionPrint, id, premises, pargs);
    }
    // We are done with the assumptions in scope, pop a context.
    d_passumeCtx.pop();
  }
  else
  {
    out->printStep(rname, conclusionPrint, id, premises, args);
  }
}

size_t AlfPrinter::allocateAssumePushId(const ProofNode* pn, const Node& a)
{
  std::pair<const ProofNode*, Node> key(pn, a);

  bool wasAlloc = false;
  size_t aid = allocateAssumeId(a, wasAlloc);
  // if we assigned an id to the assumption
  if (!wasAlloc)
  {
    // otherwise we shadow, just use a dummy
    d_pfIdCounter++;
    aid = d_pfIdCounter;
  }
  return aid;
}

size_t AlfPrinter::allocateAssumeId(const Node& n, bool& wasAlloc)
{
  context::CDHashMap<Node, size_t>::iterator it = d_passumeMap.find(n);
  if (it != d_passumeMap.end())
  {
    wasAlloc = false;
    return it->second;
  }
  wasAlloc = true;
  d_pfIdCounter++;
  d_passumeMap[n] = d_pfIdCounter;
  return d_pfIdCounter;
}

size_t AlfPrinter::allocateProofId(const ProofNode* pn, bool& wasAlloc)
{
  std::map<const ProofNode*, size_t>::iterator it = d_pletMap.find(pn);
  if (it != d_pletMap.end())
  {
    wasAlloc = false;
    return it->second;
  }
  wasAlloc = true;
  d_pfIdCounter++;
  d_pletMap[pn] = d_pfIdCounter;
  return d_pfIdCounter;
}

}  // namespace proof
}  // namespace cvc5::internal
