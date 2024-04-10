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
#include "printer/printer.h"
#include "proof/proof_node_to_sexpr.h"
#include "rewriter/rewrite_db.h"
#include "smt/print_benchmark.h"
#include "theory/strings/theory_strings_utils.h"

namespace cvc5::internal {

namespace proof {

AlfPrinter::AlfPrinter(Env& env, BaseAlfNodeConverter& atp)
    : EnvObj(env), d_tproc(atp), d_termLetPrefix("@t")
{
  d_pfType = nodeManager()->mkSort("proofType");
  d_false = nodeManager()->mkConst(false);
}

bool AlfPrinter::isHandled(const ProofNode* pfn) const
{
  const std::vector<Node> pargs = pfn->getArguments();
  switch (pfn->getRule())
  {
    // List of handled rules
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
    case ProofRule::ARITH_TRICHOTOMY:
    case ProofRule::INT_TIGHT_LB:
    case ProofRule::INT_TIGHT_UB:
    case ProofRule::SKOLEM_INTRO:
    case ProofRule::CONCAT_EQ:
    case ProofRule::CONCAT_UNIFY:
    case ProofRule::CONCAT_CSPLIT:
    case ProofRule::CONCAT_CONFLICT:
    case ProofRule::STRING_LENGTH_POS:
    case ProofRule::STRING_LENGTH_NON_EMPTY:
    case ProofRule::RE_INTER:
    case ProofRule::RE_UNFOLD_POS:
    case ProofRule::REMOVE_TERM_FORMULA_AXIOM:
    case ProofRule::INSTANTIATE:
    case ProofRule::SKOLEMIZE:
    case ProofRule::ALPHA_EQUIV:
    case ProofRule::ENCODE_PRED_TRANSFORM:
    case ProofRule::DSL_REWRITE: return true;
    case ProofRule::ARITH_POLY_NORM:
    {
      // we don't support bitvectors yet
      Assert(pargs[0].getKind() == Kind::EQUAL);
      if (pargs[0][0].getType().isBoolean())
      {
        return pargs[0][0][0].getType().isRealOrInt();
      }
      return pargs[0][0].getType().isRealOrInt();
    }
    break;
    case ProofRule::STRING_REDUCTION:
    {
      // depends on the operator
      Assert(!pargs.empty());
      Kind k = pargs[0].getKind();
      return k == Kind::STRING_SUBSTR || k == Kind::STRING_INDEXOF;
    }
    break;
    case ProofRule::STRING_EAGER_REDUCTION:
    {
      // depends on the operator
      Assert(!pargs.empty());
      Kind k = pargs[0].getKind();
      return k == Kind::STRING_CONTAINS || k == Kind::STRING_TO_CODE
             || k == Kind::STRING_INDEXOF;
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

bool AlfPrinter::canEvaluate(Node n) const
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
        case Kind::NOT:
        case Kind::AND:
        case Kind::OR:
        case Kind::XOR:
        case Kind::CONST_BOOLEAN:
        case Kind::CONST_INTEGER:
        case Kind::CONST_RATIONAL:
        case Kind::CONST_STRING:
        case Kind::ADD:
        case Kind::SUB:
        case Kind::NEG:
        case Kind::EQUAL:
        case Kind::LT:
        case Kind::GT:
        case Kind::GEQ:
        case Kind::LEQ:
        case Kind::MULT:
        case Kind::NONLINEAR_MULT:
        case Kind::STRING_CONCAT:
        case Kind::STRING_SUBSTR:
        case Kind::STRING_LENGTH:
        case Kind::STRING_CONTAINS:
        case Kind::BITVECTOR_ADD:
        case Kind::BITVECTOR_SUB:
        case Kind::BITVECTOR_NEG:
        case Kind::BITVECTOR_MULT:
        case Kind::BITVECTOR_AND:
        case Kind::BITVECTOR_OR: break;
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

std::string AlfPrinter::getRuleName(const ProofNode* pfn)
{
  ProofRule r = pfn->getRule();
  std::string name = toString(r);
  std::transform(name.begin(), name.end(), name.begin(), [](unsigned char c) {
    return std::tolower(c);
  });
  return name;
}

void AlfPrinter::printLetList(std::ostream& out, LetBinding& lbind)
{
  std::vector<Node> letList;
  lbind.letify(letList);
  std::map<Node, size_t>::const_iterator it;
  for (size_t i = 0, nlets = letList.size(); i < nlets; i++)
  {
    Node n = letList[i];
    Node def = lbind.convert(n, false);
    Node f = lbind.convert(n, true);
    // use define command which does not invoke type checking
    out << "(define " << f << " () " << def << ")" << std::endl;
  }
}

void AlfPrinter::print(std::ostream& out, std::shared_ptr<ProofNode> pfn)
{
  // ensures options are set once and for all
  options::ioutils::applyOutputLanguage(out, Language::LANG_SMTLIB_V2_6);
  options::ioutils::applyPrintArithLitToken(out, true);
  d_pfIdCounter = 0;

  // Get the definitions and assertions and print the declarations from them
  const std::vector<Node>& definitions = pfn->getArguments();
  const std::vector<Node>& assertions = pfn->getChildren()[0]->getArguments();
  const ProofNode* pnBody = pfn->getChildren()[0]->getChildren()[0].get();

  // Use a let binding if proofDagGlobal is true.
  // We can traverse binders due to the way we print global declare-var, since
  // terms beneath binders will always have their variables in scope and hence
  // can be printed in define commands.
  LetBinding lbind(d_termLetPrefix, 2, true);
  LetBinding* lbindUse = options().proof.proofDagGlobal ? &lbind : nullptr;
  AlfPrintChannelPre aletify(lbindUse);
  AlfPrintChannelOut aprint(out, lbindUse, d_termLetPrefix);

  d_pletMap.clear();
  d_passumeMap.clear();

  bool wasAlloc;
  for (size_t i = 0; i < 2; i++)
  {
    AlfPrintChannel* aout;
    if (i == 0)
    {
      aout = &aletify;
    }
    else
    {
      aout = &aprint;
    }
    if (i == 1)
    {
      std::stringstream outVars;
      const std::unordered_set<TNode>& vars = aletify.getVariables();
      for (TNode v : vars)
      {
        if (v.getKind() == Kind::BOUND_VARIABLE)
        {
          outVars << "(declare-var " << v << " " << v.getType() << ")"
                  << std::endl;
        }
      }
      if (options().proof.alfPrintReference)
      {
        // [1] print the reference
        // we currently do not need to provide a normalization routine.
        out << "(reference \"" << options().driver.filename << "\")"
            << std::endl;
        // [2] print the universal variables
        out << outVars.str();
      }
      else
      {
        // [1] print the types
        smt::PrintBenchmark pb(Printer::getPrinter(out), &d_tproc);
        std::stringstream outFuns;
        pb.printDeclarationsFrom(out, outFuns, definitions, assertions);
        // [2] print the universal variables
        out << outVars.str();
        // [3] print the declared functions
        out << outFuns.str();
      }
      // [4] print proof-level term bindings
      printLetList(out, lbind);
    }
    // [5] print (unique) assumptions
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
      aout->printAssume(nc, id, false);
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
      aout->printStep("refl", f.eqNode(lam), id, {}, {lam});
    }
    // [6] print proof body
    printProofInternal(aout, pnBody);
  }
}

void AlfPrinter::printProofInternal(AlfPrintChannel* out, const ProofNode* pn)
{
  // the stack
  std::vector<const ProofNode*> visit;
  // whether we have to process children
  std::unordered_map<const ProofNode*, bool> processingChildren;
  // helper iterators
  std::unordered_map<const ProofNode*, bool>::iterator pit;
  const ProofNode* cur;
  visit.push_back(pn);
  do
  {
    cur = visit.back();
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
    }
  } while (!visit.empty());
}

void AlfPrinter::printStepPre(AlfPrintChannel* out, const ProofNode* pn)
{
  // if we haven't yet allocated a proof id, do it now
  ProofRule r = pn->getRule();
  if (r == ProofRule::SCOPE)
  {
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
  bool handled = isHandled(pn);
  if (handled)
  {
    getArgsFromProofRule(pn, args);
  }
  size_t id = allocateProofId(pn, wasAlloc);
  std::vector<size_t> premises;
  // get the premises
  std::map<Node, size_t>::iterator ita;
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
  }
  else
  {
    out->printStep(rname, conclusionPrint, id, premises, args);
  }
}

size_t AlfPrinter::allocateAssumePushId(const ProofNode* pn, const Node& a)
{
  std::pair<const ProofNode*, Node> key(pn, a);
  std::map<std::pair<const ProofNode*, Node>, size_t>::iterator it =
      d_ppushMap.find(key);
  if (it != d_ppushMap.end())
  {
    return it->second;
  }
  bool wasAlloc = false;
  size_t aid = allocateAssumeId(a, wasAlloc);
  // if we assigned an id to the assumption
  if (!wasAlloc)
  {
    // otherwise we shadow, just use a dummy
    d_pfIdCounter++;
    aid = d_pfIdCounter;
  }
  d_ppushMap[key] = aid;
  return aid;
}

size_t AlfPrinter::allocateAssumeId(const Node& n, bool& wasAlloc)
{
  std::map<Node, size_t>::iterator it = d_passumeMap.find(n);
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
