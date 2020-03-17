/*********************                                                        */
/*! \file abstraction.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Aina Niemetz, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/
#include "theory/bv/abstraction.h"

#include "options/bv_options.h"
#include "smt/dump.h"
#include "smt/smt_statistics_registry.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/rewriter.h"


using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;
using namespace CVC4::context;

using namespace std;
using namespace CVC4::theory::bv::utils;

bool AbstractionModule::applyAbstraction(const std::vector<Node>& assertions,
                                         std::vector<Node>& new_assertions)
{
  Debug("bv-abstraction") << "AbstractionModule::applyAbstraction\n";

  TimerStat::CodeTimer abstractionTimer(d_statistics.d_abstractionTime);

  TNodeSet seen;
  for (unsigned i = 0; i < assertions.size(); ++i)
  {
    if (assertions[i].getKind() == kind::OR)
    {
      for (unsigned j = 0; j < assertions[i].getNumChildren(); ++j)
      {
        if (!isConjunctionOfAtoms(assertions[i][j], seen))
        {
          continue;
        }
        Node signature = computeSignature(assertions[i][j]);
        storeSignature(signature, assertions[i][j]);
        Debug("bv-abstraction") << "   assertion: " << assertions[i][j] << "\n";
        Debug("bv-abstraction") << "   signature: " << signature << "\n";
      }
    }
  }
  finalizeSignatures();

  for (unsigned i = 0; i < assertions.size(); ++i)
  {
    if (assertions[i].getKind() == kind::OR
        && assertions[i][0].getKind() == kind::AND)
    {
      std::vector<Node> new_children;
      for (unsigned j = 0; j < assertions[i].getNumChildren(); ++j)
      {
        if (hasSignature(assertions[i][j]))
        {
          new_children.push_back(abstractSignatures(assertions[i][j]));
        }
        else
        {
          new_children.push_back(assertions[i][j]);
        }
      }
      new_assertions.push_back(utils::mkOr(new_children));
    }
    else
    {
      // assertions that are not changed
      new_assertions.push_back(assertions[i]);
    }
  }

  if (options::skolemizeArguments())
  {
    skolemizeArguments(new_assertions);
  }

  // if we are using the eager solver reverse the abstraction
  if (options::bitblastMode() == options::BitblastMode::EAGER)
  {
    if (d_funcToSignature.size() == 0)
    {
      // we did not change anything
      return false;
    }
    NodeNodeMap seen_rev;
    for (unsigned i = 0; i < new_assertions.size(); ++i)
    {
      new_assertions[i] = reverseAbstraction(new_assertions[i], seen_rev);
    }
    // we undo the abstraction functions so the logic is QF_BV still
    return true;
  }

  // return true if we have created new function symbols for the problem
  return d_funcToSignature.size() != 0;
}

bool AbstractionModule::isConjunctionOfAtoms(TNode node, TNodeSet& seen)
{
  if (seen.find(node)!= seen.end())
    return true;

  if (!node.getType().isBitVector() && node.getKind() != kind::AND)
  {
    return utils::isBVPredicate(node);
  }

  if (node.getNumChildren() == 0)
    return true;

  for (unsigned i = 0; i < node.getNumChildren(); ++i) {
    if (!isConjunctionOfAtoms(node[i], seen))
    {
      return false;
    }
  }
  seen.insert(node);
  return true;
}


Node AbstractionModule::reverseAbstraction(Node assertion, NodeNodeMap& seen) {

  if (seen.find(assertion) != seen.end())
    return seen[assertion];

  if (isAbstraction(assertion)) {
    Node interp =  getInterpretation(assertion);
    seen[assertion] = interp;
    Assert(interp.getType() == assertion.getType());
    return interp;
  }

  if (assertion.getNumChildren() == 0) {
    seen[assertion] = assertion;
    return assertion;
  }

  NodeBuilder<> result(assertion.getKind());
  if (assertion.getMetaKind() == kind::metakind::PARAMETERIZED) {
    result << assertion.getOperator();
  }

  for (unsigned i = 0; i < assertion.getNumChildren(); ++i) {
    result << reverseAbstraction(assertion[i], seen);
  }
  Node res = result;
  seen[assertion] = res;
  return res;
}

void AbstractionModule::skolemizeArguments(std::vector<Node>& assertions)
{
  NodeManager* nm = NodeManager::currentNM();
  for (unsigned i = 0; i < assertions.size(); ++i)
  {
    TNode assertion = assertions[i];
    if (assertion.getKind() != kind::OR) continue;

    bool is_skolemizable = true;
    for (unsigned k = 0; k < assertion.getNumChildren(); ++k)
    {
      if (assertion[k].getKind() != kind::EQUAL
          || assertion[k][0].getKind() != kind::APPLY_UF
          || assertion[k][1].getKind() != kind::CONST_BITVECTOR
          || assertion[k][1].getConst<BitVector>() != BitVector(1, 1u))
      {
        is_skolemizable = false;
        break;
      }
    }

    if (!is_skolemizable) continue;

    ArgsTable assertion_table;

    // collect function symbols and their arguments
    for (unsigned j = 0; j < assertion.getNumChildren(); ++j)
    {
      TNode current = assertion[j];
      Assert(current.getKind() == kind::EQUAL
             && current[0].getKind() == kind::APPLY_UF);
      TNode func = current[0];
      ArgsVec args;
      for (unsigned k = 0; k < func.getNumChildren(); ++k)
      {
        args.push_back(func[k]);
      }
      assertion_table.addEntry(func.getOperator(), args);
    }

    NodeBuilder<> assertion_builder(kind::OR);
    // construct skolemized assertion
    for (ArgsTable::iterator it = assertion_table.begin();
         it != assertion_table.end();
         ++it)
    {
      // for each function symbol
      ++(d_statistics.d_numArgsSkolemized);
      TNode func = it->first;
      ArgsTableEntry& args = it->second;
      NodeBuilder<> skolem_func(kind::APPLY_UF);
      skolem_func << func;
      std::vector<Node> skolem_args;

      for (unsigned j = 0; j < args.getArity(); ++j)
      {
        bool all_same = true;
        for (unsigned k = 1; k < args.getNumEntries(); ++k)
        {
          if (args.getEntry(k)[j] != args.getEntry(0)[j]) all_same = false;
        }
        Node new_arg = all_same
                           ? (Node)args.getEntry(0)[j]
                           : utils::mkVar(utils::getSize(args.getEntry(0)[j]));
        skolem_args.push_back(new_arg);
        skolem_func << new_arg;
      }

      Node skolem_func_eq1 =
          nm->mkNode(kind::EQUAL, (Node)skolem_func, utils::mkConst(1, 1u));

      // enumerate arguments assignments
      std::vector<Node> or_assignments;
      for (const ArgsVec& av : args)
      // for (ArgsTableEntry::iterator it = args.begin(); it != args.end();
      // ++it)
      {
        NodeBuilder<> arg_assignment(kind::AND);
        // ArgsVec& args = *it;
        for (unsigned k = 0; k < av.size(); ++k)
        {
          Node eq = nm->mkNode(kind::EQUAL, av[k], skolem_args[k]);
          arg_assignment << eq;
        }
        or_assignments.push_back(arg_assignment);
      }

      Node new_func_def =
        utils::mkAnd(skolem_func_eq1, utils::mkOr(or_assignments));
      assertion_builder << new_func_def;
    }
    Node new_assertion = assertion_builder;
    Debug("bv-abstraction-dbg") << "AbstractionModule::skolemizeArguments "
                                << assertions[i] << " => \n";
    Debug("bv-abstraction-dbg") << "    " << new_assertion;
    assertions[i] = new_assertion;
  }
}

void AbstractionModule::storeSignature(Node signature, TNode assertion) {
  if(d_signatures.find(signature) == d_signatures.end()) {
    d_signatures[signature] = 0;
  }
  d_signatures[signature] = d_signatures[signature] + 1;
  d_assertionToSignature[assertion] = signature;
}

Node AbstractionModule::computeSignature(TNode node) {
  resetSignatureIndex();
  NodeNodeMap cache;
  Node sig = computeSignatureRec(node, cache);
  return sig;
}

Node AbstractionModule::getSignatureSkolem(TNode node)
{
  Assert(node.getMetaKind() == kind::metakind::VARIABLE);
  NodeManager* nm = NodeManager::currentNM();
  unsigned bitwidth = utils::getSize(node);
  if (d_signatureSkolems.find(bitwidth) == d_signatureSkolems.end())
  {
    d_signatureSkolems[bitwidth] = vector<Node>();
  }

  vector<Node>& skolems = d_signatureSkolems[bitwidth];
  // get the index of bv variables of this size
  unsigned index = getBitwidthIndex(bitwidth);
  Assert(skolems.size() + 1 >= index);
  if (skolems.size() == index)
  {
    ostringstream os;
    os << "sig_" << bitwidth << "_" << index;
    skolems.push_back(nm->mkSkolem(os.str(),
                                   nm->mkBitVectorType(bitwidth),
                                   "skolem for computing signatures"));
  }
  ++(d_signatureIndices[bitwidth]);
  return skolems[index];
}

unsigned AbstractionModule::getBitwidthIndex(unsigned bitwidth) {
  if (d_signatureIndices.find(bitwidth) == d_signatureIndices.end()) {
    d_signatureIndices[bitwidth] = 0;
  }
  return d_signatureIndices[bitwidth];
}

void AbstractionModule::resetSignatureIndex() {
  for (IndexMap::iterator it = d_signatureIndices.begin(); it != d_signatureIndices.end(); ++it) {
    it->second = 0;
  }
}

bool AbstractionModule::hasSignature(Node node) {
  return d_assertionToSignature.find(node) != d_assertionToSignature.end();
}

Node AbstractionModule::getGeneralizedSignature(Node node) {
  NodeNodeMap::const_iterator it = d_assertionToSignature.find(node);
  Assert(it != d_assertionToSignature.end());
  Node generalized_signature = getGeneralization(it->second);
  return generalized_signature;
}

Node AbstractionModule::computeSignatureRec(TNode node, NodeNodeMap& cache) {
  if (cache.find(node) != cache.end()) {
    return cache.find(node)->second;
  }

  if (node.getNumChildren() == 0) {
    if (node.getKind() == kind::CONST_BITVECTOR)
      return node;

    Node sig = getSignatureSkolem(node);
    cache[node] = sig;
    return sig;
  }

  NodeBuilder<> builder(node.getKind());
  if (node.getMetaKind() == kind::metakind::PARAMETERIZED) {
    builder << node.getOperator();
  }
  for (unsigned i = 0; i < node.getNumChildren(); ++i) {
    Node converted = computeSignatureRec(node[i], cache);
    builder << converted;
  }
  Node result = builder;
  cache[node] = result;
  return result;
}

/**
 * Returns 0, if the two are equal,
 * 1 if s is a generalization of t
 * 2 if t is a generalization of s
 * -1 if the two cannot be unified
 *
 * @param s
 * @param t
 *
 * @return
 */
int AbstractionModule::comparePatterns(TNode s, TNode t) {
  if (s.getKind() == kind::SKOLEM &&
      t.getKind() == kind::SKOLEM) {
    return 0;
  }

  if (s.getKind() == kind::CONST_BITVECTOR &&
      t.getKind() == kind::CONST_BITVECTOR) {
    if (s == t) {
      return 0;
    } else {
      return -1;
    }
  }

  if (s.getKind() == kind::SKOLEM &&
      t.getKind() == kind::CONST_BITVECTOR) {
    return 1;
  }

  if (s.getKind() == kind::CONST_BITVECTOR &&
      t.getKind() == kind::SKOLEM) {
    return 2;
  }

  if (s.getNumChildren() != t.getNumChildren() ||
      s.getKind() != t.getKind())
    return -1;

  int unify = 0;
  for (unsigned i = 0; i < s.getNumChildren(); ++i) {
    int unify_i = comparePatterns(s[i], t[i]);
    if (unify_i < 0)
      return -1;
    if (unify == 0) {
      unify = unify_i;
    } else if (unify != unify_i && unify_i != 0) {
      return -1;
    }
  }
  return unify;
}

TNode AbstractionModule::getGeneralization(TNode term) {
  NodeNodeMap::iterator it = d_sigToGeneralization.find(term);
  // if not in the map we add it
  if (it == d_sigToGeneralization.end()) {
    d_sigToGeneralization[term] = term;
    return term;
  }
  // doesn't have a generalization
  if (it->second == term)
    return term;

  TNode generalization = getGeneralization(it->second);
  Assert(generalization != term);
  d_sigToGeneralization[term] = generalization;
  return generalization;
}

void AbstractionModule::storeGeneralization(TNode s, TNode t) {
  Assert(s == getGeneralization(s));
  Assert(t == getGeneralization(t));
  d_sigToGeneralization[s] = t;
}

void AbstractionModule::finalizeSignatures()
{
  NodeManager* nm = NodeManager::currentNM();
  Debug("bv-abstraction")
      << "AbstractionModule::finalizeSignatures num signatures = "
      << d_signatures.size() << "\n";
  TNodeSet new_signatures;

  // "unify" signatures
  for (SignatureMap::const_iterator ss = d_signatures.begin();
       ss != d_signatures.end();
       ++ss)
  {
    for (SignatureMap::const_iterator tt = ss; tt != d_signatures.end(); ++tt)
    {
      TNode t = getGeneralization(tt->first);
      TNode s = getGeneralization(ss->first);

      if (t != s)
      {
        int status = comparePatterns(s, t);
        Assert(status);
        if (status < 0) continue;
        if (status == 1)
        {
          storeGeneralization(t, s);
        }
        else
        {
          storeGeneralization(s, t);
        }
      }
    }
  }
  // keep only most general signatures
  for (SignatureMap::iterator it = d_signatures.begin();
       it != d_signatures.end();)
  {
    TNode sig = it->first;
    TNode gen = getGeneralization(sig);
    if (sig != gen)
    {
      Assert(d_signatures.find(gen) != d_signatures.end());
      // update the count
      d_signatures[gen] += d_signatures[sig];
      d_signatures.erase(it++);
    }
    else
    {
      ++it;
    }
  }

  // remove signatures that are not frequent enough
  for (SignatureMap::iterator it = d_signatures.begin();
       it != d_signatures.end();)
  {
    if (it->second <= 7)
    {
      d_signatures.erase(it++);
    }
    else
    {
      ++it;
    }
  }

  for (SignatureMap::const_iterator it = d_signatures.begin();
       it != d_signatures.end();
       ++it)
  {
    TNode signature = it->first;
    // we already processed this signature
    Assert(d_signatureToFunc.find(signature) == d_signatureToFunc.end());

    Debug("bv-abstraction") << "Processing signature " << signature << " count "
                            << it->second << "\n";
    std::vector<TypeNode> arg_types;
    TNodeSet seen;
    collectArgumentTypes(signature, arg_types, seen);
    Assert(signature.getType().isBoolean());
    // make function return a bitvector of size 1
    // Node bv_function = nm->mkNode(kind::ITE, signature, utils::mkConst(1,
    // 1u), utils::mkConst(1, 0u));
    TypeNode range = nm->mkBitVectorType(1);

    TypeNode abs_type = nm->mkFunctionType(arg_types, range);
    Node abs_func =
        nm->mkSkolem("abs_$$", abs_type, "abstraction function for bv theory");
    Debug("bv-abstraction") << " abstracted by function " << abs_func << "\n";

    // NOTE: signature expression type is BOOLEAN
    d_signatureToFunc[signature] = abs_func;
    d_funcToSignature[abs_func] = signature;
  }

  d_statistics.d_numFunctionsAbstracted.setData(d_signatureToFunc.size());

  Debug("bv-abstraction") << "AbstractionModule::finalizeSignatures abstracted "
                          << d_signatureToFunc.size() << " signatures. \n";
}

void AbstractionModule::collectArgumentTypes(TNode sig, std::vector<TypeNode>& types, TNodeSet& seen) {
  if (seen.find(sig) != seen.end())
    return;

  if (sig.getKind() == kind::SKOLEM) {
    types.push_back(sig.getType());
    seen.insert(sig);
    return;
  }

  for (unsigned i = 0; i < sig.getNumChildren(); ++i) {
    collectArgumentTypes(sig[i], types, seen);
    seen.insert(sig);
  }
}

void AbstractionModule::collectArguments(TNode node, TNode signature, std::vector<Node>& args, TNodeSet& seen) {
  if (seen.find(node)!= seen.end())
    return;

  if (node.getMetaKind() == kind::metakind::VARIABLE
      || node.getKind() == kind::CONST_BITVECTOR)
  {
    // a constant in the node can either map to an argument of the abstraction
    // or can be hard-coded and part of the abstraction
    if (signature.getKind() == kind::SKOLEM) {
      args.push_back(node);
      seen.insert(node);
    } else {
      Assert(signature.getKind() == kind::CONST_BITVECTOR);
    }
    //
    return;
  }
  Assert(node.getKind() == signature.getKind()
         && node.getNumChildren() == signature.getNumChildren());

  for (unsigned i = 0; i < node.getNumChildren(); ++i) {
    collectArguments(node[i], signature[i], args, seen);
    seen.insert(node);
  }
}

Node AbstractionModule::abstractSignatures(TNode assertion)
{
  Debug("bv-abstraction") << "AbstractionModule::abstractSignatures "
                          << assertion << "\n";
  NodeManager* nm = NodeManager::currentNM();
  // assume the assertion has been fully abstracted
  Node signature = getGeneralizedSignature(assertion);

  Debug("bv-abstraction") << "   with sig " << signature << "\n";
  NodeNodeMap::iterator it = d_signatureToFunc.find(signature);
  if (it != d_signatureToFunc.end())
  {
    std::vector<Node> args;
    TNode func = it->second;
    // pushing the function symbol
    args.push_back(func);
    TNodeSet seen;
    collectArguments(assertion, signature, args, seen);
    std::vector<TNode> real_args;
    for (unsigned i = 1; i < args.size(); ++i)
    {
      real_args.push_back(args[i]);
    }
    d_argsTable.addEntry(func, real_args);
    Node result = nm->mkNode(
        kind::EQUAL,
        nm->mkNode(kind::APPLY_UF, args), utils::mkConst(1, 1u));
    Debug("bv-abstraction") << "=>   " << result << "\n";
    Assert(result.getType() == assertion.getType());
    return result;
  }
  return assertion;
}

bool AbstractionModule::isAbstraction(TNode node) {
  if (node.getKind() != kind::EQUAL)
    return false;
  if ((node[0].getKind() != kind::CONST_BITVECTOR ||
       node[1].getKind() != kind::APPLY_UF) &&
      (node[1].getKind() != kind::CONST_BITVECTOR ||
       node[0].getKind() != kind::APPLY_UF))
    return false;

  TNode constant = node[0].getKind() == kind::CONST_BITVECTOR ? node[0] : node[1];
  TNode func = node[0].getKind() == kind::APPLY_UF ? node[0] : node[1];
  Assert(constant.getKind() == kind::CONST_BITVECTOR
         && func.getKind() == kind::APPLY_UF);
  if (utils::getSize(constant) != 1)
    return false;
  if (constant != utils::mkConst(1, 1u))
    return false;

  TNode func_symbol = func.getOperator();
  if (d_funcToSignature.find(func_symbol) == d_funcToSignature.end())
    return false;

  return true;
}

Node AbstractionModule::getInterpretation(TNode node) {
  Assert(isAbstraction(node));
  TNode constant = node[0].getKind() == kind::CONST_BITVECTOR ? node[0] : node[1];
  TNode apply = node[0].getKind() == kind::APPLY_UF ? node[0] : node[1];
  Assert(constant.getKind() == kind::CONST_BITVECTOR
         && apply.getKind() == kind::APPLY_UF);

  Node func = apply.getOperator();
  Assert(d_funcToSignature.find(func) != d_funcToSignature.end());

  Node sig = d_funcToSignature[func];

  // substitute arguments in signature
  TNodeTNodeMap seen;
  unsigned index = 0;
  Node result = substituteArguments(sig, apply, index, seen);
  Assert(result.getType().isBoolean());
  Assert(index == apply.getNumChildren());
  // Debug("bv-abstraction") << "AbstractionModule::getInterpretation " << node << "\n";
  // Debug("bv-abstraction") << "    => " << result << "\n";
  return result;
}

Node AbstractionModule::substituteArguments(TNode signature, TNode apply, unsigned& index, TNodeTNodeMap& seen) {
  if (seen.find(signature) != seen.end()) {
    return seen[signature];
  }

  if (signature.getKind() == kind::SKOLEM) {
    // return corresponding argument and increment counter
    seen[signature] = apply[index];
    return apply[index++];
  }

  if (signature.getNumChildren() == 0) {
    Assert(signature.getMetaKind() != kind::metakind::VARIABLE);
    seen[signature] = signature;
    return signature;
  }

  NodeBuilder<> builder(signature.getKind());
  if (signature.getMetaKind() == kind::metakind::PARAMETERIZED) {
    builder << signature.getOperator();
  }

  for (unsigned i = 0; i < signature.getNumChildren(); ++i) {
    Node child = substituteArguments(signature[i], apply, index, seen);
    builder << child;
  }

  Node result = builder;
  seen[signature]= result;

  return result;
}

Node AbstractionModule::simplifyConflict(TNode conflict) {
  if (Dump.isOn("bv-abstraction")) {
    NodeNodeMap seen;
    Node c = reverseAbstraction(conflict, seen);
    Dump("bv-abstraction") << PushCommand();
    Dump("bv-abstraction") << AssertCommand(c.toExpr());
    Dump("bv-abstraction") << CheckSatCommand();
    Dump("bv-abstraction") << PopCommand();
  }

  Debug("bv-abstraction-dbg") << "AbstractionModule::simplifyConflict " << conflict << "\n";
  if (conflict.getKind() != kind::AND)
    return conflict;

  std::vector<Node> conjuncts;
  for (unsigned i = 0; i < conflict.getNumChildren(); ++i)
    conjuncts.push_back(conflict[i]);

  theory::SubstitutionMap subst(new context::Context());
  for (unsigned i = 0; i < conjuncts.size(); ++i) {
    TNode conjunct = conjuncts[i];
    // substitute s -> t
    Node s, t;

    if (conjunct.getKind() == kind::EQUAL) {
      if (conjunct[0].getMetaKind() == kind::metakind::VARIABLE &&
          conjunct[1].getKind() == kind::CONST_BITVECTOR) {
        s = conjunct[0];
        t = conjunct[1];
      }
      else if (conjunct[1].getMetaKind() == kind::metakind::VARIABLE &&
               conjunct[0].getKind() == kind::CONST_BITVECTOR) {
        s = conjunct[1];
        t = conjunct[0];
      } else {
        continue;
      }

      Assert(!subst.hasSubstitution(s));
      Assert(!t.isNull() && !s.isNull() && s != t);
      subst.addSubstitution(s, t);

      for (unsigned k = 0; k < conjuncts.size(); k++) {
        conjuncts[k] = subst.apply(conjuncts[k]);
      }
    }
  }
  Node new_conflict = Rewriter::rewrite(utils::mkAnd(conjuncts));

  Debug("bv-abstraction") << "AbstractionModule::simplifyConflict conflict " << conflict <<"\n";
  Debug("bv-abstraction") << "   => " << new_conflict <<"\n";

  if (Dump.isOn("bv-abstraction")) {

    NodeNodeMap seen;
    Node nc = reverseAbstraction(new_conflict, seen);
    Dump("bv-abstraction") << PushCommand();
    Dump("bv-abstraction") << AssertCommand(nc.toExpr());
    Dump("bv-abstraction") << CheckSatCommand();
    Dump("bv-abstraction") << PopCommand();
  }

  return new_conflict;
}

void DebugPrintInstantiations(
    const std::vector<std::vector<ArgsVec> >& instantiations,
    const std::vector<TNode>& functions)
{
  // print header
  Debug("bv-abstraction-dbg") <<"[ ";
  for (unsigned i = 0; i < functions.size(); ++i) {
    for (unsigned j = 1; j < functions[i].getNumChildren(); ++j) {
      Debug("bv-abstraction-dgb") << functions[i][j] <<" ";
    }
    Debug("bv-abstraction-dgb") << " || ";
  }
  Debug("bv-abstraction-dbg") <<"]\n";

  for (unsigned i = 0; i < instantiations.size(); ++i) {
    Debug("bv-abstraction-dbg") <<"[";
    const std::vector<ArgsVec>& inst = instantiations[i];
    for (unsigned j = 0; j < inst.size(); ++j) {
      for (unsigned k = 0; k < inst[j].size(); ++k) {
        Debug("bv-abstraction-dbg") << inst[j][k] << " ";
      }
      Debug("bv-abstraction-dbg") << " || ";
    }
    Debug("bv-abstraction-dbg") <<"]\n";
  }
}

void AbstractionModule::generalizeConflict(TNode conflict, std::vector<Node>& lemmas) {
  Debug("bv-abstraction") << "AbstractionModule::generalizeConflict " << conflict << "\n";
  std::vector<TNode> functions;

  // collect abstract functions
  if (conflict.getKind() != kind::AND) {
    if (isAbstraction(conflict)) {
      Assert(conflict[0].getKind() == kind::APPLY_UF);
      functions.push_back(conflict[0]);
    }
  } else {
    for (unsigned i = 0; i < conflict.getNumChildren(); ++i) {
      TNode conjunct = conflict[i];
      if (isAbstraction(conjunct)) {
        Assert(conjunct[0].getKind() == kind::APPLY_UF);
        functions.push_back(conjunct[0]);
      }
    }
  }

  // if (functions.size() >= 3) {
  //   // dump conflict
  //   NodeNodeMap seen;
  //   Node reversed = reverseAbstraction(conflict, seen);
  //   std::cout << "CONFLICT " << reversed << "\n";
  // }


  if (functions.size() == 0 || functions.size() > options::bvNumFunc()) {
    return;
  }


  // Skolemize function arguments to avoid confusion in pattern matching
  SubstitutionMap skolem_subst(new context::Context());
  SubstitutionMap reverse_skolem(new context::Context());
  makeFreshSkolems(conflict, skolem_subst, reverse_skolem);

  Node skolemized_conflict = skolem_subst.apply(conflict);
  for (unsigned i = 0; i < functions.size(); ++i) {
    functions[i] = skolem_subst.apply(functions[i]);
  }

  conflict = skolem_subst.apply(conflict);

  LemmaInstantiatior inst(functions, d_argsTable, conflict);
  std::vector<Node> new_lemmas;
  inst.generateInstantiations(new_lemmas);
  for (unsigned i = 0; i < new_lemmas.size(); ++i) {
    TNode lemma = reverse_skolem.apply(new_lemmas[i]);
    if (d_addedLemmas.find(lemma) == d_addedLemmas.end()) {
      lemmas.push_back(lemma);
      Debug("bv-abstraction-gen") << "adding lemma " << lemma << "\n";
      storeLemma(lemma);

      if (Dump.isOn("bv-abstraction")) {
        NodeNodeMap seen;
        Node l = reverseAbstraction(lemma, seen);
        Dump("bv-abstraction") << PushCommand();
        Dump("bv-abstraction") << AssertCommand(l.toExpr());
        Dump("bv-abstraction") << CheckSatCommand();
        Dump("bv-abstraction") << PopCommand();
      }
    }
  }
}

int AbstractionModule::LemmaInstantiatior::next(int val, int index) {
  if (val < d_maxMatch[index]  - 1)
    return val + 1;
  return -1;
}

/**
 * Assumes the stack without top is consistent, and checks that the
 * full stack is consistent
 *
 * @param stack
 *
 * @return
 */
bool AbstractionModule::LemmaInstantiatior::isConsistent(const vector<int>& stack) {
  if (stack.empty())
    return true;

  unsigned current = stack.size() - 1;
  TNode func = d_functions[current];
  ArgsTableEntry& matches = d_argsTable.getEntry(func.getOperator());
  ArgsVec& args = matches.getEntry(stack[current]);
  Assert(args.size() == func.getNumChildren());
  for (unsigned k = 0; k < args.size(); ++k) {
    TNode s = func[k];
    TNode t = args[k];

    TNode s0 = s;
    while (d_subst.hasSubstitution(s0)) {
      s0 = d_subst.getSubstitution(s0);
    }

    TNode t0 = t;
    while (d_subst.hasSubstitution(t0)) {
      t0 = d_subst.getSubstitution(t0);
    }

    if (s0.isConst() && t0.isConst()) {
      if (s0 != t0)
        return false; // fail
      else
        continue;
    }

    if(s0.getMetaKind() == kind::metakind::VARIABLE &&
       t0.isConst()) {
      d_subst.addSubstitution(s0, t0);
      continue;
    }

    if (s0.isConst() &&
        t0.getMetaKind() == kind::metakind::VARIABLE) {
      d_subst.addSubstitution(t0, s0);
      continue;
    }

    Assert(s0.getMetaKind() == kind::metakind::VARIABLE
           && t0.getMetaKind() == kind::metakind::VARIABLE);

    if (s0 != t0) {
      d_subst.addSubstitution(s0, t0);
    }
  }
  return true;
}

bool AbstractionModule::LemmaInstantiatior::accept(const vector<int>& stack) {
  return stack.size() == d_functions.size();
}

void AbstractionModule::LemmaInstantiatior::mkLemma() {
  Node lemma = d_subst.apply(d_conflict);
  // Debug("bv-abstraction-gen") << "AbstractionModule::LemmaInstantiatior::mkLemma " << lemma <<"\n";
  d_lemmas.push_back(lemma);
}

void AbstractionModule::LemmaInstantiatior::backtrack(vector<int>& stack) {
  if (!isConsistent(stack))
    return;

  if (accept(stack)) {
    mkLemma();
    return;
  }

  int x = 0;
  while (x != -1) {
    d_ctx->push();
    stack.push_back(x);
    backtrack(stack);

    d_ctx->pop();
    stack.pop_back();
    x = next(x, stack.size());
  }
}


void AbstractionModule::LemmaInstantiatior::generateInstantiations(std::vector<Node>& lemmas) {
  Debug("bv-abstraction-gen") << "AbstractionModule::LemmaInstantiatior::generateInstantiations ";

  std::vector<int> stack;
  backtrack(stack);
  Assert(d_ctx->getLevel() == 0);
  Debug("bv-abstraction-gen") << "numLemmas=" << d_lemmas.size() <<"\n";
  lemmas.swap(d_lemmas);
}

void AbstractionModule::makeFreshSkolems(TNode node, SubstitutionMap& map, SubstitutionMap& reverse_map) {
  if (map.hasSubstitution(node)) {
    return;
  }
  if (node.getMetaKind() == kind::metakind::VARIABLE) {
    Node skolem = utils::mkVar(utils::getSize(node));
    map.addSubstitution(node, skolem);
    reverse_map.addSubstitution(skolem, node);
    return;
  }
  if (node.isConst())
    return;

  for (unsigned i = 0; i < node.getNumChildren(); ++i) {
    makeFreshSkolems(node[i], map, reverse_map);
  }
}

void AbstractionModule::makeFreshArgs(TNode func, std::vector<Node>& fresh_args) {
  Assert(fresh_args.size() == 0);
  Assert(func.getKind() == kind::APPLY_UF);
  TNodeNodeMap d_map;
  for (unsigned i = 0; i < func.getNumChildren(); ++i) {
    TNode arg = func[i];
    if (arg.isConst()) {
      fresh_args.push_back(arg);
      continue;
    }
    Assert(arg.getMetaKind() == kind::metakind::VARIABLE);
    TNodeNodeMap::iterator it = d_map.find(arg);
    if (it != d_map.end()) {
      fresh_args.push_back(it->second);
    } else {
      Node skolem = utils::mkVar(utils::getSize(arg));
      d_map[arg] = skolem;
      fresh_args.push_back(skolem);
    }
  }
  Assert(fresh_args.size() == func.getNumChildren());
}

Node AbstractionModule::tryMatching(const std::vector<Node>& ss, const std::vector<TNode>& tt, TNode conflict) {
  Assert(ss.size() == tt.size());

  Debug("bv-abstraction-dbg") << "AbstractionModule::tryMatching conflict = " << conflict << "\n";
  if (Debug.isOn("bv-abstraction-dbg")) {
    Debug("bv-abstraction-dbg") << "  Match: ";
    for (unsigned i = 0; i < ss.size(); ++i) {
      Debug("bv-abstraction-dbg") << ss[i] <<" ";

    }
    Debug("bv-abstraction-dbg") << "\n  To: ";
    for (unsigned i = 0; i < tt.size(); ++i) {
      Debug("bv-abstraction-dbg") << tt[i] <<" ";
    }
    Debug("bv-abstraction-dbg") <<"\n";
  }


  SubstitutionMap subst(new context::Context());

  for (unsigned i = 0; i < ss.size(); ++i) {
    TNode s = ss[i];
    TNode t = tt[i];

    TNode s0 = subst.hasSubstitution(s) ? subst.getSubstitution(s) : s;
    TNode t0 = subst.hasSubstitution(t) ? subst.getSubstitution(t) : t;

    if (s0.isConst() && t0.isConst()) {
      if (s0 != t0)
        return Node(); // fail
      else
        continue;
    }

    if(s0.getMetaKind() == kind::metakind::VARIABLE &&
       t0.isConst()) {
      subst.addSubstitution(s0, t0);
      continue;
    }

    if (s0.isConst() &&
        t0.getMetaKind() == kind::metakind::VARIABLE) {
      subst.addSubstitution(t0, s0);
      continue;
    }

    Assert(s0.getMetaKind() == kind::metakind::VARIABLE
           && t0.getMetaKind() == kind::metakind::VARIABLE);

    Assert(s0 != t0);
    subst.addSubstitution(s0, t0);
  }

  Node res = subst.apply(conflict);
  Debug("bv-abstraction-dbg") << "  Lemma: " << res <<"\n";
  return res;
}

void AbstractionModule::storeLemma(TNode lemma) {
  d_addedLemmas.insert(lemma);
  if (lemma.getKind() == kind::AND) {
    for (unsigned i = 0; i < lemma.getNumChildren(); i++) {
      TNode atom = lemma[i];
      atom = atom.getKind() == kind::NOT ? atom[0] : atom;
      Assert(atom.getKind() != kind::NOT);
      Assert(utils::isBVPredicate(atom));
      d_lemmaAtoms.insert(atom);
    }
  } else {
    lemma = lemma.getKind() == kind::NOT? lemma[0] : lemma;
    Assert(utils::isBVPredicate(lemma));
    d_lemmaAtoms.insert(lemma);
  }
}


bool AbstractionModule::isLemmaAtom(TNode node) const {
  Assert(node.getType().isBoolean());
  node = node.getKind() == kind::NOT? node[0] : node;

  return d_inputAtoms.find(node) == d_inputAtoms.end() &&
    d_lemmaAtoms.find(node) != d_lemmaAtoms.end();
}

void AbstractionModule::addInputAtom(TNode atom) {
  if (options::bitblastMode() == options::BitblastMode::LAZY)
  {
    d_inputAtoms.insert(atom);
  }
}

void AbstractionModule::ArgsTableEntry::addArguments(const ArgsVec& args) {
  Assert(args.size() == d_arity);
  d_data.push_back(args);
}

void AbstractionModule::ArgsTable::addEntry(TNode signature, const ArgsVec& args) {
  if (d_data.find(signature) == d_data.end()) {
    d_data[signature] = ArgsTableEntry(args.size());
  }
  ArgsTableEntry& entry = d_data[signature];
  entry.addArguments(args);
}


bool AbstractionModule::ArgsTable::hasEntry(TNode signature) const {
  return d_data.find(signature) != d_data.end();
}

AbstractionModule::ArgsTableEntry& AbstractionModule::ArgsTable::getEntry(TNode signature) {
  Assert(hasEntry(signature));
  return d_data.find(signature)->second;
}

AbstractionModule::Statistics::Statistics(const std::string& name)
    : d_numFunctionsAbstracted(name + "::abstraction::NumFunctionsAbstracted",
                               0),
      d_numArgsSkolemized(name + "::abstraction::NumArgsSkolemized", 0),
      d_abstractionTime(name + "::abstraction::AbstractionTime")
{
  smtStatisticsRegistry()->registerStat(&d_numFunctionsAbstracted);
  smtStatisticsRegistry()->registerStat(&d_numArgsSkolemized);
  smtStatisticsRegistry()->registerStat(&d_abstractionTime);
}

AbstractionModule::Statistics::~Statistics() {
  smtStatisticsRegistry()->unregisterStat(&d_numFunctionsAbstracted);
  smtStatisticsRegistry()->unregisterStat(&d_numArgsSkolemized);
  smtStatisticsRegistry()->unregisterStat(&d_abstractionTime);
}
