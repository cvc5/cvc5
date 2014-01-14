/*********************                                                        */
/*! \file abstraction.cpp
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: none.
 ** Minor contributors (to current version): none.
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/bv/abstraction.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/rewriter.h"
#include "theory/substitutions.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;
using namespace CVC4::context;

using namespace std;
using namespace CVC4::theory::bv::utils;

void AbstractionModule::applyAbstraction(const std::vector<Node>& assertions, std::vector<Node>& new_assertions) {
  Debug("bv-abstraction") << "AbstractionModule::applyAbstraction\n"; 
  // for (unsigned i = 0; i < assertions.size(); ++i) {
  //   inferDomains(assertions[i]); 
  // }
  // // adds the enumeration domains to the module
  // d_domainMaker.finalize();
  for (unsigned i = 0; i < assertions.size(); ++i) {
    if (assertions[i].getKind() == kind::OR) {
      for (unsigned j = 0; j < assertions[i].getNumChildren(); ++j) {
        Node signature = computeSignature(assertions[i][j]);
        storeSignature(signature, assertions[i][j]); 
        // Debug("bv-abstraction") << "   assertion: " << assertions[i][j] <<"\n";
        // Debug("bv-abstraction") << "   signature: " << signature <<"\n";
      }
    }
  }
  finalizeSignatures();

  for (unsigned i = 0; i < assertions.size(); ++i) {
    if (assertions[i].getKind() == kind::OR &&
        assertions[i][0].getKind() == kind::AND) {
      std::vector<Node> new_children; 
      for (unsigned j = 0; j < assertions[i].getNumChildren(); ++j) {
        new_children.push_back(abstractSignatures(assertions[i][j]));
      }
      new_assertions.push_back(utils::mkNode(kind::OR, new_children)); 
    } else {
      // assertions that are not changed
      new_assertions.push_back(assertions[i]); 
    }
  }
}

void AbstractionModule::storeSignature(Node signature, TNode assertion) {
  if(d_signatures.find(signature) == d_signatures.end()) {
    d_signatures[signature] = 0; 
  }
  d_signatures[signature] = d_signatures[signature] + 1; 
  d_assertionToSignature[assertion] = signature; 
}

void AbstractionModule::inferDomains(TNode assertion) {
  // check for inequalities
  if (assertion.getKind() == kind::AND &&
      assertion[0].getKind() == kind::BITVECTOR_ULT) {
    for (unsigned i = 0; i < assertion.getNumChildren(); ++i) {
      if (assertion[i].getKind() == kind::BITVECTOR_ULT &&
          assertion[i][0].getKind() == kind::VARIABLE &&
          assertion[i][1].getKind() == kind::CONST_BITVECTOR) {
        TNode var = assertion[i][0];
        TNode constant = assertion[i][1];
        storeUpperBound(var, constant); 
      }
    }
  }
  if (assertion.getKind() == kind::OR &&
      assertion[0].getKind() == kind::EQUAL &&
      ((assertion[0][0].getKind() == kind::CONST_BITVECTOR &&
        assertion[0][1].getKind() == kind::VARIABLE) ||
       (assertion[0][1].getKind() == kind::CONST_BITVECTOR &&
        assertion[0][0].getKind() == kind::VARIABLE))) {
    TNode constant = assertion[0][0].getKind() == kind::CONST_BITVECTOR ? assertion[0][0] : assertion[0][1];
    TNodeSet variables; 
    for (unsigned i = 0; i < assertion.getNumChildren(); ++i) {
      TNode eq = assertion[i];
      TNode constant_i = eq[0].getKind() == kind::CONST_BITVECTOR ? eq[0] : eq[1];
      TNode var_i = eq[0].getKind() == kind::CONST_BITVECTOR ? eq[1] : eq[0];
      // same constant on all branches
      if (constant_i != constant)
        return;
      // each variable occurs once
      if (variables.count(var_i))
        return; 
      variables.insert(var_i); 
    }
    d_domainMaker.add(constant, variables); 
  }
}

void AbstractionModule::storeUpperBound(TNode var, TNode constant) {
  Assert (var.getKind() == kind::VARIABLE &&
          constant.getKind() == kind::CONST_BITVECTOR);

  // Debug("bv-abstraction") << "AbstractionModule::storeUpperBound "<< var << " < " << constant <<"\n";
  
  if (d_upperBoundToDomain.find(constant) == d_upperBoundToDomain.end()) {
    Node new_skolem = utils::mkVar(utils::getSize(var));
    d_upperBoundToDomain[constant] = new_skolem; 
  }
  TNode skolem = d_upperBoundToDomain[constant];
  storeDomain(var, skolem); 
  // Debug("bv-abstraction") << "   with skolem " << skolem <<"\n";
}

void AbstractionModule::DomainMaker::add(TNode constant, TNodeSet& variables) {
  Assert (variables.size());
  // Debug("bv-abstraction") << "AbstractionModule::DomainMaker::add constant = " << constant <<"\n"; 
  if (!d_canMakeDomain)
    return;
  
  // if it is the first add
  if (d_variables.size() == 0) {
    d_variables.swap(variables);
    d_constants.insert(constant);
    return; 
  }
  
  // check that variable sets contain the exact same elements
  if (variables.size() != d_variables.size()) {
    d_canMakeDomain = false;
    return; 
  }
  for (TNodeSet::const_iterator it = variables.begin(); it != variables.end(); ++it) {
    if (d_variables.find(*it) == d_variables.end()) {
      d_canMakeDomain = false;
      return;
    }
  }
  // finally add the constant
  d_constants.insert(constant); 
}

void AbstractionModule::DomainMaker::finalize() {
  if (!d_canMakeDomain) return;
  d_canMakeDomain = false;
  // check that we have the exact same number of variables and constants
  if (d_variables.size() != d_constants.size())
    return;


  TNode domain_skolem = d_module.makeEnumDomain(d_constants);
  // Debug("bv-abstraction") << "AbstractionModule::DomainMaker::finalize skolem " << domain_skolem << " for set: \n";
  // if (Debug.isOn("bv-abstraction")) {
  //   for (TNodeSet::iterator it = d_constants.begin(); it != d_constants.end(); ++it) {
  //     Debug("bv-abstraction") << "   [" << *it << " "; 
  //   }
  //   Debug("bv-abstraction") << "\n"; 
  // }
  
  for (TNodeSet::iterator it = d_variables.begin(); it != d_variables.end(); ++it) {
    d_module.storeDomain(*it, domain_skolem); 
  }
  d_variables.clear();
  d_constants.clear(); 
}

TNode AbstractionModule::getDomainSkolem(TNode node) {
  TNodeTNodeMap::const_iterator it = d_varToDomain.find(node);
  if (it == d_varToDomain.end())
    return node;
  return it->second; 
}

Node AbstractionModule::computeSignature(TNode node) {
  resetSignatureIndex(); 
  NodeNodeMap cache; 
  Node sig = computeSignatureRec(node, cache);
  return sig;
}

Node AbstractionModule::getSignatureSkolem(TNode node) {
  Assert (node.getKind() == kind::VARIABLE);
  unsigned bitwidth = utils::getSize(node);
  if (d_signatureSkolems.find(bitwidth) == d_signatureSkolems.end()) {
    d_signatureSkolems[bitwidth] = vector<Node>(); 
  }
  
  vector<Node>& skolems = d_signatureSkolems[bitwidth];
  // get the index of bv variables of this size
  unsigned index = getBitwidthIndex(bitwidth); 
  Assert (skolems.size() + 1 >= index );
  if (skolems.size() == index) {
    ostringstream os;
    os << "sig_" <<bitwidth <<"_" << index;
    NodeManager* nm = NodeManager::currentNM(); 
    skolems.push_back(nm->mkSkolem(os.str(), nm->mkBitVectorType(bitwidth), "skolem for computing signatures"));
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

Node AbstractionModule::getGeneralizedSignature(Node node) {
  NodeNodeMap::const_iterator it = d_assertionToSignature.find(node); 
  Assert (it != d_assertionToSignature.end());
  Node generalized_signature = getGeneralization(it->second); 
  return generalized_signature; 
}

Node AbstractionModule::computeSignatureRec(TNode node, NodeNodeMap& cache) {
  Assert(node.getKind() != kind::OR &&
         node.getKind() != kind::XOR &&
         node.getKind() != kind::ITE &&
         node.getKind() != kind::NOT &&
         node.getKind() != kind::IMPLIES);

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
int AbstractionModule::PatternMatcher::comparePatterns(TNode s, TNode t) {
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
    int unify_i = PatternMatcher::comparePatterns(s[i], t[i]);
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
  Assert (generalization != term);
  d_sigToGeneralization[term] = generalization;
  return generalization; 
}

void AbstractionModule::storeGeneralization(TNode s, TNode t) {
  // std::cout << "StoreGeneralization " << s.getId() << " => " << t.getId() <<"\n"; 
  Assert (s == getGeneralization(s));
  Assert (t == getGeneralization(t));
  d_sigToGeneralization[s] = t; 
}

void AbstractionModule::finalizeSignatures() {
  NodeManager* nm = NodeManager::currentNM();
  Debug("bv-abstraction") << "AbstractionModule::finalizeSignatures num signatures = " << d_signatures.size() <<"\n";
  TNodeSet new_signatures;
  // remove signatures that are not frequent enough
  for (SignatureMap::iterator it = d_signatures.begin(); it != d_signatures.end(); ) {
    if (it->second <= 7) {
      d_signatures.erase(it++); 
    } else {
      ++it;
    }
  }

  // unify signatures
  for (SignatureMap::const_iterator ss = d_signatures.begin(); ss != d_signatures.end(); ++ss) {
    for (SignatureMap::const_iterator tt = ss; tt != d_signatures.end(); ++tt) {
      TNode t = getGeneralization(tt->first);
      TNode s = getGeneralization(ss->first);
      
      if (t != s) {
        int status = PatternMatcher::comparePatterns(s, t);
        Assert (status); 
        if (status < 0)
          continue;
        if (status == 1) {
          // std::cout << s << " is a generalization of \n" << t << "\n";
          storeGeneralization(t, s); 
        } else {
          // std::cout << t << " is a generalization of \n" << s << "\n\n"; 
          storeGeneralization(s, t); 
        }
      }
    }
  }
  // keep only most general signatures
  for (SignatureMap::iterator it = d_signatures.begin(); it != d_signatures.end(); ) {
    TNode sig = it->first; 
    TNode gen = getGeneralization(sig);
    // std::cout << "sig " << sig <<"\n";
    // std::cout << "gen " << gen <<"\n\n";
    if (sig != gen) {
      Assert (d_signatures.find(gen) != d_signatures.end()); 
      // update the count
      d_signatures[gen]+= d_signatures[sig];
      d_signatures.erase(it++); 
    } else {
      ++it;
    }
  }
  
  for (SignatureMap::const_iterator it = d_signatures.begin(); it != d_signatures.end(); ++it) {
    TNode signature = it->first;
    // we already processed this signature
    Assert (d_signatureToFunc.find(signature) == d_signatureToFunc.end());

    Debug("bv-abstraction") << "Processing signature " << signature << " count " << it->second << "\n";
    std::vector<TypeNode> arg_types;
    TNodeSet seen;
    collectArgumentTypes(signature, arg_types, seen);
    Assert (signature.getType().isBoolean());
    // make function return a bitvector of size 1
    //Node bv_function = utils::mkNode(kind::ITE, signature, utils::mkConst(1, 1u), utils::mkConst(1, 0u)); 
    TypeNode range = NodeManager::currentNM()->mkBitVectorType(1);
    
    TypeNode abs_type = nm->mkFunctionType(arg_types, range);
    Node abs_func = nm->mkSkolem("abs_$$", abs_type, "abstraction function for bv theory");
    Debug("bv-abstraction") << " abstracted by function " << abs_func << "\n";

    // NOTE: signature expression type is BOOLEAN
    d_signatureToFunc[signature] = abs_func;
    d_funcToSignature[abs_func] = signature; 
  }

  Debug("bv-abstraction") << "AbstractionModule::finalizeSignatures abstracted " << d_signatureToFunc.size() << " signatures. \n";
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
  
  if (node.getKind() == kind::VARIABLE ||
      node.getKind() == kind::CONST_BITVECTOR) {
    // a constant in the node can either map to an argument of the abstraction
    // or can be hard-coded and part of the abstraction 
    if (signature.getKind() == kind::SKOLEM) {
      args.push_back(node);
    } else {
      Assert (signature.getKind() == kind::CONST_BITVECTOR); 
    }
    seen.insert(node);
    return; 
  }
  Assert (node.getKind() == signature.getKind() &&
          node.getNumChildren() == signature.getNumChildren()); 

  for (unsigned i = 0; i < node.getNumChildren(); ++i) {
    collectArguments(node[i], signature[i], args, seen); 
    seen.insert(node); 
  }
}


Node AbstractionModule::abstractSignatures(TNode assertion) {
  // Debug("bv-abstraction") << "AbstractionModule::abstractSignatures "<< assertion <<"\n"; 
  // assume the assertion has been fully abstracted
  Node signature = getGeneralizedSignature(assertion);
  
  // Debug("bv-abstraction") << "   with sig "<< signature <<"\n"; 
  NodeNodeMap::iterator it = d_signatureToFunc.find(signature);
  if (it!= d_signatureToFunc.end()) {
    std::vector<Node> args;
    TNode func = it->second;
    // pushing the function symbol
    args.push_back(func);
    TNodeSet seen;
    collectArguments(assertion, signature, args, seen);
    std::vector<TNode> real_args;
    for (unsigned i = 1; i < args.size(); ++i) {
      real_args.push_back(args[i]); 
    }
    d_argsTable.addEntry(func, real_args); 
    Node result = utils::mkNode(kind::EQUAL, utils::mkNode(kind::APPLY_UF, args), 
                                utils::mkConst(1, 1u));
    // Debug("bv-abstraction") << "=>   "<< result << "\n"; 
    Assert (result.getType() == assertion.getType()); 
    return result; 
  }
  return assertion; 
}

Node AbstractionModule::makeEnumDomain(TNodeSet& values) {
  TNodeSet::iterator it = values.begin();
  Assert (it != values.end()); 
  unsigned size = utils::getSize(*it);
  Node skolem = utils::mkVar(size);
  d_domainsEnum[skolem] = std::vector<Node>();
  for (; it != values.end(); ++it) {
    d_domainsEnum[skolem].push_back(*it); 
  }
  
  return skolem; 
}

void AbstractionModule::storeDomain(Node var, Node domain_skolem) {
  Assert (var.getKind() == kind::VARIABLE &&
          domain_skolem.getKind() == kind::SKOLEM);
  Assert (d_varToDomain.find(var) == d_varToDomain.end());
  Debug("bv-abstraction") << "AbstractionModule::storeDomain var = "<< var
                          << ", skolem = " << domain_skolem << "\n"; 
  d_varToDomain[var] = domain_skolem;
  d_skolems.insert(domain_skolem); 
}

bool AbstractionModule::isDomainSkolem(TNode node) {
  return d_skolems.find(node) != d_skolems.end(); 
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
  Assert (constant.getKind() == kind::CONST_BITVECTOR &&
          func.getKind() == kind::APPLY_UF);
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
  Assert (isAbstraction(node));
  TNode constant = node[0].getKind() == kind::CONST_BITVECTOR ? node[0] : node[1];
  TNode apply = node[0].getKind() == kind::APPLY_UF ? node[0] : node[1];
  Assert (constant.getKind() == kind::CONST_BITVECTOR &&
          apply.getKind() == kind::APPLY_UF);

  Node func = apply.getOperator(); 
  Assert (d_funcToSignature.find(func) != d_funcToSignature.end());
  
  Node sig = d_funcToSignature[func];
  // substitute arguments in signature
  TNodeTNodeMap seen;
  unsigned index = 0;
  Node result = substituteArguments(sig, apply, index, seen);
  Assert (result.getType().isBoolean()); 
  Assert (index == apply.getNumChildren());
  // Debug("bv-abstraction") << "AbstractionModule::getInterpretation " << node << "\n";
  // Debug("bv-abstraction") << "    => " << result << "\n";
  return result; 
}

Node AbstractionModule::substituteArguments(TNode signature, TNode apply, unsigned& index, TNodeTNodeMap& seen) {
  // std::cout << "substArgs index " << index << " apply " << apply << "\n";
  // std::cout << "substArgs signature " << signature << "\n\n";
  if (seen.find(signature) != seen.end()) {
    return seen[signature]; 
  }
  
  if (signature.getKind() == kind::SKOLEM) {
    // return corresponding argument and increment counter
    seen[signature] = apply[index];
    return apply[index++]; 
  }

  if (signature.getNumChildren() == 0) {
    Assert (signature.getKind() != kind::VARIABLE); 
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
  // std::cout << "sig " << signature << " => " << result <<"\n\n"; 
  return result;
}

Node AbstractionModule::simplifyConflict(TNode conflict) {
  if (conflict.getKind() != kind::AND)
    return conflict; 
  
  theory::SubstitutionMap subst(new context::Context());
  for (unsigned i = 0; i < conflict.getNumChildren(); ++i) {
    TNode conjunct = conflict[i];
    if (conjunct.getKind() == kind::EQUAL) {
      if (conjunct[0].getKind() == kind::VARIABLE &&
          conjunct[1].getKind() == kind::CONST_BITVECTOR) {
        subst.addSubstitution(conjunct[0], conjunct[1]); 
      }
      if (conjunct[1].getKind() == kind::VARIABLE &&
          conjunct[0].getKind() == kind::CONST_BITVECTOR) {
        subst.addSubstitution(conjunct[1], conjunct[0]); 
      }
    }
  }
  Node new_conflict = Rewriter::rewrite(subst.apply(conflict));
  Debug("bv-abstraction") << "AbstractionModule::simplifyConflict conflict " << conflict <<"\n";
  Debug("bv-abstraction") << "   => " << new_conflict <<"\n";
  return new_conflict; 
}


void DebugPrintInstantiations(const std::vector< std::vector<ArgsVec> >& instantiations,
                             const std::vector<TNode> functions) {
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

static int num_one = 0;
static int num_many = 0;

void AbstractionModule::generalizeConflict(TNode conflict, std::vector<Node>& lemmas) {
  Debug("bv-abstraction") << "AbstractionModule::generalizeConflict " << conflict << "\n"; 
  std::vector<TNode> functions;
  // collect abstract functions
  for (unsigned i = 0; i < conflict.getNumChildren(); ++i) {
    TNode conjunct = conflict[i];
    if (conjunct.getKind() != kind::EQUAL)
      continue;

    if (conjunct[0].getKind() != kind::APPLY_UF &&
        conjunct[1].getKind() != kind::APPLY_UF)
      continue;
    TNode func = conjunct[0].getKind() == kind::APPLY_UF ? conjunct[0] : conjunct[1];

    if (d_funcToSignature.find(func.getOperator()) == d_funcToSignature.end())
      continue;
    functions.push_back(func); 
  }
    
  if (functions.size() > 1) {
    num_many++;
    //    std::cout << "one fun=" << num_one << " many fun " << num_many << " this many= " << functions.size() << " \n";
    // if (functions.size() == 2) {
    //   std::cout << "Conflict " << conflict << "\n"; 
    // }
    return;
  }

  num_one++;
  
  std::vector<ArgsTableEntry> matches; 
  for (unsigned i = 0; i < functions.size(); ++i) {
    matches.push_back(ArgsTableEntry(functions[i].getNumChildren())); 
    getMatches(functions[i], matches[i]);
    Debug("bv-abstraction-dbg") << "  function=" << functions[i] << " matches=" << matches[i].getNumEntries() << "\n";
    for (ArgsTableEntry::iterator it = matches[i].begin(); it != matches[i].end(); ++it) {
      const ArgsVec& args = *it;
      Debug("bv-abstraction-dbg") << " ["; 
      for (unsigned i = 0; i < args.size(); ++i) {
        Debug("bv-abstraction-dbg") << args[i] <<" "; 
      }
      Debug("bv-abstraction-dbg") << "]\n"; 
    }
  }

  Assert (matches.size() == functions.size()); 
  
  // compute all instantiations
  std::vector< std::vector<ArgsVec> > instantiations;
  std::vector< std::vector<ArgsVec> > current_inst;
  instantiations.push_back(std::vector<ArgsVec>());
  
  for (unsigned i = 0; i < functions.size(); ++i) {
    generateInstantiations(i, matches, instantiations, current_inst);
    instantiations.swap(current_inst);
    current_inst.clear(); 
  }

  DebugPrintInstantiations(instantiations, functions); 

  // remove inconsistent instantiations
  for (unsigned i = 0; i < instantiations.size(); ++i) {
    if (isConsistent(instantiations[i], functions)) {
      Node lemma = mkInstantiationLemma(instantiations[i], functions, conflict);
      lemmas.push_back(lemma); 
      Debug("bv-abstraction") << "   lemma: " << lemma <<"\n"; 
    }
  }
}

Node AbstractionModule::mkInstantiationLemma(const std::vector<ArgsVec>& instantiation,
                                              const std::vector<TNode>& functions,
                                              TNode conflict) {
  SubstitutionMap subst(new context::Context());
  Assert (functions.size() == instantiation.size());
  for (unsigned i = 0; i < instantiation.size(); ++i) {
    // for each function
    TNode function = functions[i];
    const ArgsVec& args = instantiation[i];
    Assert (function.getKind() == kind::APPLY_UF);

    Assert (function.getNumChildren() == args.size());
    for (unsigned j = 0; j < args.size(); ++j) {
      TNode arg = function[j];
      if (arg.getKind() == kind::CONST_BITVECTOR &&
          args[j].getKind() == kind::CONST_BITVECTOR) {
        Assert (arg == args[j]);
      } else if (arg.getKind() == kind::VARIABLE &&
                 arg != args[j]) {
        subst.addSubstitution(arg, args[j]);
      }
    }
  }
  Node lemma = Rewriter::rewrite(subst.apply(conflict)); 
  return lemma;
}

// FIXME!!! THIS IS DUMB AND WRONG
bool AbstractionModule::isConsistent(const std::vector<ArgsVec>& instantiation,
                                     const std::vector<TNode>& funcs) {
  Assert (instantiation.size() == funcs.size());
  TNodeTNodeMap subst;
  for (unsigned i = 0; i < instantiation.size(); ++i) {
    TNode function = funcs[i];
    const ArgsVec& args = instantiation[i];
    Assert (function.getNumChildren() == args.size());
    
    for (unsigned j = 0; j < args.size(); ++j) {
      TNode arg = function[j];
      if (arg.getKind() == kind::CONST_BITVECTOR &&
          args[j].getKind() == kind::CONST_BITVECTOR) {
        Assert (arg == args[j]);
        continue;
      }

      if (arg.getKind() == kind::CONST_BITVECTOR ||
          args[j].getKind() == kind::CONST_BITVECTOR) {
        TNode c = arg.getKind() == kind::CONST_BITVECTOR? arg : args[j];
        TNode v = arg.getKind() == kind::CONST_BITVECTOR? args[j] : arg;

        Assert (v.getKind() == kind::VARIABLE);
        
        TNodeTNodeMap::iterator it = subst.find(v);
        if (it == subst.end()) {
          subst[v]  = c;
        } else {
          if (it->second != c)
            return false; 
        }
        continue;
      }

      Assert (arg.getKind() == kind::VARIABLE &&
              args[j].getKind() == kind::VARIABLE);
      
      TNodeTNodeMap::iterator it = subst.find(arg);
      if (it == subst.end()) {
        subst[arg] = args[j];
      } else {
        if (it->second != args[j])
          return false; 
      }
      
    }
  }
  return true; 
}

void AbstractionModule::generateInstantiations(unsigned current,
                                               std::vector<ArgsTableEntry>& matches, 
                                               std::vector<std::vector<ArgsVec> >& instantiations,
                                               std::vector<std::vector<ArgsVec> >& new_instantiations) {
  // assume we already have all the instantiations for all current - 1 functions
  ArgsTableEntry& current_matches = matches[current];
  for (ArgsTableEntry::iterator it = current_matches.begin(); it != current_matches.end(); ++it) {
    ArgsVec& match = *it;
    for (unsigned i = 0; i < instantiations.size(); ++i) {
      vector<ArgsVec>& instantiation = instantiations[i];
      vector<ArgsVec> new_instantiation;
      for (unsigned j = 0; j < instantiation.size(); ++j) {
        new_instantiation.push_back(instantiation[j]); 
      }
      new_instantiation.push_back(match);
      new_instantiations.push_back(new_instantiation); 
    }
  }
}


void AbstractionModule::getMatches(TNode node, ArgsTableEntry& matches) {
  Debug("bv-abstraction-dbg") << "AbstractionModule::getMatches for " << node <<"\n";
  Assert (node.getKind() == kind::APPLY_UF);
  Assert (node.getNumChildren() == matches.getArity()); 
  TNode function = node.getOperator(); 
  ArgsTableEntry& entry = d_argsTable.getEntry(function);
  for (ArgsTableEntry::iterator it = entry.begin(); it != entry.end(); ++it) {
    const ArgsVec& match_args = *it;

    bool consistent = true;
    Debug("bv-abstraction-dbg") << "[";
    for (unsigned i = 0; i < match_args.size(); ++i) {
      Debug("bv-abstraction-dbg") <<match_args[i] << " ";
      TNode arg = node[i];
      if (arg.getKind() == kind::CONST_BITVECTOR &&
          match_args[i].getKind() == kind::CONST_BITVECTOR &&
          match_args[i] != arg) {
        consistent = false;
      }
    }
    Debug("bv-abstraction-dbg") << "]\n";
    if (consistent) {
      matches.addArguments(*it); 
    }
  }
}

void AbstractionModule::ArgsTableEntry::addArguments(const ArgsVec& args) {
  Assert (args.size() == d_arity);
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
  Assert (hasEntry(signature));
  return d_data.find(signature)->second; 
}

