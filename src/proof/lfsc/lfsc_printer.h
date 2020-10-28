/*********************                                                        */
/*! \file lfsc_printer.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for printing Lfsc proof nodes
 **/

#include "cvc4_private.h"

#ifndef CVC4__PROOF__LFSC__LFSC_PRINTER_H
#define CVC4__PROOF__LFSC__LFSC_PRINTER_H

#include <iostream>
#include <map>

#include "expr/proof_node.h"
#include "expr/node.h"
#include "proof/lfsc/lfsc_term_process.h"

namespace CVC4 {
namespace proof {

/**
 * LFSC rules
 */
enum class LfscRule : uint32_t
{
  NONE,
};

class LfscPrinter
{
public:
  /**
   * Print the full proof of assertions => false by pn.
   */
  void print(std::ostream& out, const std::vector<Node>& assertions, const ProofNode* pn);
  /**
   * Print node to stream in the expected format of LFSC.
   */
  void print(std::ostream& out, const ProofNode* pn);
  
  /**
   * Print node to stream in the expected format of LFSC.
   */
  void print(std::ostream& out, Node n);
  /**
   * Print type node to stream in the expected format of LFSC.
   */
  void print(std::ostream& out, TypeNode n);
private:
  /**
   * Print node to stream in the expected format of LFSC.
   */
  void printLetify(std::ostream& out, Node n);
  /**
   * Print node to stream in the expected format of LFSC.
   */
  void printInternal(std::ostream& out, Node n, const std::map<Node, uint32_t>& letMap);
  /**
   * Print type node to stream in the expected format of LFSC.
   */
  void printInternal(std::ostream& out, TypeNode n);
  
  //------------------------------ printing proofs
  /** A term or a proof */
  class PExpr
  {
  public:
    PExpr() : d_node(), d_pnode(nullptr){}
    PExpr(Node n) : d_node(n), d_pnode(nullptr){}
    PExpr(const ProofNode * pn) : d_node(), d_pnode(pn) {}
    ~PExpr(){}
    Node d_node;
    const ProofNode * d_pnode;
  };
  /** A hole */
  PExpr d_hole;
  /**
   * Print proof internal, after term lets and proofs for assumptions have
   * been computed.
   */
  void printProofLetify(std::ostream& out, const ProofNode* pn, std::map<Node, uint32_t>& letMap, std::map<Node, uint32_t>& passumeMap);
  /**
   * Print proof internal, after all mappings have been computed.
   */
  void printProofInternal(std::ostream& out, const ProofNode* pn, std::map<Node, uint32_t>& letMap, std::map<const ProofNode*, uint32_t>& pletMap, std::map<Node, uint32_t>& passumeMap);
  /**
   * Get the arguments for the proof node application
   */
  void computeProofArgs(const ProofNode* pn, std::vector<PExpr>& pargs);
  //------------------------------ end printing proofs
  
  
  //------------------- letification of terms
  /** stores nodes in map that require letification */
  static void computeLet(Node n, std::vector<Node>& letList, std::map<Node, uint32_t>& letMap, uint32_t& counter);
  /** 
   * Compute the count of sub nodes in pn, store in pcount. Additionally,
   * store each node in the domain of pcount in an order in visitList
   * such that visitList[i] does not contain sub visitList[j] for j>i.
   */
  static void computeCounts(Node n, std::vector<Node>& visitList, std::map<Node, uint32_t>& count);
  /** 
   * Convert a count to a let list
   */
  static void convertCountToLet(const std::vector<Node>& visitList, const std::map<Node, uint32_t>& count, std::vector<Node>& letList, std::map<Node, uint32_t>& pletMap, uint32_t& counter);
  //------------------- end letification of terms
  
  //------------------- letification of proofs
  /** 
   * Stores proofs in map that require letification, mapping them to a unique
   * identifier, allocated in pcounter. For store each proof node in the domain 
   * of pletMap in the list pletList such that pletList[i] does not contain sub
   * proof pletList[j] for j>i.
   */
  static void computeProofLet(const ProofNode* pn, std::vector<const ProofNode *>& pletList, std::map<const ProofNode*, uint32_t>& pletMap, uint32_t& pcounter);
  /** 
   * Compute the count of sub proof nodes in pn, store in pcount. Additionally,
   * store each proof node in the domain of pcount in an order in visitList
   * such that visitList[i] does not contain sub proof visitList[j] for j>i.
   */
  static void computeProofCounts(const ProofNode* pn, std::vector<const ProofNode *>& visitList, std::map<const ProofNode*, uint32_t>& pcount);
  /** 
   * Convert a count to a let list
   */
  static void convertProofCountToLet(const std::vector<const ProofNode *>& visitList, const std::map<const ProofNode*, uint32_t>& pcount, std::vector<const ProofNode *>& pletList, std::map<const ProofNode*, uint32_t>& pletMap, uint32_t& pcounter);
  //------------------- end letification of proofs
  
  //------------------- atomic printing
  void printRule(std::ostream& out, const ProofNode*);
  void printId(std::ostream& out, uint32_t id);
  void printProofId(std::ostream& out, uint32_t id);
  void printAssumeId(std::ostream& out, uint32_t id);
  //------------------- end atomic printing
  
  /** The null term, which is used as a hole */
  Node d_null;
};

}  // namespace proof
}  // namespace CVC4

#endif
