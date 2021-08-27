/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of Model class.
 */

#include "smt/model.h"

namespace cvc5 {
namespace smt {

Model::Model() : d_isKnownSat(false)
{
}

std::ostream& operator<<(std::ostream& out, const Model& m) {
  expr::ExprDag::Scope scope(out, false);
  Printer::getPrinter(options::outputLanguage())->toStream(out, m);
  return out;
}

const std::vector<Node>& Model::getDomainElements(TypeNode tn) const
{
  std::map<TypeNode, std::vector<Node>>::const_iterator it =  d_domainElements.find(tn);
  Assert (it!=d_domainElements.end());
  return it->second;
}

Node Model::getValue(TNode n) const { 
  std::map<Node,Node>::const_iterator it = d_declareTermValues.find(n);
  Assert (it!=d_declareTermValues.end());
  return it->second;
}

void Model::clearModelDeclarations()
{
  d_declareTerms.clear();
  d_declareSorts.clear();
}

void Model::addDeclarationSort(TypeNode tn, const std::vector<Node>& elements) { 
  d_declareSorts.push_back(tn);
  d_domainElements[tn] = elements;
}

void Model::addDeclarationTerm(Node n, Node value) { 
  d_declareTerms.push_back(n); 
  d_declareTermValues[n] = value;
}
const std::vector<TypeNode>& Model::getDeclaredSorts() const
{
  return d_declareSorts;
}
const std::vector<Node>& Model::getDeclaredTerms() const
{
  return d_declareTerms;
}

}  // namespace smt
}  // namespace cvc5
