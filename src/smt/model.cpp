/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of Model class.
 */

#include "smt/model.h"

#include "options/base_options.h"
#include "options/io_utils.h"
#include "printer/printer.h"

namespace cvc5::internal {
namespace smt {

Model::Model(bool isKnownSat, const std::string& inputName)
    : d_inputName(inputName), d_isKnownSat(isKnownSat)
{
}

std::ostream& operator<<(std::ostream& out, const Model& m) {
  options::ioutils::Scope scope(out);
  options::ioutils::applyDagThresh(out, 0);
  Printer::getPrinter(out)->toStream(out, m);
  return out;
}

const std::vector<Node>& Model::getDomainElements(TypeNode tn) const
{
  std::map<TypeNode, std::vector<Node>>::const_iterator it =
      d_domainElements.find(tn);
  Assert(it != d_domainElements.end());
  return it->second;
}

Node Model::getValue(TNode n) const
{
  std::map<Node, Node>::const_iterator it = d_declareTermValues.find(n);
  Assert(it != d_declareTermValues.end());
  return it->second;
}

bool Model::getHeapModel(Node& h, Node& nilEq) const
{
  if (d_sepHeap.isNull() || d_sepNilEq.isNull())
  {
    return false;
  }
  h = d_sepHeap;
  nilEq = d_sepNilEq;
  return true;
}

void Model::addDeclarationSort(TypeNode tn, const std::vector<Node>& elements)
{
  d_declareSorts.push_back(tn);
  d_domainElements[tn] = elements;
}

void Model::addDeclarationTerm(Node n, Node value)
{
  d_declareTerms.push_back(n);
  d_declareTermValues[n] = value;
}

void Model::setHeapModel(Node h, Node nilEq)
{
  d_sepHeap = h;
  d_sepNilEq = nilEq;
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
}  // namespace cvc5::internal
