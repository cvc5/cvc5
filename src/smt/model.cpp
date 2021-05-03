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

#include "expr/expr_iomanip.h"
#include "options/base_options.h"
#include "printer/printer.h"
#include "smt/dump_manager.h"
#include "smt/node_command.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/theory_model.h"

namespace cvc5 {
namespace smt {

Model::Model(theory::TheoryModel* tm) : d_isKnownSat(false), d_tmodel(tm)
{
  Assert(d_tmodel != nullptr);
}

std::ostream& operator<<(std::ostream& out, const Model& m) {
  expr::ExprDag::Scope scope(out, false);
  Printer::getPrinter(options::outputLanguage())->toStream(out, m);
  return out;
}

theory::TheoryModel* Model::getTheoryModel() { return d_tmodel; }

const theory::TheoryModel* Model::getTheoryModel() const { return d_tmodel; }

bool Model::isModelCoreSymbol(TNode sym) const
{
  return d_tmodel->isModelCoreSymbol(sym);
}
Node Model::getValue(TNode n) const { return d_tmodel->getValue(n); }

bool Model::hasApproximations() const { return d_tmodel->hasApproximations(); }

void Model::clearModelDeclarations()
{
  d_declareTerms.clear();
  d_declareSorts.clear();
}

void Model::addDeclarationSort(TypeNode tn) { d_declareSorts.push_back(tn); }

void Model::addDeclarationTerm(Node n) { d_declareTerms.push_back(n); }
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
