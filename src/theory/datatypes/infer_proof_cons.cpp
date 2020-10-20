/*********************                                                        */
/*! \file infer_proof_cons.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of inference to proof conversion  for datatypes
 **/

#include "theory/datatypes/infer_proof_cons.h"

#include "theory/rewriter.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace datatypes {

InferProofCons::InferProofCons(context::Context* c, ProofNodeManager* pnm)
    : d_pnm(pnm), d_lazyFactMap(c)
{
  Assert(d_pnm != nullptr);
}

void InferProofCons::notifyFact(std::shared_ptr<DatatypesInference> di)
{
  Node fact = di->d_conc;
  if (d_lazyFactMap.find(fact) != d_lazyFactMap.end())
  {
    return;
  }
  Node symFact = CDProof::getSymmFact(fact);
  if (!symFact.isNull() && d_lazyFactMap.find(symFact) != d_lazyFactMap.end())
  {
    return;
  }
  d_lazyFactMap.insert(fact, di);
}

void InferProofCons::convert(InferId infer, Node conc, Node exp, CDProof* cdp)
{
  Trace("dt-ipc") << "convert: " << infer << ": " << conc << " by " << exp
                  << std::endl;
  NodeManager * nm = NodeManager::currentNM();
  bool success = false;
  switch (infer)
  {
    case InferId::UNIF: 
    {
      Assert (exp.getKind()==EQUAL && exp[0].getKind()==APPLY_CONSTRUCTOR && exp[1].getKind()==APPLY_CONSTRUCTOR && exp[0].getOperator()==exp[1].getOperator());
      Assert (conc.getKind()==EQUAL);
      Node narg;
      for (size_t i=0, nchild = exp[0].getNumChildren(); i<nchild; i++)
      {
        if (exp[0][i]==conc[0] && exp[1][i]==conc[1])
        {
          narg = nm->mkConst(Rational(i));
          break;
        }
      }
      if (!narg.isNull())
      {
        cdp->addStep(conc, PfRule::DT_UNIF, {exp}, {narg});
        success = true;
      }
    }
      break;
    case InferId::INST: 
    {
    }
      break;
    case InferId::SPLIT: 
    {
      Assert (exp.isNull());
      Node t = conc.getKind()==OR ? conc[0][0] : conc[0];
      cdp->addStep(conc, PfRule::DT_SPLIT, {}, {t});
    }
      break;
    case InferId::LABEL_EXH: break;
    case InferId::COLLAPSE_SEL: break;
    case InferId::CLASH_CONFLICT: break;
    case InferId::TESTER_CONFLICT: break;
    case InferId::TESTER_MERGE_CONFLICT: break;
    case InferId::BISIMILAR: break;
    case InferId::CYCLE: break;
    default:
      Trace("dt-ipc") << "...no conversion for inference " << infer
                      << std::endl;
      break;
  }

  if (!success)
  {
    // failed to reconstruct, add trust
    Trace("dt-ipc") << "...failed " << infer << std::endl;
    cdp->addStep(conc, PfRule::DT_TRUST, {}, {conc});
  }
}

std::shared_ptr<ProofNode> InferProofCons::getProofFor(Node fact)
{
  // temporary proof
  CDProof pf(d_pnm);
  // get the inference
  NodeDatatypesInferenceMap::iterator it = d_lazyFactMap.find(fact);
  if (it == d_lazyFactMap.end())
  {
    Node factSym = CDProof::getSymmFact(fact);
    if (!factSym.isNull())
    {
      // Use the symmetric fact. There is no need to explictly make a
      // SYMM proof, as this is handled by CDProof::getProofFor below.
      it = d_lazyFactMap.find(factSym);
    }
  }
  AlwaysAssert(it != d_lazyFactMap.end());
  // now go back and convert it to proof steps and add to proof
  std::shared_ptr<DatatypesInference> di = (*it).second;
  // run the conversion
  convert(di->getInferId(), di->d_conc, di->d_exp, &pf);
  return pf.getProofFor(fact);
}

std::string InferProofCons::identify() const
{
  return "datatypes::InferProofCons";
}

}  // namespace datatypes
}  // namespace theory
}  // namespace CVC4
