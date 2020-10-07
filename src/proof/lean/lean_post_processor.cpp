#include "proof/lean/lean_post_processor.h"

#include "../../expr/proof_node_updater.h"
#include "expr/lazy_proof.h"
#include "expr/proof_node_algorithm.h"

namespace CVC4 {

namespace proof {

LeanProofPostprocessCallback::LeanProofPostprocessCallback(
    ProofNodeManager* pnm)
    : d_pnm(pnm)
{
}

LeanProofPostprocess::LeanProofPostprocess(ProofNodeManager* pnm)
    : d_cb(new proof::LeanProofPostprocessCallback(pnm)), d_pnm(pnm)
{
}

bool LeanProofPostprocessCallback::shouldUpdate(std::shared_ptr<ProofNode> pn,
                                                bool& continueUpdate)
{
  return false;
};

bool LeanProofPostprocessCallback::update(Node res,
                                          PfRule id,
                                          const std::vector<Node>& children,
                                          const std::vector<Node>& args,
                                          CDProof* cdp,
                                          bool& continueUpdate)
{
  return true;
};

void LeanProofPostprocess::process(std::shared_ptr<ProofNode> pf){};
}  // namespace proof
}  // namespace CVC4
