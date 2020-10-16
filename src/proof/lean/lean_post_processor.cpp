#include "proof/lean/lean_post_processor.h"

#include "../../expr/proof_node_updater.h"
#include "expr/lazy_proof.h"
#include "expr/proof_node_algorithm.h"

namespace CVC4 {

namespace proof {

LeanProofPostproccessCallback::LeanProofPostproccessCallback(
    ProofNodeManager* pnm)
    : d_pnm(pnm)
{
}

LeanProofPostproccess::LeanProofPostproccess(ProofNodeManager* pnm)
    : d_cb(new proof::LeanProofPostproccessCallback(pnm)), d_pnm(pnm)
{
}

bool LeanProofPostproccessCallback::shouldUpdate(std::shared_ptr<ProofNode> pn,
                                                bool& continueUpdate)
{
  return false;
};

bool LeanProofPostproccessCallback::update(Node res,
                                          PfRule id,
                                          const std::vector<Node>& children,
                                          const std::vector<Node>& args,
                                          CDProof* cdp,
                                          bool& continueUpdate)
{
  return true;
};

void LeanProofPostproccess::process(std::shared_ptr<ProofNode> pf){};
}  // namespace proof
}  // namespace CVC4
