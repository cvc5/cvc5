/******************************************************************************
 * Top contributors (to current version):
 *   Daneshvar Amrollahi
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Normalizes the input benchmark regardless of the symbol names and assertion
 * order.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__NORMALIZE_H
#define CVC5__PREPROCESSING__PASSES__NORMALIZE_H

#include <unordered_map>

#include "preprocessing/preprocessing_pass.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

/**
 * Struct for storing information about a node, used for normalization.
 */
struct NodeInfo
{
  /** The node itself. */
  Node node;
  /** Compressed string encoding of the DAG, aka patterns. */
  std::string encoding;
  /** Equivalence class ID. */
  size_t equivClass;
  /** First occurrence index (counter) of each symbol when traversing the DAG,
   * aka super-pattern */
  std::unordered_map<std::string, int32_t> role;
  /** Variable names and their indices. */
  std::vector<std::pair<std::string, int32_t>> varNames;
  /** Index of the assertion after first round of sorting. */
  size_t id;

  /** Default constructor. */
  NodeInfo() {}

  /**
   * Constructor with parameters.
   * @param n The node.
   * @param enc Compressed encoding string.
   * @param eqClass Equivalence class ID.
   * @param r Role map.
   * @param vn Variable names and indices.
   */
  NodeInfo(const Node& n,
           const std::string& enc,
           uint32_t eqClass,
           const std::unordered_map<std::string, int32_t>& r,
           const std::vector<std::pair<std::string, int32_t>>& vn)
      : node(n), encoding(enc), equivClass(eqClass), role(r), varNames(vn)
  {
  }

  /**
   * Print node information to stdout.
   */
  void print() const
  {
    std::cout << "Node : " << node << std::endl;
    std::cout << "Encoding: " << encoding << std::endl;
    std::cout << "Roles: ";
    for (const auto& [symbol, idx] : role)
    {
      std::cout << symbol << " : " << idx << " , ";
    }
    std::cout << std::endl;
    std::cout << "Symbols: ";
    for (const auto& [symbol, idx] : varNames)
    {
      std::cout << symbol << " : " << idx << " , ";
    }
    std::cout << std::endl;
  }

  /**
   * Set the ID of the node.
   * @param i The ID to set.
   */
  void setId(uint32_t i) { id = i; }
};

/**
 * Preprocessing pass for normalizing assertions.
 */
class Normalize : public PreprocessingPass
{
 public:
  /**
   * Construct a Normalize preprocessing pass.
   * @param preprocContext The preprocessing pass context.
   */
  Normalize(PreprocessingPassContext* preprocContext);

 protected:
  /**
   * Apply normalization to the assertions to preprocess.
   * @param assertionsToPreprocess The assertions pipeline.
   * @return The result of preprocessing.
   */
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:
  /**
   * Struct for tracking statistics of the normalization pass.
   */
  struct Statistics
  {
    /** Timer for the normalization pass. */
    TimerStat d_passTime;
    /** Construct statistics and register them. */
    Statistics(StatisticsRegistry& reg);
  };

  /**
   * Get information about a node.
   * @param node The node to analyze.
   * @return Unique pointer to NodeInfo.
   */
  std::unique_ptr<NodeInfo> getNodeInfo(const Node& node);

  /** Statistics for the normalization pass. */
  Statistics d_statistics;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__NORMALIZE_H */
