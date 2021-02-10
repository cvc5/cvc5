/*********************                                                        */
/*! \file infer_info.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Inference information utility
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BAGS__INFER_INFO_H
#define CVC4__THEORY__BAGS__INFER_INFO_H

#include <map>
#include <vector>

#include "expr/node.h"
#include "theory/theory_inference.h"

namespace CVC4 {
namespace theory {
namespace bags {

/**
 * Types of inferences used in the procedure
 */
enum class Inference : uint32_t
{
  NONE,
  BAG_NON_NEGATIVE_COUNT,
  BAG_MK_BAG_SAME_ELEMENT,
  BAG_MK_BAG,
  BAG_EQUALITY,
  BAG_DISEQUALITY,
  BAG_EMPTY,
  BAG_UNION_DISJOINT,
  BAG_UNION_MAX,
  BAG_INTERSECTION_MIN,
  BAG_DIFFERENCE_SUBTRACT,
  BAG_DIFFERENCE_REMOVE,
  BAG_DUPLICATE_REMOVAL
};

/**
 * Converts an inference to a string. Note: This function is also used in
 * `safe_print()`. Changing this functions name or signature will result in
 * `safe_print()` printing "<unsupported>" instead of the proper strings for
 * the enum values.
 *
 * @param i The inference
 * @return The name of the inference
 */
const char* toString(Inference i);

/**
 * Writes an inference name to a stream.
 *
 * @param out The stream to write to
 * @param i The inference to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, Inference i);

class InferenceManager;

/**
 * An inference. This is a class to track an unprocessed call to either
 * send a fact, lemma, or conflict that is waiting to be asserted to the
 * equality engine or sent on the output channel.
 */
class InferInfo : public TheoryInference
{
 public:
  InferInfo();
  ~InferInfo() {}
  /** Process this inference */
  bool process(TheoryInferenceManager* im, bool asLemma) override;
  /** The inference identifier */
  Inference d_id;
  /** The conclusions */
  Node d_conclusion;
  /**
   * The premise(s) of the inference, interpreted conjunctively. These are
   * literals that currently hold in the equality engine.
   */
  std::vector<Node> d_premises;

  /**
   * A map of nodes to their skolem variables introduced as a result of this
   * inference.
   */
  std::map<Node, Node> d_skolems;
  /**  Is this infer info trivial? True if d_conc is true. */
  bool isTrivial() const;
  /**
   * Does this infer info correspond to a conflict? True if d_conc is false
   * and it has no new premises (d_noExplain).
   */
  bool isConflict() const;
  /**
   * Does this infer info correspond to a "fact". A fact is an inference whose
   * conclusion should be added as an equality or predicate to the equality
   * engine with no new external premises (d_noExplain).
   */
  bool isFact() const;
};

/**
 * Writes an inference info to a stream.
 *
 * @param out The stream to write to
 * @param ii The inference info to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, const InferInfo& ii);

}  // namespace bags
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__BAGS__INFER_INFO_H */
