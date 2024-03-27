/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mudathir Mohamed, Kshitij Bansal
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Skolem manager utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__EXPR__SKOLEM_MANAGER_H
#define CVC5__EXPR__SKOLEM_MANAGER_H

#include <cvc5/cvc5_skolem_id.h>

#include <string>

#include "expr/node.h"

namespace cvc5::internal {

class ProofGenerator;

/**
 * Internal skolem function identifier, used for identifying internal skolems
 * that are not exported as part of the API.
 *
 * This is a subclassification of skolems whose SkolemId is INTERNAL. It is
 * used to generate canonical skolems but without exporting to the API. Skolems
 * can be created using mkInternalSkolemFunction below.
 */
enum class InternalSkolemId
{
  NONE,
  /** Sequence model construction, element for base */
  SEQ_MODEL_BASE_ELEMENT,
  /** the "none" term, for instantiation evaluation */
  IEVAL_NONE,
  /** the "some" term, for instantiation evaluation */
  IEVAL_SOME,
  /** sygus "any constant" placeholder */
  SYGUS_ANY_CONSTANT,
  /**
   * Quantifiers synth fun embedding, for function-to-synthesize, this the
   * first order datatype variable for f.
   */
  QUANTIFIERS_SYNTH_FUN_EMBED,
  /** Higher-order type match predicate, see HoTermDb */
  HO_TYPE_MATCH_PRED,
  /** abstract value for a term t */
  ABSTRACT_VALUE,
};
/** Converts an internal skolem function name to a string. */
const char* toString(InternalSkolemId id);
/** Writes an internal skolem function name to a stream. */
std::ostream& operator<<(std::ostream& out, InternalSkolemId id);

/**
 * A manager for skolems that can be used in proofs. This is designed to be
 * a trusted interface for constructing variables of SKOLEM type, where one
 * must provide information that characterizes the skolem. This information
 * may either be:
 * (1) the term that the skolem purifies (`mkPurifySkolem`)
 * (2) an identifier (`mkSkolemFunction`) and a set of "cache values", which
 * can be seen as arguments to the skolem function. These are typically used for
 * implementing theory-specific inferences that introduce symbols that
 * are not interpreted by the theory (see SkolemId enum).
 *
 * Note that (1) is a special instance of (2), where the purification skolem
 * for t is equivalent to calling mkSkolemFunction on SkolemId::PURIFY
 * and t.
 *
 * If a variable cannot be associated with any of the above information,
 * the method `mkDummySkolem` may be used, which always constructs a fresh
 * skolem variable.
 *
 * It is implemented by mapping terms to an attribute corresponding to their
 * "original form" as described below. Hence, this class does not impact the
 * reference counting of skolem variables which may be deleted if they are not
 * used.
 *
 * To handle purification of witness terms, notice that the purification
 * skolem for (witness ((x T)) P) is equivalent to the skolem function:
 *    (QUANTIFIERS_SKOLEMIZE (exists ((x T)) P) 0)
 * In other words, the purification for witness terms are equivalent to
 * the skolemization of their corresponding existential. This is currently only
 * used for eliminating witness terms coming from algorithms that introduce
 * them, e.g. BV/set instantiation. Unifying these two skolems is required
 * for ensuring proof checking succeeds for term formula removal on witness
 * terms.
 *
 * The use of purification skolems and skolem functions avoid having to reason
 * about witness terms. This avoids several complications. In particular,
 * witness terms in most contexts should be seen as black boxes, converting
 * something to a witness term may have unintended consequences e.g. variable
 * shadowing. In contrast, converting to original form does not have these
 * complications. Furthermore, having original form greatly simplifies
 * reasoning in the proof in certain external proof formats, in particular, it
 * avoids the need to reason about identifiers for introduced variables for
 * the binders of witness terms.
 */
class SkolemManager
{
 public:
  SkolemManager();
  ~SkolemManager() {}

  /**
   * Optional flags used to control behavior of skolem creation.
   * They should be composed with a bitwise OR.
   */
  enum SkolemFlags
  {
    /** default behavior */
    SKOLEM_DEFAULT = 0,
    /** do not make the name unique by adding the id */
    SKOLEM_EXACT_NAME = 1,
  };
  /**
   * Make purification skolem. This skolem is unique for each t, which we
   * implement via an attribute on t. This attribute is used to ensure to
   * associate a unique skolem for each t.
   *
   * Notice that a purification skolem is trivial to justify (via
   * SKOLEM_INTRO), and hence it does not require a proof generator.
   *
   * Notice that we do not convert t to original form in this call. Thus,
   * in very rare cases, two Skolems may be introduced that have the same
   * original form. For example, let k be the skolem introduced to eliminate
   * (ite A B C). Then, asking for the purify skolem for:
   *  (ite (ite A B C) D E) and (ite k D E)
   * will return two different Skolems.
   *
   * @param t The term to purify
   * @param pg The proof generator for the skolemization of t. This should
   * only be provided if t is a witness term (witness ((x T)) P). If non-null,
   * this proof generator must respond to a call to getProofFor on
   * (exists ((x T)) P) during the lifetime of the current node manager.
   * @return The purification skolem for t
   */
  Node mkPurifySkolem(Node t,
                      ProofGenerator* pg = nullptr);
  /**
   * Make skolem function. This method should be used for creating fixed
   * skolem functions of the forms described in SkolemId. The user of this
   * method is responsible for providing a proper type for the identifier that
   * matches the description of id. Skolem functions are useful for modelling
   * the behavior of partial functions, or for theory-specific inferences that
   * introduce fresh variables.
   *
   * A skolem function is not given a formal semantics in terms of a witness
   * term, nor is it a purification skolem, thus it does not fall into the two
   * categories of skolems above. This method is motivated by convenience, as
   * the user of this method does not require constructing canonical variables
   * for witness terms.
   *
   * The returned skolem is an ordinary skolem variable that can be used
   * e.g. in APPLY_UF terms when tn is a function type.
   *
   * Notice that we do not insist that tn is a function type. A user of this
   * method may construct a canonical (first-order) skolem using this method
   * as well.
   *
   * @param id The identifier of the skolem function
   * @param cacheVal A cache value. The returned skolem function will be
   * unique to the pair (id, cacheVal). This value is required, for instance,
   * for skolem functions that are in fact families of skolem functions,
   * e.g. the wrongly applied case of selectors.
   * @return The skolem function.
   */
  Node mkSkolemFunction(SkolemId id, Node cacheVal = Node::null());
  /** Same as above, with multiple cache values */
  Node mkSkolemFunction(SkolemId id, const std::vector<Node>& cacheVals);
  /**
   * Same as above, with multiple cache values and an internal skolem id.
   * This will call mkSkolemFunction where the (external) id is
   * SkolemId::INTERNAL. The type is provided explicitly.
   */
  Node mkInternalSkolemFunction(InternalSkolemId id,
                                TypeNode tn,
                                const std::vector<Node>& cacheVals = {});
  /**
   * Is k a skolem function? Returns true if k was generated by the above
   * call.
   */
  bool isSkolemFunction(TNode k) const;
  /**
   * Is k a skolem function? Returns true if k was generated by the above
   * call. Updates the arguments to the values used when constructing it.
   */
  bool isSkolemFunction(TNode k, SkolemId& id, Node& cacheVal) const;
  /**
   * Get skolem function id
   */
  SkolemId getId(TNode k) const;
  /**
   * Get the internal skolem function id, for skolems whose id is
   * SkolemId::INTERNAL.
   */
  InternalSkolemId getInternalId(TNode k) const;
  /**
   * Create a skolem constant with the given name, type, and comment. This
   * should only be used if the definition of the skolem does not matter.
   * The definition of a skolem matters e.g. when the skolem is used in a
   * proof.
   *
   * @param prefix the name of the new skolem variable is the prefix
   * appended with a unique ID.  This way a family of skolem variables
   * can be made with unique identifiers, used in dump, tracing, and
   * debugging output.  Use SKOLEM_EXACT_NAME flag if you don't want
   * a unique ID appended and use prefix as the name.
   * @param type the type of the skolem variable to create
   * @param comment a comment for dumping output; if declarations are
   * being dumped, this is included in a comment before the declaration
   * and can be quite useful for debugging
   * @param flags an optional mask of bits from SkolemFlags to control
   * skolem behavior
   */
  Node mkDummySkolem(const std::string& prefix,
                     const TypeNode& type,
                     const std::string& comment = "",
                     int flags = SKOLEM_DEFAULT);
  /**
   * Get proof generator for existentially quantified formula q. This returns
   * the proof generator that was provided in a call to `mkSkolemize` above.
   */
  ProofGenerator* getProofGenerator(Node q) const;
  /** Returns true if n is a skolem that stands for an abstract value */
  bool isAbstractValue(TNode n) const;
  /**
   * Convert to original form, which recursively replaces all skolems terms in
   * n by the term they purify.
   *
   * @param n The term or formula to convert to original form described above
   * @return n in original form.
   */
  static Node getOriginalForm(Node n);
  /**
   * Convert to unpurified form, which returns the term that k purifies. This
   * is literally the term that was passed as an argument to mkPurify on the
   * call that created k. In contrast to getOriginalForm, this is not
   * recursive w.r.t. skolems, so that the term purified by k may itself
   * contain purification skolems that are not expanded.
   *
   * @param k The skolem to convert to unpurified form
   * @return the unpurified form of k.
   */
  static Node getUnpurifiedForm(Node k);

 private:
  /** Cache of skolem functions for mkSkolemFunction above. */
  std::map<std::tuple<SkolemId, TypeNode, Node>, Node> d_skolemFuns;
  /** Backwards mapping of above */
  std::map<Node, std::tuple<SkolemId, TypeNode, Node>> d_skolemFunMap;
  /**
   * Mapping from witness terms to proof generators.
   */
  std::map<Node, ProofGenerator*> d_gens;

  /**
   * A counter used to produce unique skolem names.
   *
   * Note that it is NOT incremented when skolems are created using
   * SKOLEM_EXACT_NAME, so it is NOT a count of the skolems produced
   * by this node manager.
   */
  size_t d_skolemCounter;
  /** Same as mkSkolemFunction, with explicit type */
  Node mkSkolemFunctionTyped(SkolemId id,
                             TypeNode tn,
                             Node cacheVal = Node::null());
  /** Same as above, with multiple cache values and explicit Type */
  Node mkSkolemFunctionTyped(SkolemId id,
                             TypeNode tn,
                             const std::vector<Node>& cacheVals);
  /**
   * Create a skolem constant with the given name, type, and comment.
   *
   * This method is intentionally private. To create skolems, one should
   * call a public method from SkolemManager for allocating a skolem in a
   * proper way, or otherwise use SkolemManager::mkDummySkolem.
   */
  Node mkSkolemNode(Kind k,
                    const std::string& prefix,
                    const TypeNode& type,
                    int flags = SKOLEM_DEFAULT);
  /** Get type for skolem */
  TypeNode getTypeFor(SkolemId id, const std::vector<Node>& cacheVals);
};

}  // namespace cvc5::internal

#endif /* CVC5__EXPR__PROOF_SKOLEM_CACHE_H */
