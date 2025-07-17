/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Abdalrhman Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Proof rule enumeration.
 */

#if (!defined(CVC5_API_USE_C_ENUMS)                 \
     && !defined(CVC5__API__CVC5_CPP_PROOF_RULE_H)) \
    || (defined(CVC5_API_USE_C_ENUMS)               \
        && !defined(CVC5__API__CVC5_C_PROOF_RULE_H))

#include <stdint.h>

#ifdef CVC5_API_USE_C_ENUMS
#undef ENUM
#define ENUM(name) Cvc5##name
#else
#include <cvc5/cvc5_export.h>

#include <iosfwd>
#include <ostream>
namespace cvc5 {
#undef ENUM
#define ENUM(name) class name
#define EVALUE(name) name
#endif

#ifdef CVC5_API_USE_C_ENUMS
#undef EVALUE
#define EVALUE(name) CVC5_PROOF_RULE_##name
#endif

// clang-format off
/**
 * \internal
 * This documentation is target for the online documentation that can
 * be found at https://cvc5.github.io/docs/latest/proofs/proof_rules.html
 * \endinternal
 *
 * \verbatim embed:rst:leading-asterisk
 * An enumeration for proof rules. This enumeration is analogous to Kind for
 * Node objects.
 *
 * All proof rules are given as inference rules, presented in the following
 * form:
 *
 * .. math::
 *
 *   \texttt{RULENAME}:
 *   \inferruleSC{\varphi_1 \dots \varphi_n \mid t_1 \dots t_m}{\psi}{if $C$}
 *
 * where we call :math:`\varphi_i` its premises or children, :math:`t_i` its
 * arguments, :math:`\psi` its conclusion, and :math:`C` its side condition.
 * Alternatively, we can write the application of a proof rule as
 * ``(RULENAME F1 ... Fn :args t1 ... tm)``, omitting the conclusion
 * (since it can be uniquely determined from premises and arguments).
 * Note that premises are sometimes given as proofs, i.e., application of
 * proof rules, instead of formulas. This abuses the notation to see proof
 * rule applications and their conclusions interchangeably.
 *
 * Conceptually, the following proof rules form a calculus whose target
 * user is the Node-level theory solvers. This means that the rules below
 * are designed to reason about, among other things, common operations on Node
 * objects like Rewriter::rewrite or Node::substitute. It is intended to be
 * translated or printed in other formats.
 *
 * The following ProofRule values include core rules and those categorized by
 * theory, including the theory of equality.
 *
 * The "core rules" include two distinguished rules which have special status:
 * (1) :cpp:enumerator:`ASSUME <cvc5::ProofRule::ASSUME>`, which represents an
 * open leaf in a proof; and
 * (2) :cpp:enumerator:`SCOPE <cvc5::ProofRule::SCOPE>`, which encloses a scope
 * (a subproof) with a set of scoped assumptions.
 * The core rules additionally correspond to generic operations that are done
 * internally on nodes, e.g., calling `Rewriter::rewrite()`.
 *
 * Rules with prefix ``MACRO_`` are those that can be defined in terms of other
 * rules. These exist for convenience and can be replaced by their definition
 * in post-processing.
 * \endverbatim
 */
enum ENUM(ProofRule)
{
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Assumption (a leaf)**
   *
   * .. math::
   *
   *   \inferrule{- \mid F}{F}
   *
   * This rule has special status, in that an application of assume is an
   * open leaf in a proof that is not (yet) justified. An assume leaf is
   * analogous to a free variable in a term, where we say "F is a free
   * assumption in proof P" if it contains an application of F that is not
   * bound by :cpp:enumerator:`SCOPE <cvc5::ProofRule::SCOPE>` (see below).
   * \endverbatim
   */
  EVALUE(ASSUME),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Scope (a binder for assumptions)**
   *
   * .. math::
   *
   *   \inferruleSC{F \mid F_1 \dots F_n}{(F_1 \land \dots \land F_n)
   *   \Rightarrow F}{if $F\neq\bot$} \textrm{ or } \inferruleSC{F \mid F_1
   *   \dots F_n}{\neg (F_1 \land \dots \land F_n)}{if $F=\bot$}
   *
   * This rule has a dual purpose with
   * :cpp:enumerator:`ASSUME <cvc5::ProofRule::ASSUME>`. It is a way to close
   * assumptions in a proof. We require that :math:`F_1 \dots F_n` are free
   * assumptions in P and say that :math:`F_1 \dots F_n` are not free in
   * ``(SCOPE P)``. In other words, they are bound by this application. For
   * example, the proof node:
   * ``(SCOPE (ASSUME F) :args F)``
   * has the conclusion :math:`F \Rightarrow F` and has no free assumptions.
   * More generally, a proof with no free assumptions always concludes a valid
   * formula.
   * \endverbatim
   */
  EVALUE(SCOPE),

  /**
   * \verbatim embed:rst:leading-asterisk
   * **Builtin theory -- Substitution**
   *
   * .. math::
   *
   *   \inferrule{F_1 \dots F_n \mid t, ids?}{t = t \circ \sigma_{ids}(F_n)
   *   \circ \cdots \circ \sigma_{ids}(F_1)}
   *
   * where :math:`\sigma_{ids}(F_i)` are substitutions, which notice are applied
   * in reverse order. Notice that :math:`ids` is a MethodId identifier, which
   * determines how to convert the formulas :math:`F_1 \dots F_n` into
   * substitutions. It is an optional argument, where by default the premises
   * are equalities of the form `(= x y)` and converted into substitutions
   * :math:`x\mapsto y`.
   * \endverbatim
   */
  EVALUE(SUBS),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Builtin theory -- Rewrite**
   *
   * .. math::
   *
   *   \inferrule{- \mid t, idr}{t = \texttt{rewrite}_{idr}(t)}
   *
   * where :math:`idr` is a MethodId identifier, which determines the kind of
   * rewriter to apply, e.g., Rewriter::rewrite.
   * \endverbatim
   */
  EVALUE(MACRO_REWRITE),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Builtin theory -- Evaluate**
   *
   * .. math::
   *
   *   \inferrule{- \mid t}{t = \texttt{evaluate}(t)}
   *
   * where :math:`\texttt{evaluate}` is implemented by calling the method
   * :math:`\texttt{Evalutor::evaluate}` in :cvc5src:`theory/evaluator.h` with an
   * empty substitution.
   * Note this is equivalent to: ``(REWRITE t MethodId::RW_EVALUATE)``.
   *
   * Note this proof rule only applies to atomic sorts, that is, operators on
   * Int, Real, String, Bool or BitVector.
   * \endverbatim
   */
  EVALUE(EVALUATE),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Builtin theory -- Distinct values**
   *
   * .. math::
   *
   *   \inferrule{- \mid t, s}{\neg t = s}
   *
   * where :math:`t` and :math:`s` are distinct values.
   *
   * Note that cvc5 internally has a notion of which terms denote "values".
   * This property is implemented for any sort that can appear in equalities.
   * A term denotes a value if and only if it is the canonical representation
   * of a value of that sort. For example, set values are a chain of unions of
   * singleton sets whose elements are also values, where this chain is sorted.
   * Any two distinct values are semantically disequal in all models.
   *
   * In practice, we use this rule only to show the distinctness of non-atomic
   * sort, e.g. Sets, Sequences, Datatypes, Arrays, etc.
   *
   * Note that internally, the notion of value is implemented by the
   * Node::isConst method.
   *
   * \endverbatim
   */
  EVALUE(DISTINCT_VALUES),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Builtin theory -- associative/commutative/idempotency/identity \
   * normalization**
   *
   * .. math::
   *
   *   \inferrule{- \mid t = s}{t = s}
   *
   * where :math:`t` and :math:`s` are equivalent modulo associativity
   * and identity elements, and (optionally) commutativity and idempotency.
   *
   * This method normalizes currently based on two kinds of operators:
   * (1) those that are associative, commutative, idempotent, and have an
   * identity element (examples are or, and, bvand),
   * (2) those that are associative, commutative and have an identity
   * element (bvxor),
   * (3) those that are associative and have an identity element (examples
   * are concat, str.++, re.++).
   *
   * This is implemented internally by checking that
   * :math:`\texttt{expr::isACINorm(t, s)} = \top`. For details, see
   * :cvc5src:`expr/aci_norm.h`.
   * \endverbatim
   */
  EVALUE(ACI_NORM),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Builtin theory -- absorb**
   *
   * .. math::
   *
   *   \inferrule{- \mid t = z}{t = z}
   *
   * where :math:`t` contains :math:`z` as a subterm, where :math:`z`
   * is a zero element.
   *
   * In particular, :math:`t` is expected to be an application of a
   * function with a zero element :math:`z`, and :math:`z` is contained
   * as a subterm of :math:`t` beneath applications of that function.
   * For example, this may show that :math:`(A \wedge ( B \wedge \bot)) = \bot`.
   *
   * This is implemented internally by checking that
   * :math:`\texttt{expr::isAbsorb(t, z)} = \top`. For details, see
   * :cvc5src:`expr/aci_norm.h`.
   * \endverbatim
   */
  EVALUE(ABSORB),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Builtin theory -- Substitution + Rewriting equality introduction**
   *
   * In this rule, we provide a term :math:`t` and conclude that it is equal to
   * its rewritten form under a (proven) substitution.
   *
   * .. math::
   *
   *   \inferrule{F_1 \dots F_n \mid t, (ids (ida (idr)?)?)?}{t =
   *   \texttt{rewrite}_{idr}(t \circ \sigma_{ids, ida}(F_n) \circ \cdots \circ
   *   \sigma_{ids, ida}(F_1))}
   *
   * In other words, from the point of view of Skolem forms, this rule
   * transforms :math:`t` to :math:`t'` by standard substitution + rewriting.
   *
   * The arguments :math:`ids`, :math:`ida` and :math:`idr` are optional and
   * specify the identifier of the substitution, the substitution application
   * and rewriter respectively to be used. For details, see
   * :cvc5src:`theory/builtin/proof_checker.h`.
   * \endverbatim
   */
  EVALUE(MACRO_SR_EQ_INTRO),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Builtin theory -- Substitution + Rewriting predicate introduction**
   *
   * In this rule, we provide a formula :math:`F` and conclude it, under the
   * condition that it rewrites to true under a proven substitution.
   *
   * .. math::
   *
   *   \inferrule{F_1 \dots F_n \mid F, (ids (ida (idr)?)?)?}{F}
   *
   * where :math:`\texttt{rewrite}_{idr}(F \circ \sigma_{ids, ida}(F_n) \circ
   * \cdots \circ \sigma_{ids, ida}(F_1)) = \top` and :math:`ids` and
   * :math:`idr` are method identifiers.
   *
   * More generally, this rule also holds when
   * :math:`\texttt{Rewriter::rewrite}(\texttt{toOriginal}(F')) = \top`
   * where :math:`F'` is the result of the left hand side of the equality above.
   * Here, notice that we apply rewriting on the original form of :math:`F'`,
   * meaning that this rule may conclude an :math:`F` whose Skolem form is
   * justified by the definition of its (fresh) Skolem variables. For example,
   * this rule may justify the conclusion :math:`k = t` where :math:`k` is the
   * purification Skolem for :math:`t`, e.g. where the original form of
   * :math:`k` is :math:`t`.
   *
   * Furthermore, notice that the rewriting and substitution is applied only
   * within the side condition, meaning the rewritten form of the original form
   * of :math:`F` does not escape this rule.
   * \endverbatim
   */
  EVALUE(MACRO_SR_PRED_INTRO),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Builtin theory -- Substitution + Rewriting predicate elimination**
   *
   * .. math::
   *
   *   \inferrule{F, F_1 \dots F_n \mid (ids (ida
   *   (idr)?)?)?}{\texttt{rewrite}_{idr}(F \circ \sigma_{ids, ida}(F_n) \circ
   *   \cdots \circ \sigma_{ids, ida}(F_1))}
   *
   * where :math:`ids` and :math:`idr` are method identifiers.
   *
   * We rewrite only on the Skolem form of :math:`F`, similar to
   * :cpp:enumerator:`MACRO_SR_EQ_INTRO <cvc5::ProofRule::MACRO_SR_EQ_INTRO>`.
   * \endverbatim
   */
  EVALUE(MACRO_SR_PRED_ELIM),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Builtin theory -- Substitution + Rewriting predicate elimination**
   *
   * .. math::
   *
   *   \inferrule{F, F_1 \dots F_n \mid G, (ids (ida (idr)?)?)?}{G}
   *
   * where
   *
   * .. math::
   *
   *   \texttt{rewrite}_{idr}(F \circ \sigma_{ids, ida}(F_n) \circ\cdots \circ \sigma_{ids, ida}(F_1)) =\\ \texttt{rewrite}_{idr}(G \circ \sigma_{ids, ida}(F_n) \circ \cdots \circ \sigma_{ids, ida}(F_1))
   *
   * More generally, this rule also holds when:
   * :math:`\texttt{Rewriter::rewrite}(\texttt{toOriginal}(F')) = \texttt{Rewriter::rewrite}(\texttt{toOriginal}(G'))`
   * where :math:`F'` and :math:`G'` are the result of each side of the equation
   * above. Here, original forms are used in a similar manner to
   * :cpp:enumerator:`MACRO_SR_PRED_INTRO <cvc5::ProofRule::MACRO_SR_PRED_INTRO>`
   * above.
   * \endverbatim
   */
  EVALUE(MACRO_SR_PRED_TRANSFORM),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Builtin theory -- Encode equality introduction**
   *
   * .. math::
   *
   *   \inferrule{- \mid t}{t=t'}
   *
   * where :math:`t` and :math:`t'` are equivalent up to their encoding in an
   * external proof format.
   *
   * More specifically, it is the case that
   * :math:`\texttt{RewriteDbNodeConverter::postConvert}(t) = t;`.
   * This conversion method for instance may drop user patterns from quantified
   * formulas or change the representation of :math:`t` in a way that is a
   * no-op in external proof formats.
   *
   * Note this rule can be treated as a
   * :cpp:enumerator:`REFL <cvc5::ProofRule::REFL>` when appropriate in
   * external proof formats.
   * \endverbatim
   */
  EVALUE(ENCODE_EQ_INTRO),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Builtin theory -- DSL rewrite**
   *
   * .. math::
   *
   *   \inferrule{F_1 \dots F_n \mid id t_1 \dots t_n}{F}
   *
   * where `id` is a :cpp:enum:`ProofRewriteRule` whose definition in the
   * RARE DSL is :math:`\forall x_1 \dots x_n. (G_1 \wedge G_n) \Rightarrow G`
   * where for :math:`i=1, \dots n`, we have that :math:`F_i = \sigma(G_i)`
   * and :math:`F = \sigma(G)` where :math:`\sigma` is the substitution
   * :math:`\{x_1\mapsto t_1,\dots,x_n\mapsto t_n\}`.
   *
   * Notice that the application of the substitution takes into account the
   * possible list semantics of variables :math:`x_1 \ldots x_n`. If
   * :math:`x_i` is a variable with list semantics, then :math:`t_i` denotes a
   * list of terms. The substitution implemented by
   * :math:`\texttt{expr::narySubstitute}` (for details, see
   * :cvc5src:`expr/nary_term_util.h`) which replaces each :math:`x_i` with the
   * list :math:`t_i` in its place.
   * \endverbatim
   */
  EVALUE(DSL_REWRITE),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Other theory rewrite rules**
   *
   * .. math::
   *
   *   \inferrule{- \mid id, t = t'}{t = t'}
   *
   * where `id` is the :cpp:enum:`ProofRewriteRule` of the theory rewrite
   * rule which transforms :math:`t` to :math:`t'`.
   *
   * In contrast to :cpp:enumerator:`DSL_REWRITE`, theory rewrite rules used by
   * this proof rule are not necessarily expressible in RARE. Each rule that can
   * be used in this proof rule are documented explicitly in cases within the
   * :cpp:enum:`ProofRewriteRule` enum.
   * \endverbatim
   */
  EVALUE(THEORY_REWRITE),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Processing rules -- If-then-else equivalence**
   *
   * .. math::
   *
   *   \inferrule{- \mid \ite{C}{t_1}{t_2}}{\ite{C}{((\ite{C}{t_1}{t_2}) = t_1)}{((\ite{C}{t_1}{t_2}) = t_2)}}
   *
   * \endverbatim
   */
  EVALUE(ITE_EQ),

  /**
   * \verbatim embed:rst:leading-asterisk
   * **Trusted rule**
   *
   * .. math::
   *
   *   \inferrule{F_1 \dots F_n \mid tid, F, ...}{F}
   *
   * where :math:`tid` is an identifier and :math:`F` is a formula. This rule
   * is used when a formal justification of an inference step cannot be provided.
   * The formulas :math:`F_1 \dots F_n` refer to a set of formulas that
   * entail :math:`F`, which may or may not be provided.
   * \endverbatim
   */
  EVALUE(TRUST),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Trusted rules -- Theory rewrite**
   *
   * .. math::
   *
   *   \inferrule{- \mid F, tid, rid}{F}
   *
   * where :math:`F` is an equality of the form :math:`t = t'` where :math:`t'`
   * is obtained by applying the kind of rewriting given by the method
   * identifier :math:`rid`, which is one of:
   * ``RW_REWRITE_THEORY_PRE``, ``RW_REWRITE_THEORY_POST``,
   * ``RW_REWRITE_EQ_EXT``. Notice that the checker for this rule does not
   * replay the rewrite to ensure correctness, since theory rewriter methods are
   * not static. For example, the quantifiers rewriter involves constructing new
   * bound variables that are not guaranteed to be consistent on each call.
   * \endverbatim
   */
  EVALUE(TRUST_THEORY_REWRITE),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **SAT Refutation for assumption-based unsat cores**
   *
   * .. math::
   *
   *   \inferrule{F_1 \dots F_n \mid -}{\bot}
   *
   * where :math:`F_1 \dots F_n` correspond to the unsat core determined by the
   * SAT solver.
   * \endverbatim
   */
  EVALUE(SAT_REFUTATION),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **DRAT Refutation**
   *
   * .. math::
   *
   *   \inferrule{F_1 \dots F_n \mid D, P}{\bot}
   *
   * where :math:`F_1 \dots F_n` correspond to the clauses in the
   * DIMACS file given by filename `D` and `P` is a filename of a file storing
   * a DRAT proof.
   * \endverbatim
   */
  EVALUE(DRAT_REFUTATION),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **SAT external prove Refutation**
   *
   * .. math::
   *
   *   \inferrule{F_1 \dots F_n \mid D}{\bot}
   *
   * where :math:`F_1 \dots F_n` correspond to the input clauses in the
   * DIMACS file `D`.
   * \endverbatim
   */
  EVALUE(SAT_EXTERNAL_PROVE),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- Resolution**
   *
   * .. math::
   *
   *   \inferrule{C_1, C_2 \mid pol, L}{C}
   *
   * where
   *
   * - :math:`C_1` and :math:`C_2` are nodes viewed as clauses, i.e., either an
   *   ``OR`` node with each children viewed as a literal or a node viewed as a
   *   literal. Note that an ``OR`` node could also be a literal.
   * - :math:`pol` is either true or false, representing the polarity of the
   *   pivot on the first clause
   * - :math:`L` is the pivot of the resolution, which occurs as is (resp. under
   *   a ``NOT``) in :math:`C_1` and negatively (as is) in :math:`C_2` if
   *   :math:`pol = \top` (:math:`pol = \bot`).
   *
   * :math:`C` is a clause resulting from collecting all the literals in
   * :math:`C_1`, minus the first occurrence of the pivot or its negation, and
   * :math:`C_2`, minus the first occurrence of the pivot or its negation,
   * according to the policy above. If the resulting clause has a single
   * literal, that literal itself is the result; if it has no literals, then the
   * result is false; otherwise it's an ``OR`` node of the resulting literals.
   *
   * Note that it may be the case that the pivot does not occur in the
   * clauses. In this case the rule is not unsound, but it does not correspond
   * to resolution but rather to a weakening of the clause that did not have a
   * literal eliminated.
   * \endverbatim
   */
  EVALUE(RESOLUTION),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- N-ary Resolution**
   *
   * .. math::
   *
   *   \inferrule{C_1 \dots C_n \mid (pol_1 \dots pol_{n-1}), (L_1 \dots L_{n-1})}{C}
   *
   * where
   *
   * - let :math:`C_1 \dots C_n` be nodes viewed as clauses, as defined above
   * - let :math:`C_1 \diamond_{L,pol} C_2` represent the resolution of
   *   :math:`C_1` with :math:`C_2` with pivot :math:`L` and polarity
   *   :math:`pol`, as defined above
   * - let :math:`C_1' = C_1`,
   * - for each :math:`i > 1`, let :math:`C_i' = C_{i-1} \diamond_{L_{i-1}, pol_{i-1}} C_i'`
   *
   * Note the list of polarities and pivots are provided as s-expressions.
   *
   * The result of the chain resolution is :math:`C = C_n'`
   * \endverbatim
   */
  EVALUE(CHAIN_RESOLUTION),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- Factoring**
   *
   * .. math::
   *
   *   \inferrule{C_1 \mid -}{C_2}
   *
   * where :math:`C_2` is the clause :math:`C_1`, but every occurrence of a literal
   * after its first occurrence is omitted.
   * \endverbatim
   */
  EVALUE(FACTORING),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- Reordering**
   *
   * .. math::
   *
   *   \inferrule{C_1 \mid C_2}{C_2}
   *
   * where
   * the multiset representations of :math:`C_1` and :math:`C_2` are the same.
   * \endverbatim
   */
  EVALUE(REORDERING),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- N-ary Resolution + Factoring + Reordering**
   *
   * .. math::
   *
   *   \inferrule{C_1 \dots C_n \mid C, pol_1,L_1 \dots pol_{n-1},L_{n-1}}{C}
   *
   * where
   *
   * - let :math:`C_1 \dots C_n` be nodes viewed as clauses, as defined in
   *   :cpp:enumerator:`RESOLUTION <cvc5::ProofRule::RESOLUTION>`
   * - let :math:`C_1 \diamond_{L,\mathit{pol}} C_2` represent the resolution of
   *   :math:`C_1` with :math:`C_2` with pivot :math:`L` and polarity
   *   :math:`pol`, as defined in
   *   :cpp:enumerator:`RESOLUTION <cvc5::ProofRule::RESOLUTION>`
   * - let :math:`C_1'` be equal, in its set representation, to :math:`C_1`,
   * - for each :math:`i > 1`, let :math:`C_i'` be equal, in its set
   *   representation, to :math:`C_{i-1} \diamond_{L_{i-1},\mathit{pol}_{i-1}}
   *   C_i'`
   *
   * The result of the chain resolution is :math:`C`, which is equal, in its set
   * representation, to :math:`C_n'`
   * \endverbatim
   */
  EVALUE(MACRO_RESOLUTION),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- N-ary Resolution + Factoring + Reordering unchecked**
   *
   * Same as
   * :cpp:enumerator:`MACRO_RESOLUTION <cvc5::ProofRule::MACRO_RESOLUTION>`, but
   * not checked by the internal proof checker.
   * \endverbatim
   */
  EVALUE(MACRO_RESOLUTION_TRUST),

  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- Split**
   *
   * .. math::
   *
   *   \inferrule{- \mid F}{F \lor \neg F}
   *
   * \endverbatim
   */
  EVALUE(SPLIT),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- Equality resolution**
   *
   * .. math::
   *
   *   \inferrule{F_1, (F_1 = F_2) \mid -}{F_2}
   *
   * Note this can optionally be seen as a macro for
   * :cpp:enumerator:`EQUIV_ELIM1 <cvc5::ProofRule::EQUIV_ELIM1>` +
   * :cpp:enumerator:`RESOLUTION <cvc5::ProofRule::RESOLUTION>`.
   * \endverbatim
   */
  EVALUE(EQ_RESOLVE),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- Modus Ponens**
   *
   * .. math::
   *
   *   \inferrule{F_1, (F_1 \rightarrow F_2) \mid -}{F_2}
   *
   * Note this can optionally be seen as a macro for
   * :cpp:enumerator:`IMPLIES_ELIM <cvc5::ProofRule::IMPLIES_ELIM>` +
   * :cpp:enumerator:`RESOLUTION <cvc5::ProofRule::RESOLUTION>`.
   * \endverbatim
   */
  EVALUE(MODUS_PONENS),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- Double negation elimination**
   *
   * .. math::
   *
   *   \inferrule{\neg (\neg F) \mid -}{F}
   *
   * \endverbatim
   */
  EVALUE(NOT_NOT_ELIM),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- Contradiction**
   *
   * .. math::
   *
   *   \inferrule{F, \neg F \mid -}{\bot}
   *
   * \endverbatim
   */
  EVALUE(CONTRA),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- And elimination**
   *
   * .. math::
   *
   *   \inferrule{(F_1 \land \dots \land F_n) \mid i}{F_i}
   *
   * \endverbatim
   */
  EVALUE(AND_ELIM),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- And introduction**
   *
   * .. math::
   *
   *   \inferrule{F_1 \dots F_n \mid -}{(F_1 \land \dots \land F_n)}
   *
   * \endverbatim
   */
  EVALUE(AND_INTRO),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- Not Or elimination**
   *
   * .. math::
   *
   *   \inferrule{\neg(F_1 \lor \dots \lor F_n) \mid i}{\neg F_i}
   *
   * \endverbatim
   */
  EVALUE(NOT_OR_ELIM),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- Implication elimination**
   *
   * .. math::
   *
   *   \inferrule{F_1 \rightarrow F_2 \mid -}{\neg F_1 \lor F_2}
   *
   * \endverbatim
   */
  EVALUE(IMPLIES_ELIM),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- Not Implication elimination version 1**
   *
   * .. math::
   *
   *   \inferrule{\neg(F_1 \rightarrow F_2) \mid -}{F_1}
   *
   * \endverbatim
   */
  EVALUE(NOT_IMPLIES_ELIM1),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- Not Implication elimination version 2**
   *
   * .. math::
   *
   *   \inferrule{\neg(F_1 \rightarrow F_2) \mid -}{\neg F_2}
   *
   * \endverbatim
   */
  EVALUE(NOT_IMPLIES_ELIM2),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- Equivalence elimination version 1**
   *
   * .. math::
   *
   *   \inferrule{F_1 = F_2 \mid -}{\neg F_1 \lor F_2}
   *
   * \endverbatim
   */
  EVALUE(EQUIV_ELIM1),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- Equivalence elimination version 2**
   *
   * .. math::
   *
   *   \inferrule{F_1 = F_2 \mid -}{F_1 \lor \neg F_2}
   *
   * \endverbatim
   */
  EVALUE(EQUIV_ELIM2),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- Not Equivalence elimination version 1**
   *
   * .. math::
   *
   *   \inferrule{F_1 \neq F_2 \mid -}{F_1 \lor F_2}
   *
   * \endverbatim
   */
  EVALUE(NOT_EQUIV_ELIM1),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- Not Equivalence elimination version 2**
   *
   * .. math::
   *
   *   \inferrule{F_1 \neq F_2 \mid -}{\neg F_1 \lor \neg F_2}
   *
   * \endverbatim
   */
  EVALUE(NOT_EQUIV_ELIM2),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- XOR elimination version 1**
   *
   * .. math::
   *
   *   \inferrule{F_1 \xor F_2 \mid -}{F_1 \lor F_2}
   *
   * \endverbatim
   */
  EVALUE(XOR_ELIM1),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- XOR elimination version 2**
   *
   * .. math::
   *
   *   \inferrule{F_1 \xor F_2 \mid -}{\neg F_1 \lor \neg F_2}
   *
   * \endverbatim
   */
  EVALUE(XOR_ELIM2),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- Not XOR elimination version 1**
   *
   * .. math::
   *
   *   \inferrule{\neg(F_1 \xor F_2) \mid -}{F_1 \lor \neg F_2}
   *
   * \endverbatim
   */
  EVALUE(NOT_XOR_ELIM1),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- Not XOR elimination version 2**
   *
   * .. math::
   *
   *   \inferrule{\neg(F_1 \xor F_2) \mid -}{\neg F_1 \lor F_2}
   *
   * \endverbatim
   */
  EVALUE(NOT_XOR_ELIM2),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- ITE elimination version 1**
   *
   * .. math::
   *
   *   \inferrule{(\ite{C}{F_1}{F_2}) \mid -}{\neg C \lor F_1}
   *
   * \endverbatim
   */
  EVALUE(ITE_ELIM1),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- ITE elimination version 2**
   *
   * .. math::
   *
   *   \inferrule{(\ite{C}{F_1}{F_2}) \mid -}{C \lor F_2}
   *
   * \endverbatim
   */
  EVALUE(ITE_ELIM2),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- Not ITE elimination version 1**
   *
   * .. math::
   *
   *   \inferrule{\neg(\ite{C}{F_1}{F_2}) \mid -}{\neg C \lor \neg F_1}
   *
   * \endverbatim
   */
  EVALUE(NOT_ITE_ELIM1),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- Not ITE elimination version 2**
   *
   * .. math::
   *
   *   \inferrule{\neg(\ite{C}{F_1}{F_2}) \mid -}{C \lor \neg F_2}
   *
   * \endverbatim
   */
  EVALUE(NOT_ITE_ELIM2),

  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- De Morgan -- Not And**
   *
   * .. math::
   *
   *   \inferrule{\neg(F_1 \land \dots \land F_n) \mid -}{\neg F_1 \lor \dots
   *   \lor \neg F_n}
   *
   * \endverbatim
   */
  EVALUE(NOT_AND),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- CNF -- And Positive**
   *
   * .. math::
   *
   *   \inferrule{- \mid (F_1 \land \dots \land F_n), i}{\neg (F_1 \land \dots
   *   \land F_n) \lor F_i}
   *
   * \endverbatim
   */
  EVALUE(CNF_AND_POS),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- CNF -- And Negative**
   *
   * .. math::
   *
   *   \inferrule{- \mid (F_1 \land \dots \land F_n)}{(F_1 \land \dots \land
   *   F_n) \lor \neg F_1 \lor \dots \lor \neg F_n}
   *
   * \endverbatim
   */
  EVALUE(CNF_AND_NEG),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- CNF -- Or Positive**
   *
   * .. math::
   *
   *   \inferrule{- \mid (F_1 \lor \dots \lor F_n)}{\neg(F_1 \lor \dots \lor
   *   F_n) \lor F_1 \lor \dots \lor F_n}
   *
   * \endverbatim
   */
  EVALUE(CNF_OR_POS),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- CNF -- Or Negative**
   *
   * .. math::
   *
   *   \inferrule{- \mid (F_1 \lor \dots \lor F_n), i}{(F_1 \lor \dots \lor F_n)
   *   \lor \neg F_i}
   *
   * \endverbatim
   */
  EVALUE(CNF_OR_NEG),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- CNF -- Implies Positive**
   *
   * .. math::
   *
   *   \inferrule{- \mid F_1 \rightarrow F_2}{\neg(F_1 \rightarrow F_2) \lor \neg F_1
   *   \lor F_2}
   *
   * \endverbatim
   */
  EVALUE(CNF_IMPLIES_POS),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- CNF -- Implies Negative 1**
   *
   * .. math::
   *
   *   \inferrule{- \mid F_1 \rightarrow F_2}{(F_1 \rightarrow F_2) \lor F_1}
   *
   * \endverbatim
   */
  EVALUE(CNF_IMPLIES_NEG1),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- CNF -- Implies Negative 2**
   *
   * .. math::
   *
   *   \inferrule{- \mid F_1 \rightarrow F_2}{(F_1 \rightarrow F_2) \lor \neg F_2}
   *
   * \endverbatim
   */
  EVALUE(CNF_IMPLIES_NEG2),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- CNF -- Equiv Positive 1**
   *
   * .. math::
   *
   *   \inferrule{- \mid F_1 = F_2}{F_1 \neq F_2 \lor \neg F_1 \lor F_2}
   *
   * \endverbatim
   */
  EVALUE(CNF_EQUIV_POS1),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- CNF -- Equiv Positive 2**
   *
   * .. math::
   *
   *   \inferrule{- \mid F_1 = F_2}{F_1 \neq F_2 \lor F_1 \lor \neg F_2}
   *
   * \endverbatim
   */
  EVALUE(CNF_EQUIV_POS2),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- CNF -- Equiv Negative 1**
   *
   * .. math::
   *
   *   \inferrule{- \mid F_1 = F_2}{(F_1 = F_2) \lor F_1 \lor F_2}
   *
   * \endverbatim
   */
  EVALUE(CNF_EQUIV_NEG1),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- CNF -- Equiv Negative 2**
   *
   * .. math::
   *
   *   \inferrule{- \mid F_1 = F_2}{(F_1 = F_2) \lor \neg F_1 \lor \neg F_2}
   *
   * \endverbatim
   */
  EVALUE(CNF_EQUIV_NEG2),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- CNF -- XOR Positive 1**
   *
   * .. math::
   *
   *   \inferrule{- \mid F_1 \xor F_2}{\neg(F_1 \xor F_2) \lor F_1 \lor F_2}
   *
   * \endverbatim
   */
  EVALUE(CNF_XOR_POS1),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- CNF -- XOR Positive 2**
   *
   * .. math::
   *
   *   \inferrule{- \mid F_1 \xor F_2}{\neg(F_1 \xor F_2) \lor \neg F_1 \lor
   *   \neg F_2}
   *
   * \endverbatim
   */
  EVALUE(CNF_XOR_POS2),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- CNF -- XOR Negative 1**
   *
   * .. math::
   *
   *   \inferrule{- \mid F_1 \xor F_2}{(F_1 \xor F_2) \lor \neg F_1 \lor F_2}
   *
   * \endverbatim
   */
  EVALUE(CNF_XOR_NEG1),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- CNF -- XOR Negative 2**
   *
   * .. math::
   *
   *   \inferrule{- \mid F_1 \xor F_2}{(F_1 \xor F_2) \lor F_1 \lor \neg F_2}
   *
   * \endverbatim
   */
  EVALUE(CNF_XOR_NEG2),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- CNF -- ITE Positive 1**
   *
   * .. math::
   *
   *   \inferrule{- \mid (\ite{C}{F_1}{F_2})}{\neg(\ite{C}{F_1}{F_2}) \lor \neg
   *   C \lor F_1}
   *
   * \endverbatim
   */
  EVALUE(CNF_ITE_POS1),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- CNF -- ITE Positive 2**
   *
   * .. math::
   *
   *   \inferrule{- \mid (\ite{C}{F_1}{F_2})}{\neg(\ite{C}{F_1}{F_2}) \lor C
   *   \lor F_2}
   *
   * \endverbatim
   */
  EVALUE(CNF_ITE_POS2),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- CNF -- ITE Positive 3**
   *
   * .. math::
   *
   *   \inferrule{- \mid (\ite{C}{F_1}{F_2})}{\neg(\ite{C}{F_1}{F_2}) \lor F_1
   *   \lor F_2}
   *
   * \endverbatim
   */
  EVALUE(CNF_ITE_POS3),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- CNF -- ITE Negative 1**
   *
   * .. math::
   *
   *   \inferrule{- \mid (\ite{C}{F_1}{F_2})}{(\ite{C}{F_1}{F_2}) \lor \neg C
   *   \lor \neg F_1}
   *
   * \endverbatim
   */
  EVALUE(CNF_ITE_NEG1),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- CNF -- ITE Negative 2**
   *
   * .. math::
   *
   *   \inferrule{- \mid (\ite{C}{F_1}{F_2})}{(\ite{C}{F_1}{F_2}) \lor C \lor
   *   \neg F_2}
   *
   * \endverbatim
   */
  EVALUE(CNF_ITE_NEG2),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Boolean -- CNF -- ITE Negative 3**
   *
   * .. math::
   *
   *   \inferrule{- \mid (\ite{C}{F_1}{F_2})}{(\ite{C}{F_1}{F_2}) \lor \neg F_1
   *   \lor \neg F_2}
   *
   * \endverbatim
   */
  EVALUE(CNF_ITE_NEG3),

  /**
   * \verbatim embed:rst:leading-asterisk
   * **Equality -- Reflexivity**
   *
   * .. math::
   *
   *   \inferrule{-\mid t}{t = t}
   * \endverbatim
   */
  EVALUE(REFL),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Equality -- Symmetry**
   *
   * .. math::
   *
   *   \inferrule{t_1 = t_2\mid -}{t_2 = t_1}
   *
   * or
   *
   * .. math::
   *
   *   \inferrule{t_1 \neq t_2\mid -}{t_2 \neq t_1}
   *
   * \endverbatim
   */
  EVALUE(SYMM),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Equality -- Transitivity**
   *
   * .. math::
   *
   *   \inferrule{t_1=t_2,\dots,t_{n-1}=t_n\mid -}{t_1 = t_n}
   * \endverbatim
   */
  EVALUE(TRANS),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Equality -- Congruence**
   *
   * .. math::
   *
   *   \inferrule{t_1=s_1,\dots,t_n=s_n\mid f(t_1,\dots, t_n)}{f(t_1,\dots, t_n) = f(s_1,\dots, s_n)}
   *
   * This rule is used when the kind of :math:`f(t_1,\dots, t_n)` has a fixed
   * arity. This includes kinds such as ``cvc5::Kind::ITE``,
   * ``cvc5::Kind::EQUAL``, as well as indexed functions such as
   * ``cvc5::Kind::BITVECTOR_EXTRACT``.
   *
   * It is also used for ``cvc5::Kind::APPLY_UF``, where :math:`f` is an
   * uninterpreted function.
   *
   * It is not used for kinds with variadic arity, or for kind
   * ``cvc5::Kind::HO_APPLY``, which respectively use the rules
   * :cpp:enumerator:`NARY_CONG <cvc5::ProofRule::NARY_CONG>` and
   * :cpp:enumerator:`HO_CONG <cvc5::ProofRule::HO_CONG>` below.
   * \endverbatim
   */
  EVALUE(CONG),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Equality -- N-ary Congruence**
   *
   * .. math::
   *
   *   \inferrule{t_1=s_1,\dots,t_n=s_n\mid f(t_1,\dots, t_n)}{f(t_1,\dots, t_n) = f(s_1,\dots, s_n)}
   *
   * This rule is used for terms :math:`f(t_1,\dots, t_n)` whose kinds
   * :math:`k` have variadic arity, such as ``cvc5::Kind::AND``,
   * ``cvc5::Kind::PLUS`` and so on.
   * \endverbatim
   */
  EVALUE(NARY_CONG),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Equality -- True intro**
   *
   * .. math::
   *
   *   \inferrule{F\mid -}{F = \top}
   * \endverbatim
   */
  EVALUE(TRUE_INTRO),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Equality -- True elim**
   *
   * .. math::
   *
   *   \inferrule{F=\top\mid -}{F}
   * \endverbatim
   */
  EVALUE(TRUE_ELIM),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Equality -- False intro**
   *
   * .. math::
   *
   *   \inferrule{\neg F\mid -}{F = \bot}
   * \endverbatim
   */
  EVALUE(FALSE_INTRO),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Equality -- False elim**
   *
   * .. math::
   *
   *   \inferrule{F=\bot\mid -}{\neg F}
   * \endverbatim
   */
  EVALUE(FALSE_ELIM),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Equality -- Higher-order application encoding**
   *
   * .. math::
   *
   *   \inferrule{-\mid t}{t=t'}
   *
   * where `t'` is the higher-order application that is equivalent to `t`,
   * as implemented by ``uf::TheoryUfRewriter::getHoApplyForApplyUf``.
   * For details see :cvc5src:`theory/uf/theory_uf_rewriter.h`
   *
   * For example, this rule concludes :math:`f(x,y) = @( @(f,x), y)`, where
   * :math:`@` is the ``HO_APPLY`` kind.
   *
   * Note this rule can be treated as a
   * :cpp:enumerator:`REFL <cvc5::ProofRule::REFL>` when appropriate in
   * external proof formats.
   * \endverbatim
   */
  EVALUE(HO_APP_ENCODE),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Equality -- Higher-order congruence**
   *
   * .. math::
   *
   *   \inferrule{f=g, t_1=s_1,\dots,t_n=s_n\mid k}{k(f, t_1,\dots, t_n) =
   *   k(g, s_1,\dots, s_n)}
   *
   * Notice that this rule is only used when the application kind :math:`k` is
   * either `cvc5::Kind::APPLY_UF` or `cvc5::Kind::HO_APPLY`.
   * \endverbatim
   */
  EVALUE(HO_CONG),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arrays -- Read over write**
   *
   * .. math::
   *
   *   \inferrule{i_1 \neq i_2\mid \mathit{select}(\mathit{store}(a,i_1,e),i_2)}
   *   {\mathit{select}(\mathit{store}(a,i_1,e),i_2) = \mathit{select}(a,i_2)}
   * \endverbatim
   */
  EVALUE(ARRAYS_READ_OVER_WRITE),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arrays -- Read over write, contrapositive**
   *
   * .. math::
   *
   *   \inferrule{\mathit{select}(\mathit{store}(a,i_2,e),i_1) \neq
   *   \mathit{select}(a,i_1)\mid -}{i_1=i_2}
   * \endverbatim
   */
  EVALUE(ARRAYS_READ_OVER_WRITE_CONTRA),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arrays -- Read over write 1**
   *
   * .. math::
   *
   *   \inferrule{-\mid \mathit{select}(\mathit{store}(a,i,e),i)}
   *   {\mathit{select}(\mathit{store}(a,i,e),i)=e}
   * \endverbatim
   */
  EVALUE(ARRAYS_READ_OVER_WRITE_1),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arrays -- Arrays extensionality**
   *
   * .. math::
   *
   *   \inferrule{a \neq b\mid -}
   *   {\mathit{select}(a,k)\neq\mathit{select}(b,k)}
   *
   * where :math:`k` is the :math:`\texttt{ARRAY_DEQ_DIFF}` skolem for `(a, b)`.
   * \endverbatim
   */
  EVALUE(ARRAYS_EXT),

  /**
   * \verbatim embed:rst:leading-asterisk
   * **Bit-vectors -- (Macro) Bitblast**
   *
   * .. math::
   *
   *   \inferrule{-\mid t}{t = \texttt{bitblast}(t)}
   *
   * where :math:`\texttt{bitblast}` represents the result of the bit-blasted term as
   * a bit-vector consisting of the output bits of the bit-blasted circuit
   * representation of the term. Terms are bit-blasted according to the
   * strategies defined in :cvc5src:`theory/bv/bitblast/bitblast_strategies_template.h`.
   * \endverbatim
   */
  EVALUE(MACRO_BV_BITBLAST),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Bit-vectors -- Bitblast bit-vector constant, variable, and terms**
   *
   * For constant and variables:
   *
   * .. math::
   *
   *   \inferrule{-\mid t}{t = \texttt{bitblast}(t)}
   *
   * For terms:
   *
   * .. math::
   *
   *   \inferrule{-\mid k(\texttt{bitblast}(t_1),\dots,\texttt{bitblast}(t_n))}
   *   {k(\texttt{bitblast}(t_1),\dots,\texttt{bitblast}(t_n)) =
   *   \texttt{bitblast}(t)}
   *
   * where :math:`t` is :math:`k(t_1,\dots,t_n)`.
   * \endverbatim
   */
  EVALUE(BV_BITBLAST_STEP),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Bit-vectors -- Bit-vector eager atom**
   *
   * .. math::
   *
   *   \inferrule{-\mid F}{F = F[0]}
   *
   * where :math:`F` is of kind ``BITVECTOR_EAGER_ATOM``.
   * \endverbatim
   */
  EVALUE(BV_EAGER_ATOM),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Bit-vectors -- Polynomial normalization**
   *
   * .. math::
   *
   *   \inferrule{- \mid t = s}{t = s}
   *
   * where :math:`\texttt{arith::PolyNorm::isArithPolyNorm(t, s)} = \top`. This
   * method normalizes polynomials :math:`s` and :math:`t` over bitvectors.
   * \endverbatim
   */
  EVALUE(BV_POLY_NORM),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Bit-vectors -- Polynomial normalization for relations**
   *
   * .. math::
   *
   *  \inferrule{c_x \cdot (x_1 - x_2) = c_y \cdot (y_1 - y_2) \mid (x_1 = x_2) = (y_1 = y_2)}
   *            {(x_1 = x_2) = (y_1 = y_2)}
   *
   * :math:`c_x` and :math:`c_y` are scaling factors, currently required to
   * be one.
   * \endverbatim
   */
  EVALUE(BV_POLY_NORM_EQ),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Datatypes -- Split**
   *
   * .. math::
   *
   *   \inferrule{-\mid t}{\mathit{is}_{C_1}(t)\vee\cdots\vee\mathit{is}_{C_n}(t)}
   *
   * where :math:`C_1,\dots,C_n` are all the constructors of the type of :math:`t`.
   * \endverbatim
   */
  EVALUE(DT_SPLIT),

  /**
   * \verbatim embed:rst:leading-asterisk
   * **Quantifiers -- Skolem introduction**
   *
   * .. math::
   *
   *   \inferrule{-\mid k}{k = t}
   *
   * where :math:`t` is the unpurified form of skolem :math:`k`.
   * \endverbatim
   */
  EVALUE(SKOLEM_INTRO),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Quantifiers -- Skolemization**
   *
   * .. math::
   *
   *   \inferrule{\neg (\forall x_1\dots x_n.\> F)\mid -}{\neg F\sigma}
   *
   * where :math:`\sigma` maps :math:`x_1,\dots,x_n` to their representative
   * skolems, which are skolems :math:`k_1,\dots,k_n`. For each :math:`k_i`,
   * its skolem identifier is
   * :cpp:enumerator:`QUANTIFIERS_SKOLEMIZE <cvc5::SkolemId::QUANTIFIERS_SKOLEMIZE>`,
   * and its indices are :math:`(\forall x_1\dots x_n.\> F)` and :math:`x_i`.
   * \endverbatim
   */
  EVALUE(SKOLEMIZE),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Quantifiers -- Instantiation**
   *
   * .. math::
   *
   *   \inferrule{\forall x_1\dots x_n.\> F\mid (t_1 \dots t_n), (id\, (t)?)?}
   *   {F\{x_1\mapsto t_1,\dots,x_n\mapsto t_n\}}
   *
   * The list of terms to instantiate :math:`(t_1 \dots t_n)` is provided as
   * an s-expression as the first argument. The optional argument :math:`id`
   * indicates the inference id that caused the instantiation. The term
   * :math:`t` indicates an additional term (e.g. the trigger) associated with
   * the instantiation, which depends on the id. If the id has prefix
   * ``QUANTIFIERS_INST_E_MATCHING``, then :math:`t` is the trigger that
   * generated the instantiation.
   * \endverbatim
   */
  EVALUE(INSTANTIATE),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Quantifiers -- Alpha equivalence**
   *
   * .. math::
   *
   *   \inferruleSC{-\mid F, (y_1 \ldots y_n), (z_1,\dots, z_n)}
   *   {F = F\{y_1\mapsto z_1,\dots,y_n\mapsto z_n\}}
   *   {if $y_1,\dots,y_n, z_1,\dots,z_n$ are unique bound variables}
   *
   * Notice that this rule is correct only when :math:`z_1,\dots,z_n` are not
   * contained in :math:`FV(F) \setminus \{ y_1,\dots, y_n \}`, where
   * :math:`FV(F)` are the free variables of :math:`F`. The internal
   * quantifiers proof checker does not currently check that this is the case.
   * \endverbatim
   */
  EVALUE(ALPHA_EQUIV),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Quantifiers -- Variable reordering**
   *
   * .. math::
   *
   *   \inferrule{-\mid (\forall X.\> F) = (\forall Y.\> F)}
   *   {(\forall X.\> F) = (\forall Y.\> F)}
   *
   * where :math:`Y` is a reordering of :math:`X`.
   *
   * \endverbatim
   */
  EVALUE(QUANT_VAR_REORDERING),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Quantifiers -- Exists string length**
   *
   * .. math::
   *
   *   \inferrule{-\mid T n i} {\mathit{len}(k) = n}
   *
   * where :math:`k` is a skolem of string or sequence type :math:`T` and
   * :math:`n` is a non-negative integer. The argument :math:`i` is an
   * identifier for :math:`k`. These three arguments are the indices of
   * :math:`k`, whose skolem identifier is
   * :cpp:enumerator:`WITNESS_STRING_LENGTH <cvc5::SkolemId::WITNESS_STRING_LENGTH>`.
   *
   * \endverbatim
   */
  EVALUE(EXISTS_STRING_LENGTH),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Sets -- Singleton injectivity**
   *
   * .. math::
   *
   *   \inferrule{\mathit{set.singleton}(t) = \mathit{set.singleton}(s)\mid -}{t=s}
   * \endverbatim
   */
  EVALUE(SETS_SINGLETON_INJ),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Sets -- Sets extensionality**
   *
   * .. math::
   *
   *   \inferrule{a \neq b\mid -}
   *   {\mathit{set.member}(k,a)\neq\mathit{set.member}(k,b)}
   *
   * where :math:`k` is the :math:`\texttt{SETS_DEQ_DIFF}` skolem for `(a, b)`.
   * \endverbatim
   */
  EVALUE(SETS_EXT),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Sets -- Sets filter up**
   *
   * .. math::
   *
   *   \inferrule{\mathit{set.member}(x,a)\mid P}
   *   {\mathit{set.member}(x, \mathit{set.filter}(P, a)) = P(x)}
   *
   * \endverbatim
   */
  EVALUE(SETS_FILTER_UP),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Sets -- Sets filter down**
   *
   * .. math::
   *
   *   \inferrule{\mathit{set.member}(x,\mathit{set.filter}(P, a))\mid -}
   *   {\mathit{set.member}(x,a) \wedge P(x)}
   * \endverbatim
   */
  EVALUE(SETS_FILTER_DOWN),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- Core rules -- Concatenation equality**
   *
   * .. math::
   *
   *   \inferrule{(t_1 \cdot \ldots \cdot t_n \cdot t) = (t_1 \cdot \ldots \cdot t_n \cdot s)\mid \bot}{t = s}
   *
   * Alternatively for the reverse:
   *
   *   \inferrule{(t \cdot t_1 \cdot \ldots \cdot t_n) = (s \cdot t_1 \cdot \ldots \cdot t_n)\mid \top}{t = s}
   *
   * Notice that :math:`t` or :math:`s` may be empty, in which case they are
   * implicit in the concatenation above. For example, if the premise is
   * :math:`x\cdot z = x`, then this rule, with argument :math:`\bot`, concludes
   * :math:`z = \epsilon`.
   * \endverbatim
   */
  EVALUE(CONCAT_EQ),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- Core rules -- Concatenation unification**
   *
   * .. math::
   *
   *   \inferrule{(t_1 \cdot \ldots \cdot t_n) = (s_1 \cdot \ldots \cdot s_m),\, \mathit{len}(t_1) =
   *   \mathit{len}(s_1)\mid \bot}{t_1 = s_1}
   *
   * Alternatively for the reverse:
   *
   * .. math::
   *
   *   \inferrule{(t_1 \cdot \ldots \cdot t_n) = (s_1 \cdot \ldots \cdot s_m),\, \mathit{len}(t_n) =
   *   \mathit{len}(s_m)\mid \top}{t_n = s_m}
   *
   * \endverbatim
   */
  EVALUE(CONCAT_UNIFY),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- Core rules -- Concatenation split**
   *
   * .. math::
   *
   *   \inferruleSC{(t_1 \cdot \ldots \cdot t_n) = (s_1 \cdot \ldots \cdot s_m),\,
   *   \mathit{len}(t_1) \neq \mathit{len}(s_1)\mid \bot}{((t_1 = s_1\cdot r)
   *   \vee (s_1 = t_1\cdot r)) \wedge r \neq \epsilon \wedge \mathit{len}(r)>0}
   *
   * where :math:`r` is the purification skolem for
   * :math:`\mathit{ite}(
   * \mathit{len}(t_1) >= \mathit{len}(s_1),
   * \mathit{suf}(t_1,\mathit{len}(s_1)),
   * \mathit{suf}(s_1,\mathit{len}(t_1)))`
   * and :math:`\epsilon` is the empty string (or sequence).
   *
   * .. math::
   *
   *   \inferruleSC{(t_1 \cdot \ldots \cdot t_n) = (s_1 \cdot \ldots \cdot s_m),\,
   *   \mathit{len}(t_n) \neq \mathit{len}(s_m)\mid \top}{((t_n = r \cdot s_m)
   *   \vee (s_m = r \cdot t_n)) \wedge r \neq \epsilon \wedge \mathit{len}(r)>0}
   *
   * where :math:`r` is the purification Skolem for
   * :math:`\mathit{ite}(
   * \mathit{len}(t_n) >= \mathit{len}(s_m),
   * \mathit{pre}(t_n,\mathit{len}(t_n) - \mathit{len}(s_m)),
   * \mathit{pre}(s_m,\mathit{len}(s_m) - \mathit{len}(t_n)))`
   * and :math:`\epsilon` is the empty string (or sequence).
   *
   * Above, :math:`\mathit{suf}(x,y)` is shorthand for
   * :math:`\mathit{substr}(x,y, \mathit{len}(x) - y)` and
   * :math:`\mathit{pre}(x,y)` is shorthand for :math:`\mathit{substr}(x,0,y)`.
   * \endverbatim
   */
  EVALUE(CONCAT_SPLIT),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- Core rules -- Concatenation split for constants**
   *
   * .. math::
   *
   *   \inferrule{(t_1\cdot \ldots \cdot t_n) = (c \cdot t_2 \ldots \cdot s_m),\,\mathit{len}(t_1) \neq 0\mid \bot}{(t_1 = c\cdot r)}
   *
   * where :math:`r` is the purification skolem for :math:`\mathit{suf}(t_1,1)`.
   *
   * Alternatively for the reverse:
   *
   * .. math::
   *
   *   \inferrule{(t_1\cdot \ldots \cdot t_n) = (s_1 \cdot \ldots s_{m-1} \cdot c),\,\mathit{len}(t_n) \neq 0\mid \top}{(t_n = r\cdot c)}
   *
   * where :math:`r` is the purification skolem for
   * :math:`\mathit{pre}(t_n,\mathit{len}(t_n) - 1)`.
   * \endverbatim
   */
  EVALUE(CONCAT_CSPLIT),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- Core rules -- Concatenation length propagation**
   *
   * .. math::
   *
   *   \inferrule{(t_1\cdot \ldots \cdot t_n) = (s_1 \cdot \ldots \cdot s_m),\,
   *   \mathit{len}(t_1) > \mathit{len}(s_1)\mid \bot}{(t_1 = s_1\cdot r)}
   *
   * where :math:`r` is the purification Skolem for
   * :math:`\mathit{ite}(
   * \mathit{len}(t_1) >= \mathit{len}(s_1),
   * \mathit{suf}(t_1,\mathit{len}(s_1)),
   * \mathit{suf}(s_1,\mathit{len}(t_1)))`.
   *
   * Alternatively for the reverse:
   *
   * .. math::
   *
   *   \inferrule{(t_1\cdot \ldots \cdot t_n) = (s_1 \cdot \ldots \cdot s_m)),\,
   *   \mathit{len}(t_n) > \mathit{len}(s_m)\mid \top}{(t_n = r \cdot s_m)}
   *
   * where :math:`r` is the purification Skolem for
   * :math:`\mathit{ite}(
   * \mathit{len}(t_n) >= \mathit{len}(s_m),
   * \mathit{pre}(t_n,\mathit{len}(t_n) - \mathit{len}(s_m)),
   * \mathit{pre}(s_m,\mathit{len}(s_m) - \mathit{len}(t_n)))`
   * \endverbatim
   */
  EVALUE(CONCAT_LPROP),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- Core rules -- Concatenation constant propagation**
   *
   * .. math::
   *
   *   \inferrule{(t_1 \cdot w_1 \cdot \ldots \cdot t_n) = (w_2 \cdot s_2 \cdot \ldots \cdot s_m),\,
   *   \mathit{len}(t_1) \neq 0\mid \bot}{(t_1 = t_3\cdot r)}
   *
   * where :math:`w_1,\,w_2` are words, :math:`t_3` is
   * :math:`\mathit{pre}(w_2,p)`, :math:`p` is
   * :math:`\texttt{Word::overlap}(\mathit{suf}(w_2,1), w_1)`, and :math:`r` is
   * the purification skolem for
   * :math:`\mathit{suf}(t_1,\mathit{len}(w_3))`.  Note that
   * :math:`\mathit{suf}(w_2,p)` is the largest suffix of
   * :math:`\mathit{suf}(w_2,1)` that can contain a prefix of :math:`w_1`; since
   * :math:`t_1` is non-empty, :math:`w_3` must therefore be contained in
   * :math:`t_1`.
   *
   * Alternatively for the reverse:
   *
   * .. math::
   *
   *   \inferrule{(t_1 \cdot \ldots \cdot w_1 \cdot t_n) = (s_1 \cdot \ldots \cdot w_2),\,
   *   \mathit{len}(t_n) \neq 0\mid \top}{(t_n = r\cdot t_3)}
   *
   * where :math:`w_1,\,w_2` are words, :math:`t_3` is
   * :math:`\mathit{substr}(w_2, \mathit{len}(w_2) - p, p)`, :math:`p` is
   * :math:`\texttt{Word::roverlap}(\mathit{pre}(w_2, \mathit{len}(w_2) - 1),
   * w_1)`, and :math:`r` is the purification skolem for
   * :math:`\mathit{pre}(t_n,\mathit{len}(t_n) - \mathit{len}(w_3))`.  Note that
   * :math:`\mathit{pre}(w_2, \mathit{len}(w_2) - p)` is the largest prefix of
   * :math:`\mathit{pre}(w_2, \mathit{len}(w_2) - 1)` that can contain a suffix
   * of :math:`w_1`; since :math:`t_n` is non-empty, :math:`w_3` must therefore
   * be contained in :math:`t_n`.
   * \endverbatim
   */
  EVALUE(CONCAT_CPROP),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- Core rules -- String decomposition**
   *
   * .. math::
   *
   *   \inferrule{\mathit{len}(t) \geq n\mid \bot}{t = w_1\cdot w_2 \wedge
   *   \mathit{len}(w_1) = n}
   *
   * where :math:`w_1` is the purification skolem for :math:`\mathit{pre}(t,n)`
   * and :math:`w_2` is the purification skolem for :math:`\mathit{suf}(t,n)`.
   * Or alternatively for the reverse:
   *
   * .. math::
   *
   *   \inferrule{\mathit{len}(t) \geq n\mid \top}{t = w_1\cdot w_2 \wedge
   *   \mathit{len}(w_2) = n}
   *
   * where :math:`w_1` is the purification skolem for :math:`\mathit{pre}(t,n)` and
   * :math:`w_2` is the purification skolem for :math:`\mathit{suf}(t,n)`.
   * \endverbatim
   */
  EVALUE(STRING_DECOMPOSE),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- Core rules -- Length positive**
   *
   * .. math::
   *
   *   \inferrule{-\mid t}{(\mathit{len}(t) = 0\wedge t= \epsilon)\vee \mathit{len}(t)
   *   > 0}
   * \endverbatim
   */
  EVALUE(STRING_LENGTH_POS),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- Core rules -- Length non-empty**
   *
   * .. math::
   *
   *   \inferrule{t\neq \epsilon\mid -}{\mathit{len}(t) \neq 0}
   * \endverbatim
   */
  EVALUE(STRING_LENGTH_NON_EMPTY),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- Extended functions -- Reduction**
   *
   * .. math::
   *
   *   \inferrule{-\mid t}{R\wedge t = w}
   *
   * where :math:`w` is :math:`\texttt{StringsPreprocess::reduce}(t, R,
   * \dots)`. For details, see
   * :cvc5src:`theory/strings/theory_strings_preprocess.h`.
   * In other words, :math:`R` is the reduction predicate for extended
   * term :math:`t`, and :math:`w` is the purification skolem for :math:`t`.
   *
   * Notice that the free variables of :math:`R` are :math:`w` and the free
   * variables of :math:`t`.
   * \endverbatim
   */
  EVALUE(STRING_REDUCTION),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- Extended functions -- Eager reduction**
   *
   * .. math::
   *
   *   \inferrule{-\mid t}{R}
   *
   * where :math:`R` is :math:`\texttt{TermRegistry::eagerReduce}(t)`.
   * For details, see :cvc5src:`theory/strings/term_registry.h`.
   * \endverbatim
   */
  EVALUE(STRING_EAGER_REDUCTION),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- Regular expressions -- Intersection**
   *
   * .. math::
   *
   *   \inferrule{t\in R_1,\,t\in R_2\mid -}{t\in \mathit{re.inter}(R_1,R_2)}
   * \endverbatim
   */
  EVALUE(RE_INTER),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- Regular expressions -- Concatenation**
   *
   * .. math::
   *
   *   \inferrule{t_1\in R_1,\,\ldots,\,t_n\in R_n\mid -}{\text{str.++}(t_1, \ldots, t_n)\in \text{re.++}(R_1, \ldots, R_n)}
   * \endverbatim
   */
  EVALUE(RE_CONCAT),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- Regular expressions -- Positive Unfold**
   *
   * .. math::
   *
   *   \inferrule{t\in R\mid -}{F}
   *
   * where :math:`F` corresponds to the one-step unfolding of the premise.
   * This is implemented by :math:`\texttt{RegExpOpr::reduceRegExpPos}(t\in R)`.
   * \endverbatim
   */
  EVALUE(RE_UNFOLD_POS),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- Regular expressions -- Negative Unfold**
   *
   * .. math::
   *
   *   \inferrule{t \not \in \mathit{re}.\text{*}(R) \mid -}{t \neq \ \epsilon \ \wedge \forall L. L \leq 0 \vee \mathit{str.len}(t) < L \vee \mathit{pre}(t, L) \not \in R \vee \mathit{suf}(t, L) \not \in \mathit{re}.\text{*}(R)}
   *
   * Or alternatively for regular expression concatenation:
   *
   * .. math::
   *
   *   \inferrule{t \not \in \mathit{re}.\text{++}(R_1, \ldots, R_n)\mid -}{\forall L. L < 0 \vee \mathit{str.len}(t) < L \vee \mathit{pre}(t, L) \not \in R_1 \vee \mathit{suf}(t, L) \not \in \mathit{re}.\text{++}(R_2, \ldots, R_n)}
   *
   * Note that in either case the varaible :math:`L` has type :math:`Int` and
   * name `"@var.str_index"`.
   *
   * \endverbatim
   */
  EVALUE(RE_UNFOLD_NEG),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- Regular expressions -- Unfold negative concatenation, fixed**
   *
   * .. math::
   *
   *   \inferrule{t\not\in \mathit{re}.\text{re.++}(r_1, \ldots, r_n) \mid \bot}{
   *  \mathit{pre}(t, L) \not \in r_1 \vee \mathit{suf}(t, L) \not \in \mathit{re}.\text{re.++}(r_2, \ldots, r_n)}
   *
   * where :math:`r_1` has fixed length :math:`L`.
   *
   * or alternatively for the reverse:
   *
   *
   * .. math::
   *
   *   \inferrule{t \not \in \mathit{re}.\text{re.++}(r_1, \ldots, r_n) \mid \top}{
   *   \mathit{suf}(t, str.len(t) - L) \not \in r_n \vee
   *   \mathit{pre}(t, str.len(t) - L) \not \in \mathit{re}.\text{re.++}(r_1, \ldots, r_{n-1})}
   *
   * where :math:`r_n` has fixed length :math:`L`.
   *
   * \endverbatim
   */
  EVALUE(RE_UNFOLD_NEG_CONCAT_FIXED),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- Code points**
   *
   * .. math::
   *
   *   \inferrule{-\mid t,s}{\mathit{to\_code}(t) = -1 \vee \mathit{to\_code}(t) \neq
   *   \mathit{to\_code}(s) \vee t = s}
   * \endverbatim
   */
  EVALUE(STRING_CODE_INJ),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- Sequence unit**
   *
   * .. math::
   *
   *   \inferrule{\mathit{unit}(x) = \mathit{unit}(y)\mid -}{x = y}
   *
   * Also applies to the case where :math:`\mathit{unit}(y)` is a constant
   * sequence of length one.
   * \endverbatim
   */
  EVALUE(STRING_SEQ_UNIT_INJ),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- Extensionality**
   *
   * .. math::
   *
   *   \inferrule{s \neq t\mid -}
   *   {\mathit{seq.len}(s) \neq \mathit{seq.len}(t) \vee (\mathit{seq.nth}(s,k)\neq\mathit{set.nth}(t,k) \wedge 0 \leq k \wedge k < \mathit{seq.len}(s))}
   *
   * where :math:`s,t` are terms of sequence type, :math:`k` is the
   * :math:`\texttt{STRINGS_DEQ_DIFF}` skolem for :math:`s,t`. Alternatively,
   * if :math:`s,t` are terms of string type, we use 
   * :math:`\mathit{seq.substr}(s,k,1)` instead of :math:`\mathit{seq.nth}(s,k)`
   * and similarly for :math:`t`.
   *
   * \endverbatim
   */
  EVALUE(STRING_EXT),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- (Macro) String inference**
   *
   * .. math::
   *
   *   \inferrule{?\mid F,\mathit{id},\mathit{isRev},\mathit{exp}}{F}
   *
   * used to bookkeep an inference that has not yet been converted via
   * :math:`\texttt{strings::InferProofCons::convert}`.
   * \endverbatim
   */
  EVALUE(MACRO_STRING_INFERENCE),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arithmetic -- Adding inequalities**
   *
   * An arithmetic literal is a term of the form :math:`p \diamond c` where
   * :math:`\diamond \in \{ <, \leq, =, \geq, > \}`, :math:`p` a
   * polynomial and :math:`c` a rational constant.
   *
   * .. math::
   *
   *   \inferrule{l_1 \dots l_n \mid k_1 \dots k_n}{t_1 \diamond t_2}
   *
   * where :math:`k_i \in \mathbb{R}, k_i \neq 0`, :math:`\diamond` is the
   * fusion of the :math:`\diamond_i` (flipping each if its :math:`k_i` is
   * negative) such that :math:`\diamond_i \in \{ <, \leq \}` (this implies that
   * lower bounds have negative :math:`k_i` and upper bounds have positive
   * :math:`k_i`), :math:`t_1` is the sum of the scaled polynomials and
   * :math:`t_2` is the sum of the scaled constants:
   *
   * .. math::
   *
   *   t_1 \colon= k_1 \cdot p_1 + \cdots + k_n \cdot p_n
   *
   *   t_2 \colon= k_1 \cdot c_1 + \cdots + k_n \cdot c_n
   *
   * \endverbatim
   */
  EVALUE(MACRO_ARITH_SCALE_SUM_UB),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arithmetic -- Non-linear multiply absolute value comparison**
   *
   * .. math::
   *
   *   \inferrule{F_1 \dots F_n \mid -}{F}
   * 
   * where :math:`F` is of the form 
   * :math:`\left| t_1 \cdot t_n \right| \diamond \left| s_1 \cdot s_n \right|`.
   * If :math:`\diamond` is :math:`=`, then each :math:`F_i` is
   * :math:`\left| t_i \right| = \left| s_i \right|`.
   *
   * If :math:`\diamond` is :math:`>`, then
   * each :math:`F_i` is either :math:`\left| t_i \right| > \left| s_i \right|` or
   * :math:`\left| t_i \right| = \left| s_i \right| \land t_i \neq 0`,
   * and :math:`F_1` is of the former form.
   *
   * \endverbatim
   */
  EVALUE(ARITH_MULT_ABS_COMPARISON),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arithmetic -- Sum upper bounds**
   *
   * .. math::
   *
   *   \inferrule{P_1 \dots P_n \mid -}{L \diamond R}
   *
   * where :math:`P_i` has the form :math:`L_i \diamond_i R_i` and
   * :math:`\diamond_i \in \{<, \leq, =\}`. Furthermore :math:`\diamond = <` if
   * :math:`\diamond_i = <` for any :math:`i` and :math:`\diamond = \leq`
   * otherwise, :math:`L = L_1 + \cdots + L_n` and :math:`R = R_1 + \cdots + R_n`.
   * \endverbatim
   */
  EVALUE(ARITH_SUM_UB),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arithmetic -- Tighten strict integer upper bounds**
   *
   * .. math::
   *
   *   \inferrule{i < c \mid -}{i \leq \lfloor c \rfloor}
   *
   * where :math:`i` has integer type.
   * \endverbatim
   */
  EVALUE(INT_TIGHT_UB),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arithmetic -- Tighten strict integer lower bounds**
   *
   * .. math::
   *
   *   \inferrule{i > c \mid -}{i \geq \lceil c \rceil}
   *
   * where :math:`i` has integer type.
   * \endverbatim
   */
  EVALUE(INT_TIGHT_LB),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arithmetic -- Trichotomy of the reals**
   *
   * .. math::
   *
   *   \inferrule{A, B \mid -}{C}
   *
   * where :math:`\neg A, \neg B, C` are :math:`x < c, x = c, x > c` in some order.
   * Note that :math:`\neg` here denotes arithmetic negation, i.e., flipping :math:`\geq` to :math:`<` etc.
   * \endverbatim
   */
  EVALUE(ARITH_TRICHOTOMY),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arithmetic -- Reduction**
   *
   * .. math::
   *
   *   \inferrule{- \mid t}{F}
   * 
   * where :math:`t` is an application of an extended arithmetic operator (e.g.
   * division, modulus, cosine, sqrt, is_int, to_int) and :math:`F` is the
   * reduction predicate for :math:`t`. In other words, :math:`F` is a
   * predicate that is used to reduce reasoning about :math:`t` to reasoning
   * about the core operators of arithmetic.
   *
   * In detail, :math:`F` is implemented by
   * :math:`\texttt{arith::OperatorElim::getAxiomFor(t)}`, see
   * :cvc5src:`theory/arith/operator_elim.h`.
   * \endverbatim
   */
  EVALUE(ARITH_REDUCTION),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arithmetic -- Polynomial normalization**
   *
   * .. math::
   *
   *   \inferrule{- \mid t = s}{t = s}
   *
   * where :math:`\texttt{arith::PolyNorm::isArithPolyNorm(t, s)} = \top`. This
   * method normalizes polynomials :math:`s` and :math:`t` over arithmetic.
   * \endverbatim
   */
  EVALUE(ARITH_POLY_NORM),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arithmetic -- Polynomial normalization for relations**
   *
   * .. math::
   *
   *  \inferrule{c_x \cdot (x_1 - x_2) = c_y \cdot (y_1 - y_2) \mid (x_1 \diamond x_2) = (y_1 \diamond y_2)}
   *            {(x_1 \diamond x_2) = (y_1 \diamond y_2)}
   *
   * where :math:`\diamond \in \{<, \leq, =, \geq, >\}`. :math:`c_x` and
   * :math:`c_y` are scaling factors. For :math:`<, \leq, \geq, >`, the scaling
   * factors have the same sign.
   *
   * If :math:`c_x` has type :math:`Real` and :math:`x_1, x_2` are of type
   * :math:`Int`, then :math:`(x_1 - x_2)` is wrapped in an application of
   * `to_real`, similarly for :math:`(y_1 - y_2)`.
   * \endverbatim
   */
  EVALUE(ARITH_POLY_NORM_REL),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arithmetic -- Sign inference**
   *
   * .. math::
   *
   *   \inferrule{- \mid f_1 \dots f_k, m}{(f_1 \land \dots \land f_k) \rightarrow m \diamond 0}
   *
   * where :math:`f_1 \dots f_k` are variables compared to zero (less, greater
   * or not equal), :math:`m` is a monomial from these variables and
   * :math:`\diamond` is the comparison (less or greater) that results from the
   * signs of the variables. In particular, :math:`\diamond` is :math`<`
   * if :math:`f_1 \dots f_k` contains an odd number of :math`<`. Otherwise
   * :math:`\diamond` is :math`>`. All variables with even exponent in :math:`m`
   * are given as not equal to zero while all variables with odd exponent
   * in :math:`m` should be given as less or greater than zero.
   * \endverbatim
   */
  EVALUE(ARITH_MULT_SIGN),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arithmetic -- Multiplication with positive factor**
   *
   * .. math::
   *
   *   \inferrule{- \mid m, l \diamond r}{(m > 0 \land l \diamond r) \rightarrow m \cdot l \diamond m \cdot r}
   *
   * where :math:`\diamond` is a relation symbol.
   * \endverbatim
   */
  EVALUE(ARITH_MULT_POS),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arithmetic -- Multiplication with negative factor**
   *
   * .. math::
   *
   *   \inferrule{- \mid m, l \diamond r}{(m < 0 \land l \diamond r) \rightarrow m \cdot l \diamond_{inv} m \cdot r}
   *
   * where :math:`\diamond` is a relation symbol and :math:`\diamond_{inv}` the
   * inverted relation symbol.
   * \endverbatim
   */
  EVALUE(ARITH_MULT_NEG),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arithmetic -- Multiplication tangent plane**
   *
   * .. math::
   *
   *   \inferruleSC{- \mid x, y, a, b, \sigma}{(t \leq tplane) = ((x \leq a \land y \geq b) \lor (x \geq a \land y \leq b))}{if $\sigma = \bot$}
   *
   *   \inferruleSC{- \mid x, y, a, b, \sigma}{(t \geq tplane) = ((x \leq a \land y \leq b) \lor (x \geq a \land y \geq b))}{if $\sigma = \top$}
   *
   * where :math:`x,y` are real terms (variables or extended terms),
   * :math:`t = x \cdot y`, :math:`a,b` are real
   * constants, :math:`\sigma \in \{ \top, \bot\}` and :math:`tplane := b \cdot x + a \cdot y - a \cdot b` is the tangent plane of :math:`x \cdot y` at :math:`(a,b)`.
   * \endverbatim
   */
  EVALUE(ARITH_MULT_TANGENT),

  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arithmetic -- Transcendentals -- Assert bounds on Pi**
   *
   * .. math::
   *
   *   \inferrule{- \mid l, u}{\texttt{real.pi} \geq l \land \texttt{real.pi}
   *   \leq u}
   *
   * where :math:`l,u` are valid lower and upper bounds on :math:`\pi`.
   * \endverbatim
   */
  EVALUE(ARITH_TRANS_PI),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arithmetic -- Transcendentals -- Exp at negative values**
   *
   * .. math::
   *
   *   \inferrule{- \mid t}{(t < 0) \leftrightarrow (\exp(t) < 1)}
   * \endverbatim
   */
  EVALUE(ARITH_TRANS_EXP_NEG),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arithmetic -- Transcendentals -- Exp is always positive**
   *
   * .. math::
   *
   *   \inferrule{- \mid t}{\exp(t) > 0}
   * \endverbatim
   */
  EVALUE(ARITH_TRANS_EXP_POSITIVITY),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arithmetic -- Transcendentals -- Exp grows super-linearly for positive
   * values**
   *
   * .. math::
   *
   *   \inferrule{- \mid t}{t \leq 0 \lor \exp(t) > t+1}
   * \endverbatim
   */
  EVALUE(ARITH_TRANS_EXP_SUPER_LIN),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arithmetic -- Transcendentals -- Exp at zero**
   *
   * .. math::
   *
   *   \inferrule{- \mid t}{(t=0) \leftrightarrow (\exp(t) = 1)}
   * \endverbatim
   */
  EVALUE(ARITH_TRANS_EXP_ZERO),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arithmetic -- Transcendentals -- Exp is approximated from above for \
   * negative values**
   *
   * .. math::
   *
   *   \inferrule{- \mid d,t,l,u}{(t \geq l \land t \leq u) \rightarrow exp(t)
   *   \leq \texttt{secant}(\exp, l, u, t)}
   *
   * where :math:`d` is an even positive number, :math:`t` an arithmetic term
   * and :math:`l,u` are lower and upper bounds on :math:`t`. Let :math:`p` be
   * the :math:`d`'th taylor polynomial at zero (also called the Maclaurin
   * series) of the exponential function. :math:`\texttt{secant}(\exp, l, u, t)`
   * denotes the secant of :math:`p` from :math:`(l, \exp(l))` to :math:`(u,
   * \exp(u))` evaluated at :math:`t`, calculated as follows:
   *
   * .. math::
   *
   *   \frac{p(l) - p(u)}{l - u} \cdot (t - l) + p(l)
   *
   * The lemma states that if :math:`t` is between :math:`l` and :math:`u`, then
   * :math:`\exp(t` is below the secant of :math:`p` from :math:`l` to
   * :math:`u`.
   * \endverbatim
   */
  EVALUE(ARITH_TRANS_EXP_APPROX_ABOVE_NEG),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arithmetic -- Transcendentals -- Exp is approximated from above for \
   * positive values**
   *
   * .. math::
   *
   *   \inferrule{- \mid d,t,l,u}{(t \geq l \land t \leq u) \rightarrow exp(t)
   *   \leq \texttt{secant-pos}(\exp, l, u, t)}
   *
   * where :math:`d` is an even positive number, :math:`t` an arithmetic term
   * and :math:`l,u` are lower and upper bounds on :math:`t`. Let :math:`p^*` be
   * a modification of the :math:`d`'th taylor polynomial at zero (also called
   * the Maclaurin series) of the exponential function as follows where
   * :math:`p(d-1)` is the regular Maclaurin series of degree :math:`d-1`:
   *
   * .. math::
   *
   *   p^* := p(d-1) \cdot \frac{1 + t^n}{n!}
   *
   * :math:`\texttt{secant-pos}(\exp, l, u, t)` denotes the secant of :math:`p`
   * from :math:`(l, \exp(l))` to :math:`(u, \exp(u))` evaluated at :math:`t`,
   * calculated as follows:
   *
   * .. math::
   *
   *   \frac{p(l) - p(u)}{l - u} \cdot (t - l) + p(l)
   *
   * The lemma states that if :math:`t` is between :math:`l` and :math:`u`, then
   * :math:`\exp(t` is below the secant of :math:`p` from :math:`l` to
   * :math:`u`.
   * \endverbatim
   */
  EVALUE(ARITH_TRANS_EXP_APPROX_ABOVE_POS),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arithmetic -- Transcendentals -- Exp is approximated from below**
   *
   * .. math::
   *
   *   \inferrule{- \mid d,c,t}{t \geq c \rightarrow exp(t) \geq \texttt{maclaurin}(\exp, d, c)}
   *
   * where :math:`d` is a non-negative number, :math:`t` an arithmetic term and
   * :math:`\texttt{maclaurin}(\exp, n+1, c)` is the :math:`(n+1)`'th taylor
   * polynomial at zero (also called the Maclaurin series) of the exponential
   * function evaluated at :math:`c` where :math:`n` is :math:`2 \cdot d`.
   * The Maclaurin series for the exponential function is the following:
   *
   * .. math::
   *
   *   \exp(x) = \sum_{i=0}^{\infty} \frac{x^i}{i!}
   *
   * This rule furthermore requires that :math:`1 > c^{n+1}/(n+1)!`
   * \endverbatim
   */
  EVALUE(ARITH_TRANS_EXP_APPROX_BELOW),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arithmetic -- Transcendentals -- Sine is always between -1 and 1**
   *
   * .. math::
   *
   *   \inferrule{- \mid t}{\sin(t) \leq 1 \land \sin(t) \geq -1}
   * \endverbatim
   */
  EVALUE(ARITH_TRANS_SINE_BOUNDS),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arithmetic -- Transcendentals -- Sine is shifted to -pi...pi**
   *
   * .. math::
   *
   *   \inferrule{- \mid x}{-\pi \leq y \leq \pi \land \sin(y) = \sin(x)
   *   \land (\ite{-\pi \leq x \leq \pi}{x = y}{x = y + 2 \pi s})}
   *
   * where :math:`x` is the argument to sine, :math:`y` is a new real skolem
   * that is :math:`x` shifted into :math:`-\pi \dots \pi` and :math:`s` is a
   * new integer skolem that is the number of phases :math:`y` is shifted.
   * In particular, :math:`y` is the
   * :cpp:enumerator:`TRANSCENDENTAL_PURIFY_ARG <cvc5::SkolemId::TRANSCENDENTAL_PURIFY_ARG>`
   * skolem for :math:`\sin(x)` and :math:`s` is the
   * :cpp:enumerator:`TRANSCENDENTAL_SINE_PHASE_SHIFT <cvc5::SkolemId::TRANSCENDENTAL_SINE_PHASE_SHIFT>`
   * skolem for :math:`x`.
   * \endverbatim
   */
  EVALUE(ARITH_TRANS_SINE_SHIFT),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arithmetic -- Transcendentals -- Sine is symmetric with respect to \
   * negation of the argument**
   *
   * .. math::
   *
   *   \inferrule{- \mid t}{\sin(t) - \sin(-t) = 0}
   * \endverbatim
   */
  EVALUE(ARITH_TRANS_SINE_SYMMETRY),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arithmetic -- Transcendentals -- Sine is bounded by the tangent at zero**
   *
   * .. math::
   *
   *   \inferrule{- \mid t}{(t > 0 \rightarrow \sin(t) < t) \land (t < 0
   *   \rightarrow \sin(t) > t)} \endverbatim
   */
  EVALUE(ARITH_TRANS_SINE_TANGENT_ZERO),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arithmetic -- Transcendentals -- Sine is bounded by the tangents at -pi and pi**
   *
   * .. math::
   *
   *   \inferrule{- \mid t}{(t > -\pi \rightarrow \sin(t) > -\pi - t) \land (t <
   *   \pi \rightarrow \sin(t) < \pi - t)} \endverbatim
   */
  EVALUE(ARITH_TRANS_SINE_TANGENT_PI),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arithmetic -- Transcendentals -- Sine is approximated from above for\
   * negative values**
   *
   * .. math::
   *
   *   \inferrule{- \mid d,t,lb,ub,l,u}{(t \geq lb \land t \leq ub) \rightarrow
   *   \sin(t) \leq \texttt{secant}(\sin, l, u, t)}
   *
   * where :math:`d` is an even positive number, :math:`t` an arithmetic term,
   * :math:`lb,ub` are symbolic lower and upper bounds on :math:`t` (possibly
   * containing :math:`\pi`) and :math:`l,u` the evaluated lower and upper
   * bounds on :math:`t`. Let :math:`p` be the :math:`d`'th taylor polynomial at
   * zero (also called the Maclaurin series) of the sine function.
   * :math:`\texttt{secant}(\sin, l, u, t)` denotes the secant of :math:`p` from
   * :math:`(l, \sin(l))` to :math:`(u, \sin(u))` evaluated at :math:`t`,
   * calculated as follows:
   *
   * .. math::
   *
   *   \frac{p(l) - p(u)}{l - u} \cdot (t - l) + p(l)
   *
   * The lemma states that if :math:`t` is between :math:`l` and :math:`u`, then
   * :math:`\sin(t)` is below the secant of :math:`p` from :math:`l` to
   * :math:`u`.
   * \endverbatim
   */
  EVALUE(ARITH_TRANS_SINE_APPROX_ABOVE_NEG),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arithmetic -- Transcendentals -- Sine is approximated from above for \
   * positive values**
   *
   * .. math::
   *
   *   \inferrule{- \mid d,t,c,lb,ub}{(t \geq lb \land t \leq ub) \rightarrow
   *   \sin(t) \leq \texttt{upper}(\sin, c)}
   *
   * where :math:`d` is an even positive number, :math:`t` an arithmetic term,
   * :math:`c` an arithmetic constant and :math:`lb,ub` are symbolic lower and
   * upper bounds on :math:`t` (possibly containing :math:`\pi`). Let :math:`p`
   * be the :math:`d`'th taylor polynomial at zero (also called the Maclaurin
   * series) of the sine function. :math:`\texttt{upper}(\sin, c)` denotes the
   * upper bound on :math:`\sin(c)` given by :math:`p` and :math:`lb,up` such
   * that :math:`\sin(t)` is the maximum of the sine function on
   * :math:`(lb,ub)`.
   * \endverbatim
   */
  EVALUE(ARITH_TRANS_SINE_APPROX_ABOVE_POS),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arithmetic -- Transcendentals -- Sine is approximated from below for \
   * negative values**
   *
   * .. math::
   *
   *   \inferrule{- \mid d,t,c,lb,ub}{(t \geq lb \land t \leq ub) \rightarrow
   *   \sin(t) \geq \texttt{lower}(\sin, c)}
   *
   * where :math:`d` is an even positive number, :math:`t` an arithmetic term,
   * :math:`c` an arithmetic constant and :math:`lb,ub` are symbolic lower and
   * upper bounds on :math:`t` (possibly containing :math:`\pi`). Let :math:`p`
   * be the :math:`d`'th taylor polynomial at zero (also called the Maclaurin
   * series) of the sine function. :math:`\texttt{lower}(\sin, c)` denotes the
   * lower bound on :math:`\sin(c)` given by :math:`p` and :math:`lb,up` such
   * that :math:`\sin(t)` is the minimum of the sine function on
   * :math:`(lb,ub)`.
   * \endverbatim
   */
  EVALUE(ARITH_TRANS_SINE_APPROX_BELOW_NEG),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arithmetic -- Transcendentals -- Sine is approximated from below for \
   * positive values**
   *
   * .. math::
   *
   *   \inferrule{- \mid d,t,lb,ub,l,u}{(t \geq lb \land t \leq ub) \rightarrow
   *   \sin(t) \geq \texttt{secant}(\sin, l, u, t)}
   *
   * where :math:`d` is an even positive number, :math:`t` an arithmetic term,
   * :math:`lb,ub` are symbolic lower and upper bounds on :math:`t` (possibly
   * containing :math:`\pi`) and :math:`l,u` the evaluated lower and upper
   * bounds on :math:`t`. Let :math:`p` be the :math:`d`'th taylor polynomial at
   * zero (also called the Maclaurin series) of the sine function.
   * :math:`\texttt{secant}(\sin, l, u, t)` denotes the secant of :math:`p` from
   * :math:`(l, \sin(l))` to :math:`(u, \sin(u))` evaluated at :math:`t`,
   * calculated as follows:
   *
   * .. math::
   *
   *   \frac{p(l) - p(u)}{l - u} \cdot (t - l) + p(l)
   *
   * The lemma states that if :math:`t` is between :math:`l` and :math:`u`, then
   * :math:`\sin(t)` is above the secant of :math:`p` from :math:`l` to
   * :math:`u`.
   * \endverbatim
   */
  EVALUE(ARITH_TRANS_SINE_APPROX_BELOW_POS),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **External -- LFSC**
   *
   * Place holder for LFSC rules.
   *
   * .. math::
   *
   *   \inferrule{P_1, \dots, P_n\mid \texttt{id}, Q, A_1,\dots, A_m}{Q}
   *
   * Note that the premises and arguments are arbitrary. It's expected that
   * :math:`\texttt{id}` refer to a proof rule in the external LFSC calculus.
   * \endverbatim
   */
  EVALUE(LFSC_RULE),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **External -- Alethe**
   *
   * Place holder for Alethe rules.
   *
   * .. math::
   *
   *   \inferrule{P_1, \dots, P_n\mid \texttt{id}, Q, Q', A_1,\dots, A_m}{Q}
   *
   * Note that the premises and arguments are arbitrary. It's expected that
   * :math:`\texttt{id}` refer to a proof rule in the external Alethe calculus,
   * and that :math:`Q'` be the representation of Q to be printed by the Alethe
   * printer.
   * \endverbatim
   */
  EVALUE(ALETHE_RULE),

  //================================================= Unknown rule
  EVALUE(UNKNOWN),
#ifdef CVC5_API_USE_C_ENUMS
  // must be last entry
  EVALUE(LAST),
#endif
};
// clang-format on

#ifdef CVC5_API_USE_C_ENUMS
#undef EVALUE
#define EVALUE(name) CVC5_PROOF_REWRITE_RULE_##name
#endif

/**
 * \verbatim embed:rst:leading-asterisk
 * This enumeration represents the rewrite rules used in a rewrite proof. Some
 * of the rules are internal ad-hoc rewrites, while others are rewrites
 * specified by the RARE DSL. This enumeration is used as the first argument to
 * the :cpp:enumerator:`DSL_REWRITE <cvc5::ProofRule::DSL_REWRITE>` proof rule
 * and the :cpp:enumerator:`THEORY_REWRITE <cvc5::ProofRule::THEORY_REWRITE>`
 * proof rule.
 * \endverbatim
 */
enum ENUM(ProofRewriteRule)
{
  EVALUE(NONE),
  // Custom theory rewrites.
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Builtin -- Distinct elimination**
   *
   * .. math::
   *
   *   \texttt{distinct}(t_1, t_2) = \neg (t_1 = t2)
   *
   * if :math:`n = 2`, or
   * 
   * .. math::
   *
   *   \texttt{distinct}(t_1, \ldots, tn) = \bigwedge_{i=1}^n \bigwedge_{j=i+1}^n t_i \neq t_j
   *
   * if :math:`n > 2`
   *
   * \endverbatim
   */
  EVALUE(DISTINCT_ELIM),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Builtin -- Distinct cardinality conflict**
   *
   * .. math::
   *
   *   \texttt{distinct}(t_1, \ldots, tn) = \bot
   *
   * where :math:`n` is greater than the cardinality of the type of
   * :math:`t_1, \ldots, t_n`.
   *
   * \endverbatim
   */
  EVALUE(DISTINCT_CARD_CONFLICT),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **UF -- Bitvector to natural elimination**
   *
   * .. math::
   *
   *   \texttt{ubv_to_int}(t) = t_1 + \ldots + t_n
   *
   * where for :math:`i=1, \ldots, n`, :math:`t_i` is
   * :math:`\texttt{ite}(x[i-1, i-1] = 1, 2^i, 0)`.
   *
   * \endverbatim
   */
  EVALUE(UBV_TO_INT_ELIM),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **UF -- Integer to bitvector elimination**
   *
   * .. math::
   *
   *   \texttt{int2bv}_n(t) = (bvconcat t_1 \ldots t_n)
   *
   * where for :math:`i=1, \ldots, n`, :math:`t_i` is
   * :math:`\texttt{ite}(\texttt{mod}(t,2^n) \geq 2^{n-1}, 1, 0)`.
   *
   * \endverbatim
   */
  EVALUE(INT_TO_BV_ELIM),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Booleans -- Negation Normal Form with normalization**
   *
   * .. math::
   *
   *   F = G
   *
   * where :math:`G` is the result of applying negation normal form to
   * :math:`F` with additional normalizations, see
   * TheoryBoolRewriter::computeNnfNorm.
   *
   * \endverbatim
   */
  EVALUE(MACRO_BOOL_NNF_NORM),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Booleans -- Bitvector invert solve**
   *
   * .. math::
   *
   *   ((t_1 = t_2) = (x = r)) = \top
   *
   * where :math:`x` occurs on an invertible path in :math:`t_1 = t_2`
   * and has solved form :math:`r`.
   *
   * \endverbatim
   */
  EVALUE(MACRO_BOOL_BV_INVERT_SOLVE),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arithmetic -- Integer equality conflict**
   *
   * .. math::
   *
   *   (t=s) = \bot
   *
   * where :math:`t=s` is equivalent (via
   * :cpp:enumerator:`ARITH_POLY_NORM <cvc5::ProofRule::ARITH_POLY_NORM>`) to
   * :math:`(r = c)` where :math:`r` is an integral term and :math:`c` is a
   * non-integral constant.
   *
   * \endverbatim
   */
  EVALUE(MACRO_ARITH_INT_EQ_CONFLICT),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arithmetic -- Integer inequality tightening**
   *
   * .. math::
   *
   *   (t \geq s) = ( r \geq \lceil c \rceil)
   *
   * or
   *
   * .. math::
   *
   *   (t \geq s) = \neg( r \geq \lceil c \rceil)
   *
   * where :math:`t \geq s` is equivalent (via
   * :cpp:enumerator:`ARITH_POLY_NORM <cvc5::ProofRule::ARITH_POLY_NORM>`) to
   * the right hand side where :math:`r` is an integral term and
   * :math:`c` is a non-integral constant. Note that we end up with a
   * negation if the leading coefficient in :math:`t` is negative.
   *
   * \endverbatim
   */
  EVALUE(MACRO_ARITH_INT_GEQ_TIGHTEN),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arithmetic -- strings predicate entailment**
   *
   * .. math::
   *
   *   (= s t) = c
   *
   * .. math::
   *
   *   (>= s t) = c
   *
   * where :math:`c` is a Boolean constant.
   * This macro is elaborated by applications of :cpp:enumerator:`EVALUATE <cvc5::ProofRule::EVALUATE>`,
   * :cpp:enumerator:`ARITH_POLY_NORM <cvc5::ProofRule::ARITH_POLY_NORM>`,
   * :cpp:enumerator:`ARITH_STRING_PRED_ENTAIL <cvc5::ProofRewriteRule::ARITH_STRING_PRED_ENTAIL>`,
   * :cpp:enumerator:`ARITH_STRING_PRED_SAFE_APPROX <cvc5::ProofRewriteRule::ARITH_STRING_PRED_SAFE_APPROX>`,
   * as well as other rewrites for normalizing arithmetic predicates.
   *
   * \endverbatim
   */
  EVALUE(MACRO_ARITH_STRING_PRED_ENTAIL),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arithmetic -- strings predicate entailment**
   *
   * .. math::
   *
   *   (>= n 0) = true
   *
   * Where :math:`n` can be shown to be greater than or equal to :math:`0` by
   * reasoning about string length being positive and basic properties of
   * addition and multiplication.
   *
   * \endverbatim
   */
  EVALUE(ARITH_STRING_PRED_ENTAIL),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arithmetic -- strings predicate entailment**
   *
   * .. math::
   *
   *   (>= n 0) = (>= m 0)
   *
   * Where :math:`m` is a safe under-approximation of :math:`n`, namely
   * we have that :math:`(>= n m)` and :math:`(>= m 0)`.
   *
   * In detail, subterms of :math:`n` may be replaced with other terms to
   * obtain :math:`m` based on the reasoning described in the paper
   * Reynolds et al, CAV 2019, "High-Level Abstractions for Simplifying
   * Extended String Constraints in SMT".
   *
   * \endverbatim
   */
  EVALUE(ARITH_STRING_PRED_SAFE_APPROX),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arithmetic -- power elimination**
   *
   * .. math::
   *
   *   (x ^ c) = (x \cdot \ldots \cdot x)
   *
   * where :math:`c` is a non-negative integer.
   *
   * \endverbatim
   */
  EVALUE(ARITH_POW_ELIM),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Equality -- Beta reduction**
   *
   * .. math::
   *
   *   ((\lambda x_1 \ldots x_n.\> t) \ t_1 \ldots t_n) = t\{x_1 \mapsto t_1, \ldots, x_n \mapsto t_n\}
   *
   * or alternatively
   *
   * .. math::
   *
   *   ((\lambda x_1 \ldots x_n.\> t) \ t_1) = (\lambda x_2 \ldots x_n.\> t)\{x_1 \mapsto t_1\}
   *
   * In the former case, the left hand side may either be a term of kind
   * `cvc5::Kind::APPLY_UF` or `cvc5::Kind::HO_APPLY`. The latter case is used
   * only if the term has kind `cvc5::Kind::HO_APPLY`.
   *
   * In either case, the right hand side of the equality in the conclusion is
   * computed using standard substitution via ``Node::substitute``.
   *
   * \endverbatim
   */
  EVALUE(BETA_REDUCE),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Equality -- Lambda elimination**
   *
   * .. math::
   *
   *   (\lambda x_1 \ldots x_n.\> f(x_1 \ldots x_n)) = f
   *
   * \endverbatim
   */
  EVALUE(LAMBDA_ELIM),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Equality -- Macro lambda application capture avoid**
   *
   * .. math::
   *
   *   ((\lambda x_1 \ldots x_n.\> t) \ t_1 \ldots t_n) = ((\lambda y_1 \ldots y_n.\> t') \ t_1 \ldots t_n)
   *
   * The terms may either be of kind
   * `cvc5::Kind::APPLY_UF` or `cvc5::Kind::HO_APPLY`.
   * This rule ensures that the free variables of :math:`y_1, \ldots, y_n, t_1 \ldots t_n`
   * do not occur in binders within :math:`t'`, and
   * :math:`(\lambda x_1 \ldots x_n.\> t)` is alpha-equivalent to
   * :math:`(\lambda y_1 \ldots y_n.\> t')`. This rule is applied prior to
   * beta reduction to ensure there is no variable capturing.
   *
   * \endverbatim
   */
  EVALUE(MACRO_LAMBDA_CAPTURE_AVOID),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arrays -- Constant array select**
   *
   * .. math::
   *
   *   (select A x) = c
   *
   * where :math:`A` is a constant array storing element :math:`c`.
   *
   * \endverbatim
   */
  EVALUE(ARRAYS_SELECT_CONST),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arrays -- Macro normalize operation**
   *
   * .. math::
   *
   *   A = B
   *
   * where :math:`B` is the result of normalizing the array operation :math:`A`
   * into a canonical form, based on commutativity of disjoint indices.
   *
   * \endverbatim
   */
  EVALUE(MACRO_ARRAYS_NORMALIZE_OP),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arrays -- Macro normalize constant**
   *
   * .. math::
   *
   *   A = B
   *
   * where :math:`B` is the result of normalizing the array value :math:`A`
   * into a canonical form, using the internal method
   * TheoryArraysRewriter::normalizeConstant.
   *
   * \endverbatim
   */
  EVALUE(MACRO_ARRAYS_NORMALIZE_CONSTANT),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Arrays -- Expansion of array range equality**
   *
   * .. math::
   *
   *   \mathit{eqrange}(a,b,i,j)=
   *   \forall x.\> i \leq x \leq j \rightarrow
   *   \mathit{select}(a,x)=\mathit{select}(b,x)
   * \endverbatim
   */
  EVALUE(ARRAYS_EQ_RANGE_EXPAND),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Quantifiers -- Exists elimination**
   *
   * .. math::
   *
   *   \exists x_1\dots x_n.\> F = \neg \forall x_1\dots x_n.\> \neg F
   *
   * \endverbatim
   */
  EVALUE(EXISTS_ELIM),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Quantifiers -- Unused variables**
   *
   * .. math::
   *
   *   \forall X.\> F = \forall X_1.\> F
   *
   * where :math:`X_1` is the subset of :math:`X` that appear free in :math:`F`
   * and :math:`X_1` does not contain duplicate variables.
   *
   * \endverbatim
   */
  EVALUE(QUANT_UNUSED_VARS),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Quantifiers -- Macro merge prenex**
   *
   * .. math::
   *
   *   \forall X_1.\> \ldots \forall X_n.\> F = \forall X.\> F
   *
   * where :math:`X_1 \ldots X_n` are lists of variables and :math:`X` is the
   * result of removing duplicates from :math:`X_1 \ldots X_n`.
   *
   * \endverbatim
   */
  EVALUE(MACRO_QUANT_MERGE_PRENEX),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Quantifiers -- Merge prenex**
   *
   * .. math::
   *
   *   \forall X_1.\> \ldots \forall X_n.\> F = \forall X_1 \ldots X_n.\> F
   *
   * where :math:`X_1 \ldots X_n` are lists of variables.
   *
   * \endverbatim
   */
  EVALUE(QUANT_MERGE_PRENEX),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Quantifiers -- Macro prenex**
   *
   * .. math::
   *
   *   (\forall X.\> F_1 \vee \cdots \vee (\forall Y.\> F_i) \vee \cdots \vee F_n) = (\forall X Z.\> F_1 \vee \cdots \vee F_i\{ Y \mapsto Z \} \vee \cdots \vee F_n)
   *
   * \endverbatim
   */
  EVALUE(MACRO_QUANT_PRENEX),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Quantifiers -- Macro miniscoping**
   *
   * .. math::
   *
   *   \forall X.\> F_1 \wedge \cdots \wedge F_n =
   *   G_1 \wedge \cdots \wedge G_n
   *
   * where each :math:`G_i` is semantically equivalent to
   * :math:`\forall X.\> F_i`, or alternatively
   *
   * .. math::
   *
   *   \forall X.\> \ite{C}{F_1}{F_2} = \ite{C}{G_1}{G_2}
   *
   * where :math:`C` does not have any free variable in :math:`X`.
   *
   * \endverbatim
   */
  EVALUE(MACRO_QUANT_MINISCOPE),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Quantifiers -- Miniscoping and**
   *
   * .. math::
   *
   *   \forall X.\> F_1 \wedge \ldots \wedge F_n =
   *   (\forall X.\> F_1) \wedge \ldots \wedge (\forall X.\> F_n)
   *
   * \endverbatim
   */
  EVALUE(QUANT_MINISCOPE_AND),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Quantifiers -- Miniscoping or**
   *
   * .. math::
   *
   *   \forall X.\> F_1 \vee \ldots \vee F_n = (\forall X_1.\> F_1) \vee \ldots \vee (\forall X_n.\> F_n)
   *
   * where :math:`X = X_1 \ldots X_n`, and the right hand side does not have any
   * free variable in :math:`X`.
   *
   * \endverbatim
   */
  EVALUE(QUANT_MINISCOPE_OR),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Quantifiers -- Miniscoping ite**
   *
   * .. math::
   *
   *   \forall X.\> \ite{C}{F_1}{F_2} = \ite{C}{\forall X.\> F_1}{\forall X.\> F_2}
   *
   * where :math:`C` does not have any free variable in :math:`X`.
   *
   * \endverbatim
   */
  EVALUE(QUANT_MINISCOPE_ITE),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Quantifiers -- Datatypes Split**
   *
   * .. math::
   *
   *   (\forall x Y.\> F) = (\forall X_1 Y. F_1) \vee \cdots \vee (\forall X_n Y. F_n)
   *
   * where :math:`x` is of a datatype type with constructors
   * :math:`C_1, \ldots, C_n`, where for each :math:`i = 1, \ldots, n`,
   * :math:`F_i` is :math:`F \{ x \mapsto C_i(X_i) \}`.
   * 
   * \endverbatim
   */
  EVALUE(QUANT_DT_SPLIT),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Quantifiers -- Macro datatype variable expand **
   *
   * .. math::
   *
   *   (\forall Y x Z.\> F) = (\forall Y X_1 Z. F_1) \vee \cdots \vee (\forall Y X_n Z. F_n)
   *
   * where :math:`x` is of a datatype type with constructors
   * :math:`C_1, \ldots, C_n`, where for each :math:`i = 1, \ldots, n`,
   * :math:`F_i` is :math:`F \{ x \mapsto C_i(X_i) \}`, and
   * :math:`F` entails :math:`\mathit{is}_c(x)` for some :math:`c`.
   *
   * \endverbatim
   */
  EVALUE(MACRO_QUANT_DT_VAR_EXPAND),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Quantifiers -- Macro connected free variable partitioning**
   *
   * .. math::
   *
   *   \forall X.\> F_1 \vee \ldots \vee F_n =
   *   (\forall X_1.\> F_{1,1} \vee \ldots \vee F_{1,k_1}) \vee \ldots \vee
   *   (\forall X_m.\> F_{m,1} \vee \ldots \vee F_{m,k_m})
   *
   * where :math:`X_1, \ldots, X_m` is a partition of :math:`X`. This is
   * determined by computing the connected components when considering two
   * variables in :math:`X` to be connected if they occur in the same
   * :math:`F_i`.
   * \endverbatim
   */
  EVALUE(MACRO_QUANT_PARTITION_CONNECTED_FV),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Quantifiers -- Macro variable elimination equality**
   *
   * .. math::
   *
   *   \forall x Y.\> F = \forall Y.\> F \{ x \mapsto t \}
   *
   * where :math:`\neg F` entails :math:`x = t`.
   *
   * \endverbatim
   */
  EVALUE(MACRO_QUANT_VAR_ELIM_EQ),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Quantifiers -- Macro variable elimination equality**
   *
   * .. math::
   *
   *  (\forall x.\> x \neq t \vee F) = F \{ x \mapsto t \}
   *
   * or alternatively
   *
   * .. math::
   *
   *  (\forall x.\> x \neq t) = \bot
   *
   * \endverbatim
   */
  EVALUE(QUANT_VAR_ELIM_EQ),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Quantifiers -- Macro variable elimination inequality**
   *
   * .. math::
   *
   *   \forall x Y.\> F = \forall Y.\> G
   *
   * where :math:`F` is a disjunction and where :math:`G` is the
   * result of dropping all literals containing :math:`x`. This is
   * applied only when all such literals are lower (resp. upper) bounds
   * for integer or real variable :math:`x`. Note that :math:`G` may
   * be false, and :math:`Y` may be empty in which case it is omitted.
   *
   * \endverbatim
   */
  EVALUE(MACRO_QUANT_VAR_ELIM_INEQ),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Quantifiers -- Macro quantifiers rewrite body**
   *
   * .. math::
   *
   *   \forall X.\> F = \forall X.\> G
   *
   * where :math:`G` is semantically equivalent to :math:`F`.
   *
   * \endverbatim
   */
  EVALUE(MACRO_QUANT_REWRITE_BODY),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Datatypes -- Instantiation**
   *
   * .. math::
   *
   *    \mathit{is}_C(t) = (t = C(\mathit{sel}_1(t),\dots,\mathit{sel}_n(t)))
   *
   * where :math:`C` is the :math:`n^{\mathit{th}}` constructor of the type of
   * :math:`t`, and :math:`\mathit{is}_C` is the discriminator (tester) for
   * :math:`C`.
   * \endverbatim
   */
  EVALUE(DT_INST),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Datatypes -- collapse selector**
   *
   * .. math::
   *
   *   s_i(c(t_1, \ldots, t_n)) = t_i
   *
   * where :math:`s_i` is the :math:`i^{th}` selector for constructor :math:`c`.
   *
   * \endverbatim
   */
  EVALUE(DT_COLLAPSE_SELECTOR),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Datatypes -- collapse tester**
   *
   * .. math::
   *
   *   \mathit{is}_c(c(t_1, \ldots, t_n)) = true
   *
   * or alternatively
   *
   * .. math::
   *
   *   \mathit{is}_c(d(t_1, \ldots, t_n)) = false
   *
   * where :math:`c` and :math:`d` are distinct constructors.
   *
   * \endverbatim
   */
  EVALUE(DT_COLLAPSE_TESTER),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Datatypes -- collapse tester**
   *
   * .. math::
   *
   *   \mathit{is}_c(t) = true
   *
   * where :math:`c` is the only constructor of its associated datatype.
   *
   * \endverbatim
   */
  EVALUE(DT_COLLAPSE_TESTER_SINGLETON),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Datatypes -- Macro constructor equality**
   *
   * .. math::
   *
   *   (t = s) = (t_1 = s_1 \wedge \ldots \wedge t_n = s_n)
   *
   * where :math:`t_1, \ldots, t_n` and :math:`s_1, \ldots, s_n` are subterms
   * of :math:`t` and :math:`s` that occur at the same position respectively
   * (beneath constructor applications), or alternatively
   *
   * .. math::
   *
   *   (t = s) = false
   * 
   * where :math:`t` and :math:`s` have subterms that occur in the same
   * position (beneath constructor applications) that are distinct.
   *
   * \endverbatim
   */
  EVALUE(MACRO_DT_CONS_EQ),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Datatypes -- constructor equality**
   *
   * .. math::
   *
   *   (c(t_1, \ldots, t_n) = c(s_1, \ldots, s_n)) =
   *   (t_1 = s_1 \wedge \ldots \wedge t_n = s_n)
   *
   * where :math:`c` is a constructor.
   *
   * \endverbatim
   */
  EVALUE(DT_CONS_EQ),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Datatypes -- constructor equality clash**
   *
   * .. math::
   *
   *   (t = s) = false
   *
   * where :math:`t` and :math:`s` have subterms that occur in the same
   * position (beneath constructor applications) that are distinct constructor
   * applications.
   *
   * \endverbatim
   */
  EVALUE(DT_CONS_EQ_CLASH),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Datatypes -- cycle**
   *
   * .. math::
   *
   *   (x = t[x]) = \bot
   *
   * where all terms on the path to :math:`x` in :math:`t[x]` are applications
   * of constructors, and this path is non-empty.
   *
   * \endverbatim
   */
  EVALUE(DT_CYCLE),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Datatypes -- collapse tester**
   *
   * .. math::
   *
   *   u_{c,i}(c(t_1, \ldots, t_i, \ldots, t_n), s) = c(t_1, \ldots, s, \ldots, t_n)
   *
   * or alternatively
   *
   * .. math::
   *
   *   u_{c,i}(d(t_1, \ldots, t_n), s) = d(t_1, \ldots, t_n)
   *
   * where :math:`c` and :math:`d` are distinct constructors.
   *
   * \endverbatim
   */
  EVALUE(DT_COLLAPSE_UPDATER),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Datatypes - updater elimination**
   *
   * .. math::
   *
   *   u_{c,i}(t, s) = ite(\mathit{is}_c(t), c(s_0(t), \ldots, s, \ldots s_n(t)), t)
   *
   * where :math:`s_i` is the :math:`i^{th}` selector for constructor :math:`c`.
   *
   * \endverbatim
   */
  EVALUE(DT_UPDATER_ELIM),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Datatypes -- match elimination**
   *
   * .. math::
   *
   *   \texttt{match}(t ((p_1 c_1) \ldots (p_n c_n))) = \texttt{ite}(F_1, r_1, \texttt{ite}( \ldots, r_n))
   * 
   * where for :math:`i=1, \ldots, n`, :math:`F_1` is a formula that holds iff
   * :math:`t` matches :math:`p_i` and :math:`r_i` is the result of a
   * substitution on :math:`c_i` based on this match.
   *
   * \endverbatim
   */
  EVALUE(DT_MATCH_ELIM),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Bitvectors -- Macro extract and concat **
   *
   * .. math::
   *
   *    a = b
   *
   * where :math:`a` is rewritten to :math:`b` by the internal rewrite
   * rule ExtractConcat.
   *
   * \endverbatim
   */
  EVALUE(MACRO_BV_EXTRACT_CONCAT),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Bitvectors -- Macro or simplify **
   *
   * .. math::
   *
   *    a = b
   *
   * where :math:`a` is rewritten to :math:`b` by the internal rewrite
   * rule OrSimplify.
   *
   * \endverbatim
   */
  EVALUE(MACRO_BV_OR_SIMPLIFY),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Bitvectors -- Macro and simplify **
   *
   * .. math::
   *
   *    a = b
   *
   * where :math:`a` is rewritten to :math:`b` by the internal rewrite
   * rule AndSimplify.
   *
   * \endverbatim
   */
  EVALUE(MACRO_BV_AND_SIMPLIFY),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Bitvectors -- Macro xor simplify **
   *
   * .. math::
   *
   *    a = b
   *
   * where :math:`a` is rewritten to :math:`b` by the internal rewrite
   * rule XorSimplify.
   *
   * \endverbatim
   */
  EVALUE(MACRO_BV_XOR_SIMPLIFY),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Bitvectors -- Macro and/or/xor concat pullup **
   *
   * .. math::
   *
   *    a = b
   *
   * where :math:`a` is rewritten to :math:`b` by the internal rewrite
   * rule AndOrXorConcatPullup.
   *
   * \endverbatim
   */
  EVALUE(MACRO_BV_AND_OR_XOR_CONCAT_PULLUP),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Bitvectors -- Macro multiply signed less than multiply **
   *
   * .. math::
   *
   *    a = b
   *
   * where :math:`a` is rewritten to :math:`b` by the internal rewrite
   * rule MultSltMult.
   *
   * \endverbatim
   */
  EVALUE(MACRO_BV_MULT_SLT_MULT),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Bitvectors -- Macro concat extract merge **
   *
   * .. math::
   *
   *    a = b
   *
   * where :math:`a` is rewritten to :math:`b` by the internal rewrite
   * rule ConcatExtractMerge.
   *
   * \endverbatim
   */
  EVALUE(MACRO_BV_CONCAT_EXTRACT_MERGE),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Bitvectors -- Macro concat constant merge **
   *
   * .. math::
   *
   *    a = b
   *
   * where :math:`a` is rewritten to :math:`b` by the internal rewrite
   * rule ConcatConstantMerge.
   *
   * \endverbatim
   */
  EVALUE(MACRO_BV_CONCAT_CONSTANT_MERGE),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Bitvectors -- Macro equality solve**
   *
   * .. math::
   *
   *    (a = b) = \bot
   *
   * where :math:`bvsub(a,b)` normalizes to a non-zero constant, or
   * alternatively
   *
   * .. math::
   *
   *    (a = b) = \top
   *
   * where :math:`bvsub(a,b)` normalizes to zero.
   *
   * \endverbatim
   */
  EVALUE(MACRO_BV_EQ_SOLVE),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Bitvectors -- Unsigned multiplication overflow detection elimination**
   *
   * .. math::
   *
   *    \texttt{bvumulo}(x,y) = t
   *
   * where :math:`t` is the result of eliminating the application
   * of :math:`\texttt{bvumulo}`.
   *
   * See M.Gok, M.J. Schulte, P.I. Balzola, "Efficient integer multiplication
   * overflow detection circuits", 2001.
   * http://ieeexplore.ieee.org/document/987767
   * \endverbatim
   */
  EVALUE(BV_UMULO_ELIM),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Bitvectors -- Unsigned multiplication overflow detection elimination**
   *
   * .. math::
   *
   *    \texttt{bvsmulo}(x,y) = t
   *
   * where :math:`t` is the result of eliminating the application
   * of :math:`\texttt{bvsmulo}`.
   *
   * See M.Gok, M.J. Schulte, P.I. Balzola, "Efficient integer multiplication
   * overflow detection circuits", 2001.
   * http://ieeexplore.ieee.org/document/987767
   * \endverbatim
   */
  EVALUE(BV_SMULO_ELIM),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Bitvectors -- Extract continuous substrings of bitvectors**
   *
   * .. math::
   *
   *    bvand(a,\ c) = concat(bvand(a[i_0:j_0],\ c_0) ... bvand(a[i_n:j_n],\ c_n))
   *
   * where c0,..., cn are maximally continuous substrings of 0 or 1 in the
   * constant c
   * \endverbatim
   */
  EVALUE(BV_BITWISE_SLICING),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Bitvectors -- Extract continuous substrings of bitvectors**
   *
   * .. math::
   *
   *    repeat(n,\ t) = concat(t ... t)
   *
   * where :math:`t` is repeated :math:`n` times.
   * \endverbatim
   */
  EVALUE(BV_REPEAT_ELIM),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- String contains multiset subset**
   *
   * .. math::
   *
   *    \mathit{str}.contains(s,t) = \bot
   *
   * where the multiset overapproximation of :math:`s` can be shown to not
   * contain the multiset abstraction of :math:`t` based on the reasoning
   * described in the paper Reynolds et al, CAV 2019, "High-Level Abstractions
   * for Simplifying Extended String Constraints in SMT".
   * \endverbatim
   */
  EVALUE(STR_CTN_MULTISET_SUBSET),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- String equality length unify prefix**
   *
   * .. math::
   *
   *    (s = \mathit{str}.\text{++}(t_1, \ldots, t_n)) = 
   *    (s = \mathit{str}.\text{++}(t_1, \ldots t_i)) \wedge
   *    t_{i+1} = \epsilon \wedge \ldots \wedge t_n = \epsilon
   *
   * where we can show :math:`s` has a length that is at least the length
   * of :math:`\text{++}(t_1, \ldots t_i)`.
   * \endverbatim
   */
  EVALUE(MACRO_STR_EQ_LEN_UNIFY_PREFIX),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- String equality length unify**
   *
   * .. math::
   *
   *    (\mathit{str}.\text{++}(s_1, \ldots, s_n) = \mathit{str}.\text{++}(t_1, \ldots, t_m)) =
   *    (r_1 = u_1 \wedge \ldots r_k = u_k)
   *
   * where for each :math:`i = 1, \ldots, k`, we can show the length of
   * :math:`r_i` and :math:`u_i` are equal,
   * :math:`s_1, \ldots, s_n` is :math:`r_1, \ldots, r_k`, and
   * :math:`t_1, \ldots, t_m` is :math:`u_1, \ldots, u_k`.
   * \endverbatim
   */
  EVALUE(MACRO_STR_EQ_LEN_UNIFY),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- Macro string split contains**
   *
   * .. math::
   *
   *   \mathit{str.contains}(t, s) =
   *   \mathit{str.contains}(t_1, s) \vee \mathit{str.contains}(t_2, s)
   *
   * where :math:`t_1` and :math:`t_2` are substrings of :math:`t`. This
   * rule is elaborated using
   * :cpp:enumerator:`STR_OVERLAP_SPLIT_CTN <cvc5::ProofRewriteRule::STR_OVERLAP_SPLIT_CTN>`.
   *
   * \endverbatim
   */
  EVALUE(MACRO_STR_SPLIT_CTN),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- Macro string strip endpoints**
   *
   * One of the following forms:
   *
   * .. math::
   *
   *   \mathit{str.contains}(t, s) = \mathit{str.contains}(t_2, s)
   *
   * .. math::
   *
   *   \mathit{str.indexof}(t, s, n) = \mathit{str.indexof}(t_2, s, n)
   *
   * .. math::
   *
   *   \mathit{str.replace}(t, s, r) =
   *   \mathit{str.++}(t_1, \mathit{str.replace}(t_2, s, r) t_3)
   *
   * where in each case we reason about removing portions of :math:`t`
   * that are irrelevant to the evaluation of the term. This rule
   * is elaborated  using
   * :cpp:enumerator:`STR_OVERLAP_ENDPOINTS_CTN <cvc5::ProofRewriteRule::STR_OVERLAP_ENDPOINTS_CTN>`,
   * :cpp:enumerator:`STR_OVERLAP_ENDPOINTS_INDEXOF <cvc5::ProofRewriteRule::STR_OVERLAP_ENDPOINTS_INDEXOF>` and
   * :cpp:enumerator:`STR_OVERLAP_ENDPOINTS_REPLACE <cvc5::ProofRewriteRule::STR_OVERLAP_ENDPOINTS_REPLACE>`.
   *
   * \endverbatim
   */
  EVALUE(MACRO_STR_STRIP_ENDPOINTS),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- Strings overlap split contains**
   *
   * .. math::
   *
   *   \mathit{str.contains}(\mathit{str.++}(t_1, t_2, t_3), s) =
   *   \mathit{str.contains}(t_1, s) \vee \mathit{str.contains}(t_3, s)
   *
   * :math:`t_2` has no forward overlap with :math:`s` and :math:`s` has no
   * forward overlap with :math:`t_2`. For details see
   * :math:`\texttt{Word::hasOverlap}` in :cvc5src:`theory/strings/word.h`.
   * \endverbatim
   */
  EVALUE(STR_OVERLAP_SPLIT_CTN),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- Strings overlap endpoints contains**
   *
   * .. math::
   *
   *   \mathit{str.contains}(\mathit{str.++}(t_1, t_2, t_3), s) =
   *   \mathit{str.contains}(t_2, s)
   *
   * where :math:`s` is `:math:\mathit{str.++}(s_1, s_2, s_3)`,
   * :math:`t_1` has no forward overlap with :math:`s_1` and
   * :math:`t_3` has no reverse overlap with :math:`s_3`.
   * For details see :math:`\texttt{Word::hasOverlap}` in
   * :cvc5src:`theory/strings/word.h`.
   *
   * \endverbatim
   */
  EVALUE(STR_OVERLAP_ENDPOINTS_CTN),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- Strings overlap endpoints indexof**
   *
   * .. math::
   *
   *   \mathit{str.indexof}(\mathit{str.++}(t_1, t_2), s, n) =
   *   \mathit{str.indexof}(t_1, s, n)
   *
   * where :math:`s` is `:math:\mathit{str.++}(s_1, s_2)` and
   * :math:`t_2` has no reverse overlap with :math:`s_2`.
   * For details see :math:`\texttt{Word::hasOverlap}` in
   * :cvc5src:`theory/strings/word.h`.
   * \endverbatim
   */
  EVALUE(STR_OVERLAP_ENDPOINTS_INDEXOF),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- Strings overlap endpoints replace**
   *
   * .. math::
   *
   *   \mathit{str.replace}(\mathit{str.++}(t_1, t_2, t_3), s, r) =
   *   \mathit{str.++}(t_1, \mathit{str.replace}(t_2, s, r) t_3)
   *
   * where :math:`s` is `:math:\mathit{str.++}(s_1, s_2, s_3)`,
   * :math:`t_1` has no forward overlap with :math:`s_1` and
   * :math:`t_3` has no reverse overlap with :math:`s_3`.
   * For details see :math:`\texttt{Word::hasOverlap}` in
   * :cvc5src:`theory/strings/word.h`.
   *
   * \endverbatim
   */
  EVALUE(STR_OVERLAP_ENDPOINTS_REPLACE),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- Macro string component contains**
   *
   * .. math::
   *
   *   \mathit{str.contains}(t, s) = \top
   *
   * where a substring of :math:`t` can be inferred to be a superstring of
   * :math:`s` based on iterating on components of string concatenation terms
   * as well as prefix and suffix reasoning.
   *
   * \endverbatim
   */
  EVALUE(MACRO_STR_COMPONENT_CTN),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- Macro string constant no contains concatenation**
   *
   * .. math::
   *
   *   \mathit{str.contains}(c, \mathit{str.++}(t_1, \ldots, t_n)) = \bot
   *
   * where :math:`c` is not contained in :math:`R_t`, where
   * the regular expression :math:`R_t` overapproximates the possible
   * values of :math:`\mathit{str.++}(t_1, \ldots, t_n)`.
   *
   * \endverbatim
   */
  EVALUE(MACRO_STR_CONST_NCTN_CONCAT),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- Macro string in regular expression inclusion**
   *
   * .. math::
   *
   *   \mathit{str.in_re}(s, R) = \top
   *
   * where :math:`R` includes the regular expression :math:`R_s`
   * which overapproximates the possible values of string :math:`s`.
   *
   * \endverbatim
   */
  EVALUE(MACRO_STR_IN_RE_INCLUSION),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- Macro regular expression intersection/union constant elimination**
   *
   * One of the following forms:
   *
   * .. math::
   *
   *   \mathit{re.union}(R) = \mathit{re.union}(R')
   *
   * where :math:`R` is a list of regular expressions containing :math:`R_i`
   * and :math:`\mathit{str.to_re(c)}` where :math:`c` is a string in :math:`R_i`
   * and :math:`R'` is the result of removing :math:`\mathit{str.to_re(c)}` from :math:`R`.
   *
   * .. math::
   *
   *   \mathit{re.inter}(R) = \mathit{re.inter}(R')
   *
   * where :math:`R` is a list of regular expressions containing :math:`R_i`
   * and :math:`\mathit{str.to_re(c)}` where :math:`c` is a string in :math:`R_i`
   * and :math:`R'` is the result of removing :math:`R_i` from :math:`R`.
   *
   * .. math::
   *
   *   \mathit{re.inter}(R) = \mathit{re.none}
   *
   * where :math:`R` is a list of regular expressions containing :math:`R_i`
   * and :math:`\mathit{str.to_re(c)}` where :math:`c` is a string not in :math:`R_i`.
   *
   * \endverbatim
   */
  EVALUE(MACRO_RE_INTER_UNION_CONST_ELIM),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- Sequence evaluate operator**
   *
   * .. math::
   *
   *    f(s_1, \ldots, s_n) = t
   *
   * where :math:`f` is an operator over sequences and :math:`s_1, \ldots, s_n`
   * are values, that is, the Node::isConst method returns true for each, and
   * :math:`t` is the result of evaluating :math:`f` on them.
   * \endverbatim
   */
  EVALUE(SEQ_EVAL_OP),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- string indexof regex evaluation**
   *
   * .. math::
   *
   *   str.indexof\_re(s,r,n) = m
   *
   * where :math:`s` is a string values, :math:`n` is an integer value, :math:`r` is a
   * ground regular expression and :math:`m` is the result of evaluating the left hand
   * side.
   *
   * \endverbatim
   */
  EVALUE(STR_INDEXOF_RE_EVAL),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- string replace regex evaluation**
   *
   * .. math::
   *
   *   str.replace\_re(s,r,t) = u
   *
   * where :math:`s,t` are string values, :math:`r` is a ground regular expression
   * and :math:`u` is the result of evaluating the left hand side.
   *
   * \endverbatim
   */
  EVALUE(STR_REPLACE_RE_EVAL),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- string replace regex all evaluation**
   *
   * .. math::
   *
   *   str.replace\_re\_all(s,r,t) = u
   *
   * where :math:`s,t` are string values, :math:`r` is a ground regular expression
   * and :math:`u` is the result of evaluating the left hand side.
   *
   * \endverbatim
   */
  EVALUE(STR_REPLACE_RE_ALL_EVAL),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- regular expression loop elimination**
   *
   * .. math::
   *
   *   re.loop_{l,u}(R) = re.union(R^l, \ldots, R^u)
   *
   * where :math:`u \geq l`.
   *
   * \endverbatim
   */
  EVALUE(RE_LOOP_ELIM),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- regular expression intersection/union inclusion**
   *
   * .. math::
   *
   *   \mathit{re.inter}(R) = \mathit{re.inter}(\mathit{re.none}, R_0)
   *
   * where :math:`R` is a list of regular expressions containing `r_1`,
   * `re.comp(r_2)` and the list :math:`R_0` where `r_2` is a superset of
   * `r_1`.
   *
   * or alternatively:
   *
   * .. math::
   *
   *   \mathit{re.union}(R) = \mathit{re.union}(\mathit{re}.\text{*}(\mathit{re.allchar}),\ R_0)
   *
   * where :math:`R` is a list of regular expressions containing `r_1`,
   * `re.comp(r_2)` and the list :math:`R_0`, where `r_1` is a superset of
   * `r_2`.
   *
   * \endverbatim
   */
  EVALUE(MACRO_RE_INTER_UNION_INCLUSION),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- regular expression intersection inclusion**
   *
   * .. math::
   *
   *   \mathit{re.inter}(r_1, re.comp(r_2)) = \mathit{re.none}
   *
   * where :math:`r_2` is a superset of :math:`r_1`.
   *
   * \endverbatim
   */
  EVALUE(RE_INTER_INCLUSION),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- regular expression union inclusion**
   *
   * .. math::
   *
   *   \mathit{re.union}(r_1, re.comp(r_2)) = \mathit{re}.\text{*}(\mathit{re.allchar})
   *
   * where :math:`r_1` is a superset of :math:`r_2`.
   *
   * \endverbatim
   */
  EVALUE(RE_UNION_INCLUSION),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- regular expression membership evaluation**
   *
   * .. math::
   *
   *   \mathit{str.in\_re}(s, R) = c
   *
   * where :math:`s` is a constant string, :math:`R` is a constant regular
   * expression and :math:`c` is true or false.
   *
   * \endverbatim
   */
  EVALUE(STR_IN_RE_EVAL),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- regular expression membership consume**
   *
   * .. math::
   *
   *   \mathit{str.in_re}(s, R) = b
   *
   * where :math:`b` is either :math:`false` or the result of stripping
   * entailed prefixes and suffixes off of :math:`s` and :math:`R`.
   *
   * \endverbatim
   */
  EVALUE(STR_IN_RE_CONSUME),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- string in regular expression concatenation star character**
   *
   * .. math::
   *
   *   \mathit{str.in\_re}(\mathit{str}.\text{++}(s_1, \ldots, s_n), \mathit{re}.\text{*}(R)) =\\ \mathit{str.in\_re}(s_1, \mathit{re}.\text{*}(R)) \wedge \ldots \wedge \mathit{str.in\_re}(s_n, \mathit{re}.\text{*}(R))
   *
   * where all strings in :math:`R` have length one.
   *
   * \endverbatim
   */
  EVALUE(STR_IN_RE_CONCAT_STAR_CHAR),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- string in regular expression sigma**
   *
   * .. math::
   *
   *   \mathit{str.in\_re}(s, \mathit{re}.\text{++}(\mathit{re.allchar}, \ldots, \mathit{re.allchar})) = (\mathit{str.len}(s) = n)
   *
   * or alternatively:
   *
   * .. math::
   *
   *   \mathit{str.in\_re}(s, \mathit{re}.\text{++}(\mathit{re.allchar}, \ldots, \mathit{re.allchar}, \mathit{re}.\text{*}(\mathit{re.allchar}))) = (\mathit{str.len}(s) \ge n)
   *
   * \endverbatim
   */
  EVALUE(STR_IN_RE_SIGMA),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- string in regular expression sigma star**
   *
   * .. math::
   *
   *   \mathit{str.in\_re}(s, \mathit{re}.\text{*}(\mathit{re}.\text{++}(\mathit{re.allchar}, \ldots, \mathit{re.allchar}))) = (\mathit{str.len}(s) \ \% \ n = 0)
   *
   * where :math:`n` is the number of :math:`\mathit{re.allchar}` arguments to
   * :math:`\mathit{re}.\text{++}`.
   *
   * \endverbatim
   */
  EVALUE(STR_IN_RE_SIGMA_STAR),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Strings -- strings substring strip symbolic length**
   *
   * .. math::
   *
   *   str.substr(s, n, m) = t
   *
   * where :math:`t` is obtained by fully or partially stripping components of
   * :math:`s` based on :math:`n` and :math:`m`.
   *
   * \endverbatim
   */
  EVALUE(MACRO_SUBSTR_STRIP_SYM_LENGTH),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Sets -- sets evaluate operator**
   *
   * .. math::
   *
   *   \mathit{f}(t_1, t_2) = t
   *
   * where :math:`f` is one of :math:`\mathit{set.inter}, \mathit{set.minus}, \mathit{set.union}`,
   * and :math:`t` is the result of evaluating :math:`f` on
   * :math:`t_1` and :math:`t_2`.
   *
   * Note we use this rule only when :math:`t_1` and :math:`t_2` are set values,
   * that is, the Node::isConst method returns true for both.
   *
   * \endverbatim
   */
  EVALUE(SETS_EVAL_OP),
  /**
   * \verbatim embed:rst:leading-asterisk
   * **Sets -- sets insert elimination**
   *
   * .. math::
   *
   *   \mathit{set.insert}(t_1, \ldots, t_n, S) = \texttt{set.union}(\texttt{sets.singleton}(t_1), \ldots, \texttt{sets.singleton}(t_n), S)
   *
   * \endverbatim
   */
  EVALUE(SETS_INSERT_ELIM),
  // RARE rules
  // ${rules}$
  /** Auto-generated from RARE rule arith-div-total-zero-real */
  EVALUE(ARITH_DIV_TOTAL_ZERO_REAL),
  /** Auto-generated from RARE rule arith-div-total-zero-int */
  EVALUE(ARITH_DIV_TOTAL_ZERO_INT),
  /** Auto-generated from RARE rule arith-int-div-total */
  EVALUE(ARITH_INT_DIV_TOTAL),
  /** Auto-generated from RARE rule arith-int-div-total-one */
  EVALUE(ARITH_INT_DIV_TOTAL_ONE),
  /** Auto-generated from RARE rule arith-int-div-total-zero */
  EVALUE(ARITH_INT_DIV_TOTAL_ZERO),
  /** Auto-generated from RARE rule arith-int-div-total-neg */
  EVALUE(ARITH_INT_DIV_TOTAL_NEG),
  /** Auto-generated from RARE rule arith-int-mod-total */
  EVALUE(ARITH_INT_MOD_TOTAL),
  /** Auto-generated from RARE rule arith-int-mod-total-one */
  EVALUE(ARITH_INT_MOD_TOTAL_ONE),
  /** Auto-generated from RARE rule arith-int-mod-total-zero */
  EVALUE(ARITH_INT_MOD_TOTAL_ZERO),
  /** Auto-generated from RARE rule arith-int-mod-total-neg */
  EVALUE(ARITH_INT_MOD_TOTAL_NEG),
  /** Auto-generated from RARE rule arith-elim-gt */
  EVALUE(ARITH_ELIM_GT),
  /** Auto-generated from RARE rule arith-elim-lt */
  EVALUE(ARITH_ELIM_LT),
  /** Auto-generated from RARE rule arith-elim-int-gt */
  EVALUE(ARITH_ELIM_INT_GT),
  /** Auto-generated from RARE rule arith-elim-int-lt */
  EVALUE(ARITH_ELIM_INT_LT),
  /** Auto-generated from RARE rule arith-elim-leq */
  EVALUE(ARITH_ELIM_LEQ),
  /** Auto-generated from RARE rule arith-leq-norm */
  EVALUE(ARITH_LEQ_NORM),
  /** Auto-generated from RARE rule arith-geq-tighten */
  EVALUE(ARITH_GEQ_TIGHTEN),
  /** Auto-generated from RARE rule arith-geq-norm1-int */
  EVALUE(ARITH_GEQ_NORM1_INT),
  /** Auto-generated from RARE rule arith-geq-norm1-real */
  EVALUE(ARITH_GEQ_NORM1_REAL),
  /** Auto-generated from RARE rule arith-eq-elim-real */
  EVALUE(ARITH_EQ_ELIM_REAL),
  /** Auto-generated from RARE rule arith-eq-elim-int */
  EVALUE(ARITH_EQ_ELIM_INT),
  /** Auto-generated from RARE rule arith-to-int-elim */
  EVALUE(ARITH_TO_INT_ELIM),
  /** Auto-generated from RARE rule arith-to-int-elim-to-real */
  EVALUE(ARITH_TO_INT_ELIM_TO_REAL),
  /** Auto-generated from RARE rule arith-div-elim-to-real1 */
  EVALUE(ARITH_DIV_ELIM_TO_REAL1),
  /** Auto-generated from RARE rule arith-div-elim-to-real2 */
  EVALUE(ARITH_DIV_ELIM_TO_REAL2),
  /** Auto-generated from RARE rule arith-mod-over-mod */
  EVALUE(ARITH_MOD_OVER_MOD),
  /** Auto-generated from RARE rule arith-int-eq-conflict */
  EVALUE(ARITH_INT_EQ_CONFLICT),
  /** Auto-generated from RARE rule arith-int-geq-tighten */
  EVALUE(ARITH_INT_GEQ_TIGHTEN),
  /** Auto-generated from RARE rule arith-divisible-elim */
  EVALUE(ARITH_DIVISIBLE_ELIM),
  /** Auto-generated from RARE rule arith-abs-eq */
  EVALUE(ARITH_ABS_EQ),
  /** Auto-generated from RARE rule arith-abs-int-gt */
  EVALUE(ARITH_ABS_INT_GT),
  /** Auto-generated from RARE rule arith-abs-real-gt */
  EVALUE(ARITH_ABS_REAL_GT),
  /** Auto-generated from RARE rule arith-geq-ite-lift */
  EVALUE(ARITH_GEQ_ITE_LIFT),
  /** Auto-generated from RARE rule arith-leq-ite-lift */
  EVALUE(ARITH_LEQ_ITE_LIFT),
  /** Auto-generated from RARE rule arith-min-lt1 */
  EVALUE(ARITH_MIN_LT1),
  /** Auto-generated from RARE rule arith-min-lt2 */
  EVALUE(ARITH_MIN_LT2),
  /** Auto-generated from RARE rule arith-max-geq1 */
  EVALUE(ARITH_MAX_GEQ1),
  /** Auto-generated from RARE rule arith-max-geq2 */
  EVALUE(ARITH_MAX_GEQ2),
  /** Auto-generated from RARE rule array-read-over-write */
  EVALUE(ARRAY_READ_OVER_WRITE),
  /** Auto-generated from RARE rule array-read-over-write2 */
  EVALUE(ARRAY_READ_OVER_WRITE2),
  /** Auto-generated from RARE rule array-store-overwrite */
  EVALUE(ARRAY_STORE_OVERWRITE),
  /** Auto-generated from RARE rule array-store-self */
  EVALUE(ARRAY_STORE_SELF),
  /** Auto-generated from RARE rule array-read-over-write-split */
  EVALUE(ARRAY_READ_OVER_WRITE_SPLIT),
  /** Auto-generated from RARE rule array-store-swap */
  EVALUE(ARRAY_STORE_SWAP),
  /** Auto-generated from RARE rule bool-double-not-elim */
  EVALUE(BOOL_DOUBLE_NOT_ELIM),
  /** Auto-generated from RARE rule bool-not-true */
  EVALUE(BOOL_NOT_TRUE),
  /** Auto-generated from RARE rule bool-not-false */
  EVALUE(BOOL_NOT_FALSE),
  /** Auto-generated from RARE rule bool-eq-true */
  EVALUE(BOOL_EQ_TRUE),
  /** Auto-generated from RARE rule bool-eq-false */
  EVALUE(BOOL_EQ_FALSE),
  /** Auto-generated from RARE rule bool-eq-nrefl */
  EVALUE(BOOL_EQ_NREFL),
  /** Auto-generated from RARE rule bool-impl-false1 */
  EVALUE(BOOL_IMPL_FALSE1),
  /** Auto-generated from RARE rule bool-impl-false2 */
  EVALUE(BOOL_IMPL_FALSE2),
  /** Auto-generated from RARE rule bool-impl-true1 */
  EVALUE(BOOL_IMPL_TRUE1),
  /** Auto-generated from RARE rule bool-impl-true2 */
  EVALUE(BOOL_IMPL_TRUE2),
  /** Auto-generated from RARE rule bool-impl-elim */
  EVALUE(BOOL_IMPL_ELIM),
  /** Auto-generated from RARE rule bool-dual-impl-eq */
  EVALUE(BOOL_DUAL_IMPL_EQ),
  /** Auto-generated from RARE rule bool-and-conf */
  EVALUE(BOOL_AND_CONF),
  /** Auto-generated from RARE rule bool-and-conf2 */
  EVALUE(BOOL_AND_CONF2),
  /** Auto-generated from RARE rule bool-or-taut */
  EVALUE(BOOL_OR_TAUT),
  /** Auto-generated from RARE rule bool-or-taut2 */
  EVALUE(BOOL_OR_TAUT2),
  /** Auto-generated from RARE rule bool-or-de-morgan */
  EVALUE(BOOL_OR_DE_MORGAN),
  /** Auto-generated from RARE rule bool-implies-de-morgan */
  EVALUE(BOOL_IMPLIES_DE_MORGAN),
  /** Auto-generated from RARE rule bool-and-de-morgan */
  EVALUE(BOOL_AND_DE_MORGAN),
  /** Auto-generated from RARE rule bool-or-and-distrib */
  EVALUE(BOOL_OR_AND_DISTRIB),
  /** Auto-generated from RARE rule bool-implies-or-distrib */
  EVALUE(BOOL_IMPLIES_OR_DISTRIB),
  /** Auto-generated from RARE rule bool-xor-refl */
  EVALUE(BOOL_XOR_REFL),
  /** Auto-generated from RARE rule bool-xor-nrefl */
  EVALUE(BOOL_XOR_NREFL),
  /** Auto-generated from RARE rule bool-xor-false */
  EVALUE(BOOL_XOR_FALSE),
  /** Auto-generated from RARE rule bool-xor-true */
  EVALUE(BOOL_XOR_TRUE),
  /** Auto-generated from RARE rule bool-xor-comm */
  EVALUE(BOOL_XOR_COMM),
  /** Auto-generated from RARE rule bool-xor-elim */
  EVALUE(BOOL_XOR_ELIM),
  /** Auto-generated from RARE rule bool-not-xor-elim */
  EVALUE(BOOL_NOT_XOR_ELIM),
  /** Auto-generated from RARE rule bool-not-eq-elim1 */
  EVALUE(BOOL_NOT_EQ_ELIM1),
  /** Auto-generated from RARE rule bool-not-eq-elim2 */
  EVALUE(BOOL_NOT_EQ_ELIM2),
  /** Auto-generated from RARE rule ite-neg-branch */
  EVALUE(ITE_NEG_BRANCH),
  /** Auto-generated from RARE rule ite-then-true */
  EVALUE(ITE_THEN_TRUE),
  /** Auto-generated from RARE rule ite-else-false */
  EVALUE(ITE_ELSE_FALSE),
  /** Auto-generated from RARE rule ite-then-false */
  EVALUE(ITE_THEN_FALSE),
  /** Auto-generated from RARE rule ite-else-true */
  EVALUE(ITE_ELSE_TRUE),
  /** Auto-generated from RARE rule ite-then-lookahead-self */
  EVALUE(ITE_THEN_LOOKAHEAD_SELF),
  /** Auto-generated from RARE rule ite-else-lookahead-self */
  EVALUE(ITE_ELSE_LOOKAHEAD_SELF),
  /** Auto-generated from RARE rule ite-then-lookahead-not-self */
  EVALUE(ITE_THEN_LOOKAHEAD_NOT_SELF),
  /** Auto-generated from RARE rule ite-else-lookahead-not-self */
  EVALUE(ITE_ELSE_LOOKAHEAD_NOT_SELF),
  /** Auto-generated from RARE rule ite-expand */
  EVALUE(ITE_EXPAND),
  /** Auto-generated from RARE rule bool-not-ite-elim */
  EVALUE(BOOL_NOT_ITE_ELIM),
  /** Auto-generated from RARE rule ite-true-cond */
  EVALUE(ITE_TRUE_COND),
  /** Auto-generated from RARE rule ite-false-cond */
  EVALUE(ITE_FALSE_COND),
  /** Auto-generated from RARE rule ite-not-cond */
  EVALUE(ITE_NOT_COND),
  /** Auto-generated from RARE rule ite-eq-branch */
  EVALUE(ITE_EQ_BRANCH),
  /** Auto-generated from RARE rule ite-then-lookahead */
  EVALUE(ITE_THEN_LOOKAHEAD),
  /** Auto-generated from RARE rule ite-else-lookahead */
  EVALUE(ITE_ELSE_LOOKAHEAD),
  /** Auto-generated from RARE rule ite-then-neg-lookahead */
  EVALUE(ITE_THEN_NEG_LOOKAHEAD),
  /** Auto-generated from RARE rule ite-else-neg-lookahead */
  EVALUE(ITE_ELSE_NEG_LOOKAHEAD),
  /** Auto-generated from RARE rule bv-concat-extract-merge */
  EVALUE(BV_CONCAT_EXTRACT_MERGE),
  /** Auto-generated from RARE rule bv-extract-extract */
  EVALUE(BV_EXTRACT_EXTRACT),
  /** Auto-generated from RARE rule bv-extract-whole */
  EVALUE(BV_EXTRACT_WHOLE),
  /** Auto-generated from RARE rule bv-extract-concat-1 */
  EVALUE(BV_EXTRACT_CONCAT_1),
  /** Auto-generated from RARE rule bv-extract-concat-2 */
  EVALUE(BV_EXTRACT_CONCAT_2),
  /** Auto-generated from RARE rule bv-extract-concat-3 */
  EVALUE(BV_EXTRACT_CONCAT_3),
  /** Auto-generated from RARE rule bv-extract-concat-4 */
  EVALUE(BV_EXTRACT_CONCAT_4),
  /** Auto-generated from RARE rule bv-eq-extract-elim1 */
  EVALUE(BV_EQ_EXTRACT_ELIM1),
  /** Auto-generated from RARE rule bv-eq-extract-elim2 */
  EVALUE(BV_EQ_EXTRACT_ELIM2),
  /** Auto-generated from RARE rule bv-eq-extract-elim3 */
  EVALUE(BV_EQ_EXTRACT_ELIM3),
  /** Auto-generated from RARE rule bv-extract-not */
  EVALUE(BV_EXTRACT_NOT),
  /** Auto-generated from RARE rule bv-extract-sign-extend-1 */
  EVALUE(BV_EXTRACT_SIGN_EXTEND_1),
  /** Auto-generated from RARE rule bv-extract-sign-extend-2 */
  EVALUE(BV_EXTRACT_SIGN_EXTEND_2),
  /** Auto-generated from RARE rule bv-extract-sign-extend-3 */
  EVALUE(BV_EXTRACT_SIGN_EXTEND_3),
  /** Auto-generated from RARE rule bv-not-xor */
  EVALUE(BV_NOT_XOR),
  /** Auto-generated from RARE rule bv-and-simplify-1 */
  EVALUE(BV_AND_SIMPLIFY_1),
  /** Auto-generated from RARE rule bv-and-simplify-2 */
  EVALUE(BV_AND_SIMPLIFY_2),
  /** Auto-generated from RARE rule bv-or-simplify-1 */
  EVALUE(BV_OR_SIMPLIFY_1),
  /** Auto-generated from RARE rule bv-or-simplify-2 */
  EVALUE(BV_OR_SIMPLIFY_2),
  /** Auto-generated from RARE rule bv-xor-simplify-1 */
  EVALUE(BV_XOR_SIMPLIFY_1),
  /** Auto-generated from RARE rule bv-xor-simplify-2 */
  EVALUE(BV_XOR_SIMPLIFY_2),
  /** Auto-generated from RARE rule bv-xor-simplify-3 */
  EVALUE(BV_XOR_SIMPLIFY_3),
  /** Auto-generated from RARE rule bv-ult-add-one */
  EVALUE(BV_ULT_ADD_ONE),
  /** Auto-generated from RARE rule bv-mult-slt-mult-1 */
  EVALUE(BV_MULT_SLT_MULT_1),
  /** Auto-generated from RARE rule bv-mult-slt-mult-2 */
  EVALUE(BV_MULT_SLT_MULT_2),
  /** Auto-generated from RARE rule bv-commutative-xor */
  EVALUE(BV_COMMUTATIVE_XOR),
  /** Auto-generated from RARE rule bv-commutative-comp */
  EVALUE(BV_COMMUTATIVE_COMP),
  /** Auto-generated from RARE rule bv-zero-extend-eliminate-0 */
  EVALUE(BV_ZERO_EXTEND_ELIMINATE_0),
  /** Auto-generated from RARE rule bv-sign-extend-eliminate-0 */
  EVALUE(BV_SIGN_EXTEND_ELIMINATE_0),
  /** Auto-generated from RARE rule bv-not-neq */
  EVALUE(BV_NOT_NEQ),
  /** Auto-generated from RARE rule bv-ult-ones */
  EVALUE(BV_ULT_ONES),
  /** Auto-generated from RARE rule bv-concat-merge-const */
  EVALUE(BV_CONCAT_MERGE_CONST),
  /** Auto-generated from RARE rule bv-commutative-add */
  EVALUE(BV_COMMUTATIVE_ADD),
  /** Auto-generated from RARE rule bv-sub-eliminate */
  EVALUE(BV_SUB_ELIMINATE),
  /** Auto-generated from RARE rule bv-ite-width-one */
  EVALUE(BV_ITE_WIDTH_ONE),
  /** Auto-generated from RARE rule bv-ite-width-one-not */
  EVALUE(BV_ITE_WIDTH_ONE_NOT),
  /** Auto-generated from RARE rule bv-eq-xor-solve */
  EVALUE(BV_EQ_XOR_SOLVE),
  /** Auto-generated from RARE rule bv-eq-not-solve */
  EVALUE(BV_EQ_NOT_SOLVE),
  /** Auto-generated from RARE rule bv-ugt-eliminate */
  EVALUE(BV_UGT_ELIMINATE),
  /** Auto-generated from RARE rule bv-uge-eliminate */
  EVALUE(BV_UGE_ELIMINATE),
  /** Auto-generated from RARE rule bv-sgt-eliminate */
  EVALUE(BV_SGT_ELIMINATE),
  /** Auto-generated from RARE rule bv-sge-eliminate */
  EVALUE(BV_SGE_ELIMINATE),
  /** Auto-generated from RARE rule bv-sle-eliminate */
  EVALUE(BV_SLE_ELIMINATE),
  /** Auto-generated from RARE rule bv-redor-eliminate */
  EVALUE(BV_REDOR_ELIMINATE),
  /** Auto-generated from RARE rule bv-redand-eliminate */
  EVALUE(BV_REDAND_ELIMINATE),
  /** Auto-generated from RARE rule bv-ule-eliminate */
  EVALUE(BV_ULE_ELIMINATE),
  /** Auto-generated from RARE rule bv-comp-eliminate */
  EVALUE(BV_COMP_ELIMINATE),
  /** Auto-generated from RARE rule bv-rotate-left-eliminate-1 */
  EVALUE(BV_ROTATE_LEFT_ELIMINATE_1),
  /** Auto-generated from RARE rule bv-rotate-left-eliminate-2 */
  EVALUE(BV_ROTATE_LEFT_ELIMINATE_2),
  /** Auto-generated from RARE rule bv-rotate-right-eliminate-1 */
  EVALUE(BV_ROTATE_RIGHT_ELIMINATE_1),
  /** Auto-generated from RARE rule bv-rotate-right-eliminate-2 */
  EVALUE(BV_ROTATE_RIGHT_ELIMINATE_2),
  /** Auto-generated from RARE rule bv-nand-eliminate */
  EVALUE(BV_NAND_ELIMINATE),
  /** Auto-generated from RARE rule bv-nor-eliminate */
  EVALUE(BV_NOR_ELIMINATE),
  /** Auto-generated from RARE rule bv-xnor-eliminate */
  EVALUE(BV_XNOR_ELIMINATE),
  /** Auto-generated from RARE rule bv-sdiv-eliminate */
  EVALUE(BV_SDIV_ELIMINATE),
  /** Auto-generated from RARE rule bv-zero-extend-eliminate */
  EVALUE(BV_ZERO_EXTEND_ELIMINATE),
  /** Auto-generated from RARE rule bv-uaddo-eliminate */
  EVALUE(BV_UADDO_ELIMINATE),
  /** Auto-generated from RARE rule bv-saddo-eliminate */
  EVALUE(BV_SADDO_ELIMINATE),
  /** Auto-generated from RARE rule bv-sdivo-eliminate */
  EVALUE(BV_SDIVO_ELIMINATE),
  /** Auto-generated from RARE rule bv-smod-eliminate */
  EVALUE(BV_SMOD_ELIMINATE),
  /** Auto-generated from RARE rule bv-srem-eliminate */
  EVALUE(BV_SREM_ELIMINATE),
  /** Auto-generated from RARE rule bv-usubo-eliminate */
  EVALUE(BV_USUBO_ELIMINATE),
  /** Auto-generated from RARE rule bv-ssubo-eliminate */
  EVALUE(BV_SSUBO_ELIMINATE),
  /** Auto-generated from RARE rule bv-nego-eliminate */
  EVALUE(BV_NEGO_ELIMINATE),
  /** Auto-generated from RARE rule bv-ite-equal-children */
  EVALUE(BV_ITE_EQUAL_CHILDREN),
  /** Auto-generated from RARE rule bv-ite-const-children-1 */
  EVALUE(BV_ITE_CONST_CHILDREN_1),
  /** Auto-generated from RARE rule bv-ite-const-children-2 */
  EVALUE(BV_ITE_CONST_CHILDREN_2),
  /** Auto-generated from RARE rule bv-ite-equal-cond-1 */
  EVALUE(BV_ITE_EQUAL_COND_1),
  /** Auto-generated from RARE rule bv-ite-equal-cond-2 */
  EVALUE(BV_ITE_EQUAL_COND_2),
  /** Auto-generated from RARE rule bv-ite-equal-cond-3 */
  EVALUE(BV_ITE_EQUAL_COND_3),
  /** Auto-generated from RARE rule bv-ite-merge-then-if */
  EVALUE(BV_ITE_MERGE_THEN_IF),
  /** Auto-generated from RARE rule bv-ite-merge-else-if */
  EVALUE(BV_ITE_MERGE_ELSE_IF),
  /** Auto-generated from RARE rule bv-ite-merge-then-else */
  EVALUE(BV_ITE_MERGE_THEN_ELSE),
  /** Auto-generated from RARE rule bv-ite-merge-else-else */
  EVALUE(BV_ITE_MERGE_ELSE_ELSE),
  /** Auto-generated from RARE rule bv-shl-by-const-0 */
  EVALUE(BV_SHL_BY_CONST_0),
  /** Auto-generated from RARE rule bv-shl-by-const-1 */
  EVALUE(BV_SHL_BY_CONST_1),
  /** Auto-generated from RARE rule bv-shl-by-const-2 */
  EVALUE(BV_SHL_BY_CONST_2),
  /** Auto-generated from RARE rule bv-lshr-by-const-0 */
  EVALUE(BV_LSHR_BY_CONST_0),
  /** Auto-generated from RARE rule bv-lshr-by-const-1 */
  EVALUE(BV_LSHR_BY_CONST_1),
  /** Auto-generated from RARE rule bv-lshr-by-const-2 */
  EVALUE(BV_LSHR_BY_CONST_2),
  /** Auto-generated from RARE rule bv-ashr-by-const-0 */
  EVALUE(BV_ASHR_BY_CONST_0),
  /** Auto-generated from RARE rule bv-ashr-by-const-1 */
  EVALUE(BV_ASHR_BY_CONST_1),
  /** Auto-generated from RARE rule bv-ashr-by-const-2 */
  EVALUE(BV_ASHR_BY_CONST_2),
  /** Auto-generated from RARE rule bv-and-concat-pullup */
  EVALUE(BV_AND_CONCAT_PULLUP),
  /** Auto-generated from RARE rule bv-or-concat-pullup */
  EVALUE(BV_OR_CONCAT_PULLUP),
  /** Auto-generated from RARE rule bv-xor-concat-pullup */
  EVALUE(BV_XOR_CONCAT_PULLUP),
  /** Auto-generated from RARE rule bv-and-concat-pullup2 */
  EVALUE(BV_AND_CONCAT_PULLUP2),
  /** Auto-generated from RARE rule bv-or-concat-pullup2 */
  EVALUE(BV_OR_CONCAT_PULLUP2),
  /** Auto-generated from RARE rule bv-xor-concat-pullup2 */
  EVALUE(BV_XOR_CONCAT_PULLUP2),
  /** Auto-generated from RARE rule bv-and-concat-pullup3 */
  EVALUE(BV_AND_CONCAT_PULLUP3),
  /** Auto-generated from RARE rule bv-or-concat-pullup3 */
  EVALUE(BV_OR_CONCAT_PULLUP3),
  /** Auto-generated from RARE rule bv-xor-concat-pullup3 */
  EVALUE(BV_XOR_CONCAT_PULLUP3),
  /** Auto-generated from RARE rule bv-xor-duplicate */
  EVALUE(BV_XOR_DUPLICATE),
  /** Auto-generated from RARE rule bv-xor-ones */
  EVALUE(BV_XOR_ONES),
  /** Auto-generated from RARE rule bv-xor-not */
  EVALUE(BV_XOR_NOT),
  /** Auto-generated from RARE rule bv-not-idemp */
  EVALUE(BV_NOT_IDEMP),
  /** Auto-generated from RARE rule bv-ult-zero-1 */
  EVALUE(BV_ULT_ZERO_1),
  /** Auto-generated from RARE rule bv-ult-zero-2 */
  EVALUE(BV_ULT_ZERO_2),
  /** Auto-generated from RARE rule bv-ult-self */
  EVALUE(BV_ULT_SELF),
  /** Auto-generated from RARE rule bv-lt-self */
  EVALUE(BV_LT_SELF),
  /** Auto-generated from RARE rule bv-ule-self */
  EVALUE(BV_ULE_SELF),
  /** Auto-generated from RARE rule bv-ule-zero */
  EVALUE(BV_ULE_ZERO),
  /** Auto-generated from RARE rule bv-zero-ule */
  EVALUE(BV_ZERO_ULE),
  /** Auto-generated from RARE rule bv-sle-self */
  EVALUE(BV_SLE_SELF),
  /** Auto-generated from RARE rule bv-ule-max */
  EVALUE(BV_ULE_MAX),
  /** Auto-generated from RARE rule bv-not-ult */
  EVALUE(BV_NOT_ULT),
  /** Auto-generated from RARE rule bv-mult-pow2-1 */
  EVALUE(BV_MULT_POW2_1),
  /** Auto-generated from RARE rule bv-mult-pow2-2 */
  EVALUE(BV_MULT_POW2_2),
  /** Auto-generated from RARE rule bv-mult-pow2-2b */
  EVALUE(BV_MULT_POW2_2B),
  /** Auto-generated from RARE rule bv-extract-mult-leading-bit */
  EVALUE(BV_EXTRACT_MULT_LEADING_BIT),
  /** Auto-generated from RARE rule bv-udiv-pow2-not-one */
  EVALUE(BV_UDIV_POW2_NOT_ONE),
  /** Auto-generated from RARE rule bv-udiv-zero */
  EVALUE(BV_UDIV_ZERO),
  /** Auto-generated from RARE rule bv-udiv-one */
  EVALUE(BV_UDIV_ONE),
  /** Auto-generated from RARE rule bv-urem-pow2-not-one */
  EVALUE(BV_UREM_POW2_NOT_ONE),
  /** Auto-generated from RARE rule bv-urem-one */
  EVALUE(BV_UREM_ONE),
  /** Auto-generated from RARE rule bv-urem-self */
  EVALUE(BV_UREM_SELF),
  /** Auto-generated from RARE rule bv-shl-zero */
  EVALUE(BV_SHL_ZERO),
  /** Auto-generated from RARE rule bv-lshr-zero */
  EVALUE(BV_LSHR_ZERO),
  /** Auto-generated from RARE rule bv-ashr-zero */
  EVALUE(BV_ASHR_ZERO),
  /** Auto-generated from RARE rule bv-ugt-urem */
  EVALUE(BV_UGT_UREM),
  /** Auto-generated from RARE rule bv-ult-one */
  EVALUE(BV_ULT_ONE),
  /** Auto-generated from RARE rule bv-merge-sign-extend-1 */
  EVALUE(BV_MERGE_SIGN_EXTEND_1),
  /** Auto-generated from RARE rule bv-merge-sign-extend-2 */
  EVALUE(BV_MERGE_SIGN_EXTEND_2),
  /** Auto-generated from RARE rule bv-sign-extend-eq-const-1 */
  EVALUE(BV_SIGN_EXTEND_EQ_CONST_1),
  /** Auto-generated from RARE rule bv-sign-extend-eq-const-2 */
  EVALUE(BV_SIGN_EXTEND_EQ_CONST_2),
  /** Auto-generated from RARE rule bv-zero-extend-eq-const-1 */
  EVALUE(BV_ZERO_EXTEND_EQ_CONST_1),
  /** Auto-generated from RARE rule bv-zero-extend-eq-const-2 */
  EVALUE(BV_ZERO_EXTEND_EQ_CONST_2),
  /** Auto-generated from RARE rule bv-zero-extend-ult-const-1 */
  EVALUE(BV_ZERO_EXTEND_ULT_CONST_1),
  /** Auto-generated from RARE rule bv-zero-extend-ult-const-2 */
  EVALUE(BV_ZERO_EXTEND_ULT_CONST_2),
  /** Auto-generated from RARE rule bv-sign-extend-ult-const-1 */
  EVALUE(BV_SIGN_EXTEND_ULT_CONST_1),
  /** Auto-generated from RARE rule bv-sign-extend-ult-const-2 */
  EVALUE(BV_SIGN_EXTEND_ULT_CONST_2),
  /** Auto-generated from RARE rule bv-sign-extend-ult-const-3 */
  EVALUE(BV_SIGN_EXTEND_ULT_CONST_3),
  /** Auto-generated from RARE rule bv-sign-extend-ult-const-4 */
  EVALUE(BV_SIGN_EXTEND_ULT_CONST_4),
  /** Auto-generated from RARE rule sets-eq-singleton-emp */
  EVALUE(SETS_EQ_SINGLETON_EMP),
  /** Auto-generated from RARE rule sets-member-singleton */
  EVALUE(SETS_MEMBER_SINGLETON),
  /** Auto-generated from RARE rule sets-member-emp */
  EVALUE(SETS_MEMBER_EMP),
  /** Auto-generated from RARE rule sets-subset-elim */
  EVALUE(SETS_SUBSET_ELIM),
  /** Auto-generated from RARE rule sets-union-comm */
  EVALUE(SETS_UNION_COMM),
  /** Auto-generated from RARE rule sets-inter-comm */
  EVALUE(SETS_INTER_COMM),
  /** Auto-generated from RARE rule sets-inter-emp1 */
  EVALUE(SETS_INTER_EMP1),
  /** Auto-generated from RARE rule sets-inter-emp2 */
  EVALUE(SETS_INTER_EMP2),
  /** Auto-generated from RARE rule sets-minus-emp1 */
  EVALUE(SETS_MINUS_EMP1),
  /** Auto-generated from RARE rule sets-minus-emp2 */
  EVALUE(SETS_MINUS_EMP2),
  /** Auto-generated from RARE rule sets-union-emp1 */
  EVALUE(SETS_UNION_EMP1),
  /** Auto-generated from RARE rule sets-union-emp2 */
  EVALUE(SETS_UNION_EMP2),
  /** Auto-generated from RARE rule sets-inter-member */
  EVALUE(SETS_INTER_MEMBER),
  /** Auto-generated from RARE rule sets-minus-member */
  EVALUE(SETS_MINUS_MEMBER),
  /** Auto-generated from RARE rule sets-union-member */
  EVALUE(SETS_UNION_MEMBER),
  /** Auto-generated from RARE rule sets-choose-singleton */
  EVALUE(SETS_CHOOSE_SINGLETON),
  /** Auto-generated from RARE rule sets-minus-self */
  EVALUE(SETS_MINUS_SELF),
  /** Auto-generated from RARE rule sets-is-empty-elim */
  EVALUE(SETS_IS_EMPTY_ELIM),
  /** Auto-generated from RARE rule sets-is-singleton-elim */
  EVALUE(SETS_IS_SINGLETON_ELIM),
  /** Auto-generated from RARE rule str-eq-ctn-false */
  EVALUE(STR_EQ_CTN_FALSE),
  /** Auto-generated from RARE rule str-eq-ctn-full-false1 */
  EVALUE(STR_EQ_CTN_FULL_FALSE1),
  /** Auto-generated from RARE rule str-eq-ctn-full-false2 */
  EVALUE(STR_EQ_CTN_FULL_FALSE2),
  /** Auto-generated from RARE rule str-eq-len-false */
  EVALUE(STR_EQ_LEN_FALSE),
  /** Auto-generated from RARE rule str-substr-empty-str */
  EVALUE(STR_SUBSTR_EMPTY_STR),
  /** Auto-generated from RARE rule str-substr-empty-range */
  EVALUE(STR_SUBSTR_EMPTY_RANGE),
  /** Auto-generated from RARE rule str-substr-empty-start */
  EVALUE(STR_SUBSTR_EMPTY_START),
  /** Auto-generated from RARE rule str-substr-empty-start-neg */
  EVALUE(STR_SUBSTR_EMPTY_START_NEG),
  /** Auto-generated from RARE rule str-substr-substr-start-geq-len */
  EVALUE(STR_SUBSTR_SUBSTR_START_GEQ_LEN),
  /** Auto-generated from RARE rule str-substr-eq-empty */
  EVALUE(STR_SUBSTR_EQ_EMPTY),
  /** Auto-generated from RARE rule str-substr-z-eq-empty-leq */
  EVALUE(STR_SUBSTR_Z_EQ_EMPTY_LEQ),
  /** Auto-generated from RARE rule str-substr-eq-empty-leq-len */
  EVALUE(STR_SUBSTR_EQ_EMPTY_LEQ_LEN),
  /** Auto-generated from RARE rule str-len-replace-inv */
  EVALUE(STR_LEN_REPLACE_INV),
  /** Auto-generated from RARE rule str-len-replace-all-inv */
  EVALUE(STR_LEN_REPLACE_ALL_INV),
  /** Auto-generated from RARE rule str-len-update-inv */
  EVALUE(STR_LEN_UPDATE_INV),
  /** Auto-generated from RARE rule str-update-in-first-concat */
  EVALUE(STR_UPDATE_IN_FIRST_CONCAT),
  /** Auto-generated from RARE rule str-len-substr-in-range */
  EVALUE(STR_LEN_SUBSTR_IN_RANGE),
  /** Auto-generated from RARE rule str-concat-clash */
  EVALUE(STR_CONCAT_CLASH),
  /** Auto-generated from RARE rule str-concat-clash-rev */
  EVALUE(STR_CONCAT_CLASH_REV),
  /** Auto-generated from RARE rule str-concat-clash2 */
  EVALUE(STR_CONCAT_CLASH2),
  /** Auto-generated from RARE rule str-concat-clash2-rev */
  EVALUE(STR_CONCAT_CLASH2_REV),
  /** Auto-generated from RARE rule str-concat-unify */
  EVALUE(STR_CONCAT_UNIFY),
  /** Auto-generated from RARE rule str-concat-unify-rev */
  EVALUE(STR_CONCAT_UNIFY_REV),
  /** Auto-generated from RARE rule str-concat-unify-base */
  EVALUE(STR_CONCAT_UNIFY_BASE),
  /** Auto-generated from RARE rule str-concat-unify-base-rev */
  EVALUE(STR_CONCAT_UNIFY_BASE_REV),
  /** Auto-generated from RARE rule str-prefixof-elim */
  EVALUE(STR_PREFIXOF_ELIM),
  /** Auto-generated from RARE rule str-suffixof-elim */
  EVALUE(STR_SUFFIXOF_ELIM),
  /** Auto-generated from RARE rule str-prefixof-eq */
  EVALUE(STR_PREFIXOF_EQ),
  /** Auto-generated from RARE rule str-suffixof-eq */
  EVALUE(STR_SUFFIXOF_EQ),
  /** Auto-generated from RARE rule str-prefixof-one */
  EVALUE(STR_PREFIXOF_ONE),
  /** Auto-generated from RARE rule str-suffixof-one */
  EVALUE(STR_SUFFIXOF_ONE),
  /** Auto-generated from RARE rule str-substr-combine1 */
  EVALUE(STR_SUBSTR_COMBINE1),
  /** Auto-generated from RARE rule str-substr-combine2 */
  EVALUE(STR_SUBSTR_COMBINE2),
  /** Auto-generated from RARE rule str-substr-combine3 */
  EVALUE(STR_SUBSTR_COMBINE3),
  /** Auto-generated from RARE rule str-substr-combine4 */
  EVALUE(STR_SUBSTR_COMBINE4),
  /** Auto-generated from RARE rule str-substr-concat1 */
  EVALUE(STR_SUBSTR_CONCAT1),
  /** Auto-generated from RARE rule str-substr-concat2 */
  EVALUE(STR_SUBSTR_CONCAT2),
  /** Auto-generated from RARE rule str-substr-replace */
  EVALUE(STR_SUBSTR_REPLACE),
  /** Auto-generated from RARE rule str-substr-full */
  EVALUE(STR_SUBSTR_FULL),
  /** Auto-generated from RARE rule str-substr-full-eq */
  EVALUE(STR_SUBSTR_FULL_EQ),
  /** Auto-generated from RARE rule str-contains-refl */
  EVALUE(STR_CONTAINS_REFL),
  /** Auto-generated from RARE rule str-contains-concat-find */
  EVALUE(STR_CONTAINS_CONCAT_FIND),
  /** Auto-generated from RARE rule str-contains-concat-find-contra */
  EVALUE(STR_CONTAINS_CONCAT_FIND_CONTRA),
  /** Auto-generated from RARE rule str-contains-split-char */
  EVALUE(STR_CONTAINS_SPLIT_CHAR),
  /** Auto-generated from RARE rule str-contains-leq-len-eq */
  EVALUE(STR_CONTAINS_LEQ_LEN_EQ),
  /** Auto-generated from RARE rule str-contains-emp */
  EVALUE(STR_CONTAINS_EMP),
  /** Auto-generated from RARE rule str-contains-char */
  EVALUE(STR_CONTAINS_CHAR),
  /** Auto-generated from RARE rule str-at-elim */
  EVALUE(STR_AT_ELIM),
  /** Auto-generated from RARE rule str-replace-self */
  EVALUE(STR_REPLACE_SELF),
  /** Auto-generated from RARE rule str-replace-id */
  EVALUE(STR_REPLACE_ID),
  /** Auto-generated from RARE rule str-replace-prefix */
  EVALUE(STR_REPLACE_PREFIX),
  /** Auto-generated from RARE rule str-replace-no-contains */
  EVALUE(STR_REPLACE_NO_CONTAINS),
  /** Auto-generated from RARE rule str-replace-find-base */
  EVALUE(STR_REPLACE_FIND_BASE),
  /** Auto-generated from RARE rule str-replace-find-first-concat */
  EVALUE(STR_REPLACE_FIND_FIRST_CONCAT),
  /** Auto-generated from RARE rule str-replace-empty */
  EVALUE(STR_REPLACE_EMPTY),
  /** Auto-generated from RARE rule str-replace-one-pre */
  EVALUE(STR_REPLACE_ONE_PRE),
  /** Auto-generated from RARE rule str-replace-find-pre */
  EVALUE(STR_REPLACE_FIND_PRE),
  /** Auto-generated from RARE rule str-replace-all-no-contains */
  EVALUE(STR_REPLACE_ALL_NO_CONTAINS),
  /** Auto-generated from RARE rule str-replace-re-none */
  EVALUE(STR_REPLACE_RE_NONE),
  /** Auto-generated from RARE rule str-replace-re-all-none */
  EVALUE(STR_REPLACE_RE_ALL_NONE),
  /** Auto-generated from RARE rule str-len-concat-rec */
  EVALUE(STR_LEN_CONCAT_REC),
  /** Auto-generated from RARE rule str-len-eq-zero-concat-rec */
  EVALUE(STR_LEN_EQ_ZERO_CONCAT_REC),
  /** Auto-generated from RARE rule str-len-eq-zero-base */
  EVALUE(STR_LEN_EQ_ZERO_BASE),
  /** Auto-generated from RARE rule str-indexof-self */
  EVALUE(STR_INDEXOF_SELF),
  /** Auto-generated from RARE rule str-indexof-no-contains */
  EVALUE(STR_INDEXOF_NO_CONTAINS),
  /** Auto-generated from RARE rule str-indexof-oob */
  EVALUE(STR_INDEXOF_OOB),
  /** Auto-generated from RARE rule str-indexof-oob2 */
  EVALUE(STR_INDEXOF_OOB2),
  /** Auto-generated from RARE rule str-indexof-contains-pre */
  EVALUE(STR_INDEXOF_CONTAINS_PRE),
  /** Auto-generated from RARE rule str-indexof-find-emp */
  EVALUE(STR_INDEXOF_FIND_EMP),
  /** Auto-generated from RARE rule str-indexof-eq-irr */
  EVALUE(STR_INDEXOF_EQ_IRR),
  /** Auto-generated from RARE rule str-indexof-re-none */
  EVALUE(STR_INDEXOF_RE_NONE),
  /** Auto-generated from RARE rule str-indexof-re-emp-re */
  EVALUE(STR_INDEXOF_RE_EMP_RE),
  /** Auto-generated from RARE rule str-to-lower-concat */
  EVALUE(STR_TO_LOWER_CONCAT),
  /** Auto-generated from RARE rule str-to-upper-concat */
  EVALUE(STR_TO_UPPER_CONCAT),
  /** Auto-generated from RARE rule str-to-lower-upper */
  EVALUE(STR_TO_LOWER_UPPER),
  /** Auto-generated from RARE rule str-to-upper-lower */
  EVALUE(STR_TO_UPPER_LOWER),
  /** Auto-generated from RARE rule str-to-lower-len */
  EVALUE(STR_TO_LOWER_LEN),
  /** Auto-generated from RARE rule str-to-upper-len */
  EVALUE(STR_TO_UPPER_LEN),
  /** Auto-generated from RARE rule str-to-lower-from-int */
  EVALUE(STR_TO_LOWER_FROM_INT),
  /** Auto-generated from RARE rule str-to-upper-from-int */
  EVALUE(STR_TO_UPPER_FROM_INT),
  /** Auto-generated from RARE rule str-to-int-concat-neg-one */
  EVALUE(STR_TO_INT_CONCAT_NEG_ONE),
  /** Auto-generated from RARE rule str-leq-empty */
  EVALUE(STR_LEQ_EMPTY),
  /** Auto-generated from RARE rule str-leq-empty-eq */
  EVALUE(STR_LEQ_EMPTY_EQ),
  /** Auto-generated from RARE rule str-leq-concat-false */
  EVALUE(STR_LEQ_CONCAT_FALSE),
  /** Auto-generated from RARE rule str-leq-concat-true */
  EVALUE(STR_LEQ_CONCAT_TRUE),
  /** Auto-generated from RARE rule str-leq-concat-base-1 */
  EVALUE(STR_LEQ_CONCAT_BASE_1),
  /** Auto-generated from RARE rule str-leq-concat-base-2 */
  EVALUE(STR_LEQ_CONCAT_BASE_2),
  /** Auto-generated from RARE rule str-lt-elim */
  EVALUE(STR_LT_ELIM),
  /** Auto-generated from RARE rule str-from-int-no-ctn-nondigit */
  EVALUE(STR_FROM_INT_NO_CTN_NONDIGIT),
  /** Auto-generated from RARE rule str-substr-ctn-contra */
  EVALUE(STR_SUBSTR_CTN_CONTRA),
  /** Auto-generated from RARE rule str-substr-ctn */
  EVALUE(STR_SUBSTR_CTN),
  /** Auto-generated from RARE rule str-replace-dual-ctn */
  EVALUE(STR_REPLACE_DUAL_CTN),
  /** Auto-generated from RARE rule str-replace-dual-ctn-false */
  EVALUE(STR_REPLACE_DUAL_CTN_FALSE),
  /** Auto-generated from RARE rule str-replace-self-ctn-simp */
  EVALUE(STR_REPLACE_SELF_CTN_SIMP),
  /** Auto-generated from RARE rule str-replace-emp-ctn-src */
  EVALUE(STR_REPLACE_EMP_CTN_SRC),
  /** Auto-generated from RARE rule str-substr-char-start-eq-len */
  EVALUE(STR_SUBSTR_CHAR_START_EQ_LEN),
  /** Auto-generated from RARE rule str-contains-repl-char */
  EVALUE(STR_CONTAINS_REPL_CHAR),
  /** Auto-generated from RARE rule str-contains-repl-self-tgt-char */
  EVALUE(STR_CONTAINS_REPL_SELF_TGT_CHAR),
  /** Auto-generated from RARE rule str-contains-repl-self */
  EVALUE(STR_CONTAINS_REPL_SELF),
  /** Auto-generated from RARE rule str-contains-repl-tgt */
  EVALUE(STR_CONTAINS_REPL_TGT),
  /** Auto-generated from RARE rule str-repl-repl-len-id */
  EVALUE(STR_REPL_REPL_LEN_ID),
  /** Auto-generated from RARE rule str-repl-repl-src-tgt-no-ctn */
  EVALUE(STR_REPL_REPL_SRC_TGT_NO_CTN),
  /** Auto-generated from RARE rule str-repl-repl-tgt-self */
  EVALUE(STR_REPL_REPL_TGT_SELF),
  /** Auto-generated from RARE rule str-repl-repl-tgt-no-ctn */
  EVALUE(STR_REPL_REPL_TGT_NO_CTN),
  /** Auto-generated from RARE rule str-repl-repl-src-self */
  EVALUE(STR_REPL_REPL_SRC_SELF),
  /** Auto-generated from RARE rule str-repl-repl-src-inv-no-ctn1 */
  EVALUE(STR_REPL_REPL_SRC_INV_NO_CTN1),
  /** Auto-generated from RARE rule str-repl-repl-src-inv-no-ctn2 */
  EVALUE(STR_REPL_REPL_SRC_INV_NO_CTN2),
  /** Auto-generated from RARE rule str-repl-repl-src-inv-no-ctn3 */
  EVALUE(STR_REPL_REPL_SRC_INV_NO_CTN3),
  /** Auto-generated from RARE rule str-repl-repl-dual-self */
  EVALUE(STR_REPL_REPL_DUAL_SELF),
  /** Auto-generated from RARE rule str-repl-repl-dual-ite1 */
  EVALUE(STR_REPL_REPL_DUAL_ITE1),
  /** Auto-generated from RARE rule str-repl-repl-dual-ite2 */
  EVALUE(STR_REPL_REPL_DUAL_ITE2),
  /** Auto-generated from RARE rule str-repl-repl-lookahead-id-simp */
  EVALUE(STR_REPL_REPL_LOOKAHEAD_ID_SIMP),
  /** Auto-generated from RARE rule re-all-elim */
  EVALUE(RE_ALL_ELIM),
  /** Auto-generated from RARE rule re-opt-elim */
  EVALUE(RE_OPT_ELIM),
  /** Auto-generated from RARE rule re-diff-elim */
  EVALUE(RE_DIFF_ELIM),
  /** Auto-generated from RARE rule re-plus-elim */
  EVALUE(RE_PLUS_ELIM),
  /** Auto-generated from RARE rule re-concat-star-swap */
  EVALUE(RE_CONCAT_STAR_SWAP),
  /** Auto-generated from RARE rule re-concat-star-repeat */
  EVALUE(RE_CONCAT_STAR_REPEAT),
  /** Auto-generated from RARE rule re-concat-star-subsume1 */
  EVALUE(RE_CONCAT_STAR_SUBSUME1),
  /** Auto-generated from RARE rule re-concat-star-subsume2 */
  EVALUE(RE_CONCAT_STAR_SUBSUME2),
  /** Auto-generated from RARE rule re-concat-merge */
  EVALUE(RE_CONCAT_MERGE),
  /** Auto-generated from RARE rule re-union-all */
  EVALUE(RE_UNION_ALL),
  /** Auto-generated from RARE rule re-union-const-elim */
  EVALUE(RE_UNION_CONST_ELIM),
  /** Auto-generated from RARE rule re-inter-all */
  EVALUE(RE_INTER_ALL),
  /** Auto-generated from RARE rule re-star-none */
  EVALUE(RE_STAR_NONE),
  /** Auto-generated from RARE rule re-star-emp */
  EVALUE(RE_STAR_EMP),
  /** Auto-generated from RARE rule re-star-star */
  EVALUE(RE_STAR_STAR),
  /** Auto-generated from RARE rule re-star-union-drop-emp */
  EVALUE(RE_STAR_UNION_DROP_EMP),
  /** Auto-generated from RARE rule re-loop-neg */
  EVALUE(RE_LOOP_NEG),
  /** Auto-generated from RARE rule re-inter-cstring */
  EVALUE(RE_INTER_CSTRING),
  /** Auto-generated from RARE rule re-inter-cstring-neg */
  EVALUE(RE_INTER_CSTRING_NEG),
  /** Auto-generated from RARE rule str-substr-len-include */
  EVALUE(STR_SUBSTR_LEN_INCLUDE),
  /** Auto-generated from RARE rule str-substr-len-include-pre */
  EVALUE(STR_SUBSTR_LEN_INCLUDE_PRE),
  /** Auto-generated from RARE rule str-substr-len-norm */
  EVALUE(STR_SUBSTR_LEN_NORM),
  /** Auto-generated from RARE rule seq-len-rev */
  EVALUE(SEQ_LEN_REV),
  /** Auto-generated from RARE rule seq-rev-rev */
  EVALUE(SEQ_REV_REV),
  /** Auto-generated from RARE rule seq-rev-concat */
  EVALUE(SEQ_REV_CONCAT),
  /** Auto-generated from RARE rule str-eq-repl-self-emp */
  EVALUE(STR_EQ_REPL_SELF_EMP),
  /** Auto-generated from RARE rule str-eq-repl-no-change */
  EVALUE(STR_EQ_REPL_NO_CHANGE),
  /** Auto-generated from RARE rule str-eq-repl-tgt-eq-len */
  EVALUE(STR_EQ_REPL_TGT_EQ_LEN),
  /** Auto-generated from RARE rule str-eq-repl-len-one-emp-prefix */
  EVALUE(STR_EQ_REPL_LEN_ONE_EMP_PREFIX),
  /** Auto-generated from RARE rule str-eq-repl-emp-tgt-nemp */
  EVALUE(STR_EQ_REPL_EMP_TGT_NEMP),
  /** Auto-generated from RARE rule str-eq-repl-nemp-src-emp */
  EVALUE(STR_EQ_REPL_NEMP_SRC_EMP),
  /** Auto-generated from RARE rule str-eq-repl-self-src */
  EVALUE(STR_EQ_REPL_SELF_SRC),
  /** Auto-generated from RARE rule seq-len-unit */
  EVALUE(SEQ_LEN_UNIT),
  /** Auto-generated from RARE rule seq-nth-unit */
  EVALUE(SEQ_NTH_UNIT),
  /** Auto-generated from RARE rule seq-rev-unit */
  EVALUE(SEQ_REV_UNIT),
  /** Auto-generated from RARE rule seq-len-empty */
  EVALUE(SEQ_LEN_EMPTY),
  /** Auto-generated from RARE rule re-in-empty */
  EVALUE(RE_IN_EMPTY),
  /** Auto-generated from RARE rule re-in-sigma */
  EVALUE(RE_IN_SIGMA),
  /** Auto-generated from RARE rule re-in-sigma-star */
  EVALUE(RE_IN_SIGMA_STAR),
  /** Auto-generated from RARE rule re-in-cstring */
  EVALUE(RE_IN_CSTRING),
  /** Auto-generated from RARE rule re-in-comp */
  EVALUE(RE_IN_COMP),
  /** Auto-generated from RARE rule str-in-re-union-elim */
  EVALUE(STR_IN_RE_UNION_ELIM),
  /** Auto-generated from RARE rule str-in-re-inter-elim */
  EVALUE(STR_IN_RE_INTER_ELIM),
  /** Auto-generated from RARE rule str-in-re-range-elim */
  EVALUE(STR_IN_RE_RANGE_ELIM),
  /** Auto-generated from RARE rule str-in-re-contains */
  EVALUE(STR_IN_RE_CONTAINS),
  /** Auto-generated from RARE rule str-in-re-from-int-nemp-dig-range */
  EVALUE(STR_IN_RE_FROM_INT_NEMP_DIG_RANGE),
  /** Auto-generated from RARE rule str-in-re-from-int-dig-range */
  EVALUE(STR_IN_RE_FROM_INT_DIG_RANGE),
  /** Auto-generated from RARE rule eq-refl */
  EVALUE(EQ_REFL),
  /** Auto-generated from RARE rule eq-symm */
  EVALUE(EQ_SYMM),
  /** Auto-generated from RARE rule eq-cond-deq */
  EVALUE(EQ_COND_DEQ),
  /** Auto-generated from RARE rule eq-ite-lift */
  EVALUE(EQ_ITE_LIFT),
  /** Auto-generated from RARE rule distinct-binary-elim */
  EVALUE(DISTINCT_BINARY_ELIM),
  /** Auto-generated from RARE rule uf-bv2nat-int2bv */
  EVALUE(UF_BV2NAT_INT2BV),
  /** Auto-generated from RARE rule uf-bv2nat-int2bv-extend */
  EVALUE(UF_BV2NAT_INT2BV_EXTEND),
  /** Auto-generated from RARE rule uf-bv2nat-int2bv-extract */
  EVALUE(UF_BV2NAT_INT2BV_EXTRACT),
  /** Auto-generated from RARE rule uf-int2bv-bv2nat */
  EVALUE(UF_INT2BV_BV2NAT),
  /** Auto-generated from RARE rule uf-bv2nat-geq-elim */
  EVALUE(UF_BV2NAT_GEQ_ELIM),
  /** Auto-generated from RARE rule uf-int2bv-bvult-equiv */
  EVALUE(UF_INT2BV_BVULT_EQUIV),
  /** Auto-generated from RARE rule uf-int2bv-bvule-equiv */
  EVALUE(UF_INT2BV_BVULE_EQUIV),
  /** Auto-generated from RARE rule uf-sbv-to-int-elim */
  EVALUE(UF_SBV_TO_INT_ELIM),
  /** Auto-generated from RARE rule arith-sine-zero */
  EVALUE(ARITH_SINE_ZERO),
  /** Auto-generated from RARE rule arith-sine-pi2 */
  EVALUE(ARITH_SINE_PI2),
  /** Auto-generated from RARE rule arith-cosine-elim */
  EVALUE(ARITH_COSINE_ELIM),
  /** Auto-generated from RARE rule arith-tangent-elim */
  EVALUE(ARITH_TANGENT_ELIM),
  /** Auto-generated from RARE rule arith-secent-elim */
  EVALUE(ARITH_SECENT_ELIM),
  /** Auto-generated from RARE rule arith-cosecent-elim */
  EVALUE(ARITH_COSECENT_ELIM),
  /** Auto-generated from RARE rule arith-cotangent-elim */
  EVALUE(ARITH_COTANGENT_ELIM),
  /** Auto-generated from RARE rule arith-pi-not-int */
  EVALUE(ARITH_PI_NOT_INT),
  /** Auto-generated from RARE rule sets-card-singleton */
  EVALUE(SETS_CARD_SINGLETON),
  /** Auto-generated from RARE rule sets-card-union */
  EVALUE(SETS_CARD_UNION),
  /** Auto-generated from RARE rule sets-card-minus */
  EVALUE(SETS_CARD_MINUS),
  /** Auto-generated from RARE rule sets-card-emp */
  EVALUE(SETS_CARD_EMP),
// ${rules}$
#ifdef CVC5_API_USE_C_ENUMS
  // must be last entry
  EVALUE(LAST)
#endif
};

#ifdef CVC5_API_USE_C_ENUMS
#ifndef DOXYGEN_SKIP
typedef enum ENUM(ProofRule) ENUM(ProofRule);
typedef enum ENUM(ProofRewriteRule) ENUM(ProofRewriteRule);
#endif
#endif

#ifdef CVC5_API_USE_C_ENUMS

/**
 * Get a string representation of a Cvc5ProofRule.
 * @param rule The proof rule.
 * @return The string representation.
 */
CVC5_EXPORT const char* cvc5_proof_rule_to_string(Cvc5ProofRule rule);

/**
 * Hash function for Cvc5ProofRule.
 * @param rule The proof rule.
 * @return The hash value.
 */
CVC5_EXPORT size_t cvc5_proof_rule_hash(Cvc5ProofRule rule);

/**
 * Get a string representation of a Cvc5ProofRewriteRule.
 * @param rule The proof rewrite rule.
 * @return The string representation.
 */
CVC5_EXPORT const char* cvc5_proof_rewrite_rule_to_string(
    Cvc5ProofRewriteRule rule);

/**
 * Hash function for Cvc5ProofRewriteRule.
 * @param rule The proof rewrite rule.
 * @return The hash value.
 */
CVC5_EXPORT size_t cvc5_proof_rewrite_rule_hash(Cvc5ProofRewriteRule rule);

#else

/**
 * Converts a proof rule to a string. Note: This function is also used in
 * `safe_print()`. Changing this function name or signature will result in
 * `safe_print()` printing "<unsupported>" instead of the proper strings for
 * the enum values.
 *
 * @param rule The proof rule
 * @return The name of the proof rule
 */
CVC5_EXPORT const char* toString(ProofRule rule);

/**
 * Writes a proof rule name to a stream.
 *
 * @param out The stream to write to
 * @param rule The proof rule to write to the stream
 * @return The stream
 */
CVC5_EXPORT std::ostream& operator<<(std::ostream& out, ProofRule rule);

/**
 * Converts a proof rewrite rule to a string. Note: This function is also
 * used in `safe_print()`. Changing this function name or signature will result
 * in `safe_print()` printing "<unsupported>" instead of the proper strings for
 * the enum values.
 *
 * @param rule The proof rewrite rule
 * @return The name of the proof rewrite rule
 */
CVC5_EXPORT const char* toString(ProofRewriteRule rule);

/**
 * Writes a proof rewrite rule name to a stream.
 *
 * @param out The stream to write to
 * @param rule The proof rewrite rule to write to the stream
 * @return The stream
 */
CVC5_EXPORT std::ostream& operator<<(std::ostream& out, ProofRewriteRule rule);

}  // namespace cvc5

namespace std {

/**
 * Hash function for ProofRules.
 */
template <>
struct CVC5_EXPORT hash<cvc5::ProofRule>
{
  /**
   * Hashes a ProofRule to a size_t.
   * @param rule The proof rule.
   * @return The hash value.
   */
  size_t operator()(cvc5::ProofRule rule) const;
};

/**
 * Converts a proof rule to a string.
 *
 * @param rule The proof rule
 * @return The name of the proof rule
 */
CVC5_EXPORT std::string to_string(cvc5::ProofRule rule);

/**
 * Hash function for ProofRewriteRules.
 */
template <>
struct CVC5_EXPORT hash<cvc5::ProofRewriteRule>
{
  /**
   * Hashes a ProofRewriteRule to a size_t.
   * @param rule The proof rewrite rule.
   * @return The hash value.
   */
  size_t operator()(cvc5::ProofRewriteRule rule) const;
};

/**
 * Converts a proof rewrite rule to a string.
 *
 * @param rule The proof rewrite rule
 * @return The name of the proof rewrite rule
 */
CVC5_EXPORT std::string to_string(cvc5::ProofRewriteRule rule);

}  // namespace std

#endif
#endif

#ifdef CVC5_API_USE_C_ENUMS
#ifndef CVC5__API__CVC5_C_PROOF_RULE_H
#define CVC5__API__CVC5_C_PROOF_RULE_H
#endif
#else
#ifndef CVC5__API__CVC5_CPP_PROOF_RULE_H
#define CVC5__API__CVC5_CPP_PROOF_RULE_H
#endif
#endif
