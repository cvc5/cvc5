/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 java API.
 */

package io.github.cvc5;

import static java.lang.foreign.ValueLayout.JAVA_LONG;

import io.github.cvc5.capi.CApi;
import java.lang.foreign.Arena;
import java.lang.foreign.MemorySegment;
import java.math.BigInteger;

/**
 * A cvc5 Proof.
 */
public class Proof extends AbstractPointer
{
  /**
   * Null proof
   */
  public Proof()
  {
    super(null, MemorySegment.NULL, null);
  }

  /**
   * This is an internal constructor intended to be used only
   * inside cvc5 package.
   *
   * @param pointer the cpp pointer to Proof
   */
  Proof(NativeContext ctx, MemorySegment pointer)
  {
    super(ctx, pointer, Proof::deletePointer);
  }

  private static void deletePointer(MemorySegment pointer)
  {
    CApi.cvc5_proof_release(pointer);
  }

  protected String toString(long pointer)
  {
    throw new UnsupportedOperationException("Proof.toString() is not supported in the cpp api");
  }

  /**
   * Get the proof rule used by the root step of the proof.
   *
   * @return The proof rule used by the root step of the proof.
   * @throws CVC5ApiException on error
   */
  public ProofRule getRule() throws CVC5ApiException
  {
    int value = getRule(handle());
    return ProofRule.fromInt(value);
  }

  private int getRule(MemorySegment pointer)
  {
    if (pointer.address() == 0)
    {
      // like Proof::getRule() of the C++ API on a null proof
      return ProofRule.UNKNOWN.getValue();
    }
    return Native.check(CApi.cvc5_proof_get_rule(pointer));
  }

  /**
   * Get the proof rewrite rule used by the root step of the proof.
   *
   * @return The proof rewrite rule used by the root step of the proof.
   * @throws CVC5ApiException if `getRule()` does not return `DSL_REWRITE`
   *         or `THEORY_REWRITE`.
   */
  public ProofRewriteRule getRewriteRule() throws CVC5ApiException
  {
    int value = getRewriteRule(handle());
    return ProofRewriteRule.fromInt(value);
  }

  private int getRewriteRule(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_proof_get_rewrite_rule(pointer));
  }

  /**
   * Get the conclusion of the root step of the proof.
   *
   * @return The conclusion of the root step of the proof.
   */
  public Term getResult()
  {
    MemorySegment termPointer = getResult(handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment getResult(MemorySegment pointer)
  {
    if (pointer.address() == 0)
    {
      // like Proof::getResult() of the C++ API on a null proof: the null term
      return MemorySegment.NULL;
    }
    return Native.handle(CApi.cvc5_proof_get_result(pointer));
  }

  /**
   * Get the premises of the root step of the proof.
   *
   * @return The premises of the root step of the proof.
   */
  public Proof[] getChildren()
  {
    MemorySegment[] proofPointers = getChildren(handle());
    return Utils.getProofs(ctx, proofPointers);
  }

  private MemorySegment[] getChildren(MemorySegment pointer)
  {
    if (pointer.address() == 0)
    {
      // like Proof::getChildren() of the C++ API on a null proof
      return new MemorySegment[0];
    }
    MemorySegment[] children;
    try (Arena arena = Arena.ofConfined())
    {
      MemorySegment size = arena.allocate(JAVA_LONG);
      MemorySegment proofs = Native.check(CApi.cvc5_proof_get_children(pointer, size));
      children = Native.handles(proofs, size.get(JAVA_LONG, 0));
    }
    // The returned proofs are owned by the solver that created this proof
    // (or by this proof, once that solver has been deleted). Acquire a
    // reference to each of them for its wrapper, so that it remains valid
    // after the solver and this proof have been released.
    for (int i = 0; i < children.length; i++)
    {
      children[i] = Native.handle(CApi.cvc5_proof_copy(children[i]));
    }
    return children;
  }

  /**
   * Get the arguments of the root step of the proof as a vector of terms.
   *
   * @return The arguments of the root step of the proof as a vector of terms.
   *         Some of those terms might be strings.
   */
  public Term[] getArguments()
  {
    MemorySegment[] termPointers = getArguments(handle());
    return Utils.getTerms(ctx, termPointers);
  }

  private MemorySegment[] getArguments(MemorySegment pointer)
  {
    if (pointer.address() == 0)
    {
      // like Proof::getArguments() of the C++ API on a null proof
      return new MemorySegment[0];
    }
    try (Arena arena = Arena.ofConfined())
    {
      MemorySegment size = arena.allocate(JAVA_LONG);
      MemorySegment terms = Native.check(CApi.cvc5_proof_get_arguments(pointer, size));
      return Native.handles(terms, size.get(JAVA_LONG, 0));
    }
  }

  /**
   * Referential equality operator.
   *
   * @param p The proof to compare to for equality.
   * @return True if the proofs point to the same internal proof object.
   */
  @Override
  public boolean equals(Object p)
  {
    if (this == p)
    {
      return true;
    }
    if (p == null || getClass() != p.getClass())
    {
      return false;
    }
    Proof proof = (Proof) p;
    if (address() == proof.address())
    {
      return true;
    }
    return equals(handle(), proof.handle());
  }

  private boolean equals(MemorySegment pointer1, MemorySegment pointer2)
  {
    // supports null proofs
    return Native.check(CApi.cvc5_proof_is_equal(pointer1, pointer2));
  }

  /**
   * Get the hash value of a proof.
   * @return The hash value.
   */
  @Override
  public int hashCode()
  {
    return Long.hashCode(hashCode(handle()));
  }

  private long hashCode(MemorySegment pointer)
  {
    if (pointer.address() == 0)
    {
      // like std::hash<Proof> of the C++ API on a null proof
      return 0;
    }
    return Native.check(CApi.cvc5_proof_hash(pointer));
  }
}
