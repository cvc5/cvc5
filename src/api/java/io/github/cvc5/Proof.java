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
    super(null, 0, null);
  }

  /**
   * This is an internal constructor intended to be used only
   * inside cvc5 package.
   *
   * @param pointer the cpp pointer to Proof
   */
  Proof(NativeContext ctx, long pointer)
  {
    super(ctx, pointer, Proof::deletePointer);
  }

  private static void deletePointer(long pointer)
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
    int value = getRule(getPointer());
    return ProofRule.fromInt(value);
  }

  private int getRule(long pointer)
  {
    if (pointer == 0)
    {
      // like Proof::getRule() of the C++ API on a null proof
      return ProofRule.UNKNOWN.getValue();
    }
    return CApi.cvc5_proof_get_rule(pointer);
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
    int value = getRewriteRule(getPointer());
    return ProofRewriteRule.fromInt(value);
  }

  private int getRewriteRule(long pointer)
  {
    return CApi.cvc5_proof_get_rewrite_rule(pointer);
  }

  /**
   * Get the conclusion of the root step of the proof.
   *
   * @return The conclusion of the root step of the proof.
   */
  public Term getResult()
  {
    long termPointer = getResult(getPointer());
    return new Term(ctx, termPointer);
  }

  private long getResult(long pointer)
  {
    if (pointer == 0)
    {
      // like Proof::getResult() of the C++ API on a null proof: the null term
      return 0;
    }
    return CApi.cvc5_proof_get_result(pointer);
  }

  /**
   * Get the premises of the root step of the proof.
   *
   * @return The premises of the root step of the proof.
   */
  public Proof[] getChildren()
  {
    long[] proofPointers = getChildren(getPointer());
    return Utils.getProofs(ctx, proofPointers);
  }

  private long[] getChildren(long pointer)
  {
    if (pointer == 0)
    {
      // like Proof::getChildren() of the C++ API on a null proof
      return new long[0];
    }
    long[] children;
    try (Arena arena = Arena.ofConfined())
    {
      MemorySegment size = Native.outLong(arena);
      long proofs = CApi.cvc5_proof_get_children(pointer, size.address());
      children = Native.longs(proofs, size.get(JAVA_LONG, 0));
    }
    // The returned proofs are owned by the solver that created this proof
    // (or by this proof, once that solver has been deleted). Acquire a
    // reference to each of them for its wrapper, so that it remains valid
    // after the solver and this proof have been released.
    for (int i = 0; i < children.length; i++)
    {
      children[i] = CApi.cvc5_proof_copy(children[i]);
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
    long[] termPointers = getArguments(getPointer());
    return Utils.getTerms(ctx, termPointers);
  }

  private long[] getArguments(long pointer)
  {
    if (pointer == 0)
    {
      // like Proof::getArguments() of the C++ API on a null proof
      return new long[0];
    }
    try (Arena arena = Arena.ofConfined())
    {
      MemorySegment size = Native.outLong(arena);
      long terms = CApi.cvc5_proof_get_arguments(pointer, size.address());
      return Native.longs(terms, size.get(JAVA_LONG, 0));
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
    if (pointer == proof.pointer)
    {
      return true;
    }
    return equals(getPointer(), proof.getPointer());
  }

  private boolean equals(long pointer1, long pointer2)
  {
    // supports null proofs
    return CApi.cvc5_proof_is_equal(pointer1, pointer2);
  }

  /**
   * Get the hash value of a proof.
   * @return The hash value.
   */
  @Override
  public int hashCode()
  {
    return Long.hashCode(hashCode(getPointer()));
  }

  private long hashCode(long pointer)
  {
    if (pointer == 0)
    {
      // like std::hash<Proof> of the C++ API on a null proof
      return 0;
    }
    return CApi.cvc5_proof_hash(pointer);
  }
}
