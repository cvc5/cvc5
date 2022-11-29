Theory Reference: Strings
=========================

cvc5 supports all operators of the `SMT-LIB standard for strings
<https://smtlib.cs.uiowa.edu/theories-UnicodeStrings.shtml>`_. It additionally
supports some non-standard operators that are described below.

Semantics
^^^^^^^^^

.. code-block::

   * (str.indexof_re String RegLan Int Int)

     Let w₂ = ⟦str.substr⟧(w, i, |w| - i)

     - ⟦str.indexof_re⟧(w, L, i) = -1     if no substring of w₂ is in L or i < 0

     - ⟦str.indexof_re⟧(w, L, i) = |u₁|
       where u₁, w₁ are the shortest words such that 
         - w₂ = u₁w₁u₂
         - w₁ ∈ L
                                          if some substring of w₂ is in L and i > 0

   * (str.update String Int String)

     - ⟦str.update⟧(w, i, w₂) = w         if i < 0 or i >= |w|

     - ⟦str.update⟧(w, i, w₂) = u₁u₂u₃
       where
         - w = u₁w₃u₃
         - |w₃| = |u₂|
         - |u₁| = i
         - u₂u₄ = w₂
         - |u₂| = min(|w₂|, |w| - i)      otherwise

   * (str.rev String String)

     ⟦str.rev⟧(w) is the string obtained by reversing w, e.g.,
     ⟦str.rev⟧("abc") = "cba".

   * (str.to_lower String String)

     ⟦str.to_lower⟧(w) = w₂
     where
       - |w| = |w₂|
       - the i-th character ri in w₂ is:

         code(ri) = code(si) + ite(65 <= code(si) <= 90, 32, 0)

         where si is the i-th character in w

     Note: This operator performs the case conversion for the ASCII portion of
     Unicode only.

   * (str.to_upper String String)

     ⟦str.to_upper⟧(w) = w₂
     where
       - |w| = |w₂|
       - the i-th character ri in w₂ is:

         code(ri) = code(si) - ite(97 <= code(si) <= 122, 32, 0)

         where si is the i-th character in w

     Note: This operator performs the case conversion for the ASCII portion of
     Unicode only.
