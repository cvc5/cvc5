Java API
========

The Java API for cvc5 mostly mirrors the :doc:`C++ API <../cpp/cpp>` and supports operator
overloading, iterators, and exceptions.
There are a few differences from the C++ API, such as using arbitrary-precision integer pairs,
specifically, pairs of Java `BigInteger` objects, to represent rational numbers.
The :doc:`quickstart guide <quickstart>` gives a short introduction,
and more examples can be found `here <../../examples/examples.html>`_.


For most applications, the `Solver <io/github/cvc5/api/Solver.html>`_ class is the main entry point to cvc5.
The class hierarchy of `cvc5 package <io/github/cvc5/api/package-summary.html>`_
provides more details on the individual classes.

.. toctree::
    :hidden:

    quickstart
    API documentation <index>

Building cvc5 Java API
^^^^^^^^^^^^^^^^^^^^^^

.. code-block:: bash

     $ git clone https://github.com/cvc5/cvc5
     $ cd cvc5
     $ ./configure.sh production --java-bindings --auto-download --prefix=build/install
     $ cd build
     $ make
     $ make install

     $ ls install/lib
       cmake  libcvc5jni.so  libcvc5parser.so  libcvc5parser.so.1  libcvc5.so
       libpicpoly.a  libpicpolyxx.a  libpoly.so libpoly.so.0  libpoly.so.0.1.9
       libpolyxx.so  libpolyxx.so.0  libpolyxx.so.0.1.9  objects-Production
     $ ls install/share/java/
       cvc5-0.0.5-dev.jar  cvc5.jar

     # compile example QuickStart.java with cvc5 jar file
     $ javac -cp "install/share/java/cvc5.jar" ../examples/api/java/QuickStart.java -d .

     # run example QuickStart with cvc5 jar file and cvc5 shared libraries
     $ java -cp "install/share/java/cvc5.jar:." "-Djava.library.path=install/lib" QuickStart
       expected: sat
       result: sat
       value for x: 1/6
       value for y: 1/6
       expected: unsat
       result: unsat
       unsat core size: 3
       unsat core:
       (< 0 a)
       (< 0 b)
       (< (+ a b) 1)

`Package io.github.cvc5.api <io/github/cvc5/api/package-summary.html>`_
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

  * class `Datatype <io/github/cvc5/api/Datatype.html>`_
  * class `DatatypeConstructor <io/github/cvc5/api/DatatypeConstructor.html>`_
  * class `DatatypeConstructorDecl <io/github/cvc5/api/DatatypeConstructorDecl.html>`_
  * class `DatatypeDecl <io/github/cvc5/api/DatatypeDecl.html>`_
  * class `DatatypeSelector <io/github/cvc5/api/DatatypeSelector.html>`_
  * class `Grammar <io/github/cvc5/api/Grammar.html>`_
  * class `Op <io/github/cvc5/api/Op.html>`_
  * class `OptionInfo <io/github/cvc5/api/OptionInfo.html>`_
  * class `Pair<K,V> <io/github/cvc5/api/Pair.html>`_
  * class `Result <io/github/cvc5/api/Result.html>`_
  * class `Solver <io/github/cvc5/api/Solver.html>`_
  * class `Sort <io/github/cvc5/api/Sort.html>`_
  * class `Stat <io/github/cvc5/api/Stat.html>`_
  * class `Statistics <io/github/cvc5/api/Statistics.html>`_
  * class `Term <io/github/cvc5/api/Term.html>`_
  * class `Triplet<A,B,C> <io/github/cvc5/api/Triplet.html>`_
  * class `Utils <io/github/cvc5/api/Utils.html>`_
  * enum `Kind <io/github/cvc5/api/Kind.html>`_
  * enum `Result.UnknownExplanation <io/github/cvc5/api/Result.UnknownExplanation.html>`_
  * enum `RoundingMode <io/github/cvc5/api/RoundingMode.html>`_
  * exception `CVC5ApiException <io/github/cvc5/api/CVC5ApiException.html>`_
  * exception `CVC5ApiOptionException <io/github/cvc5/api/CVC5ApiOptionException.html>`_
  * exception `CVC5ApiRecoverableException <io/github/cvc5/api/CVC5ApiRecoverableException.html>`_
