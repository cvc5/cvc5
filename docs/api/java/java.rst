Java API
========

The Java API of cvc5 mostly mirrors the :doc:`C++ API <../cpp/cpp>` and
supports operator overloading, iterators, and exceptions.
There are a few differences from the C++ API, such as using arbitrary-precision
integer pairs, specifically, pairs of Java `BigInteger` objects, to represent
rational numbers.
The :doc:`quickstart guide <quickstart>` gives a short introduction,
and more examples can be found `here <../../examples/examples.html>`_.


For most applications, the `Solver <io/github/cvc5/Solver.html>`_ class is the
main entry point to cvc5.
The class hierarchy of `cvc5 package <io/github/cvc5/package-summary.html>`_
provides more details on the individual classes.

.. toctree::
    :hidden:

    quickstart

----

Using the cvc5 Java API in a Maven project
------------------------------------------

.. note::

   As of version 1.3.1, a stable release has not yet been published to Maven Central.
   Only snapshot builds are available in the Central Portal Snapshots repository.

To use the library in your Maven project, add the following
repository and dependency settings:

.. code-block:: xml

  <repositories>
    <repository>
      <name>Central Portal Snapshots</name>
      <id>central-portal-snapshots</id>
      <url>https://central.sonatype.com/repository/maven-snapshots/</url>
      <releases>
        <enabled>false</enabled>
      </releases>
      <snapshots>
        <enabled>true</enabled>
      </snapshots>
    </repository>
  </repositories>

  <dependencies>
    <!-- cvc5 Java bindings (pure Java API) -->
    <dependency>
      <groupId>io.github.cvc5</groupId>
      <artifactId>cvc5</artifactId>
      <version>${cvc5.version}-SNAPSHOT</version>
    </dependency>

    <!-- cvc5 native JNI library for the target platform -->
    <dependency>
      <groupId>io.github.cvc5</groupId>
      <artifactId>cvc5</artifactId>
      <version>${cvc5.version}-SNAPSHOT</version>
      <classifier>${os.classifier}</classifier>
    </dependency>
  </dependencies>

Here, ``${cvc5.version}`` refers to the version following the latest stable release
(e.g., use ``1.3.2`` if the latest stable version is ``1.3.1``).
The ``${os.classifier}`` variable specifies the operating system and CPU architecture
(e.g., ``linux-x86_64`` or ``osx-aarch_64``).

You can automatically retrieve the correct classifier using the
`os-maven-plugin <https://github.com/trustin/os-maven-plugin>`_:

.. code-block:: xml

  <build>
    <extensions>
      <extension>
        <groupId>kr.motd.maven</groupId>
        <artifactId>os-maven-plugin</artifactId>
        <version>1.7.0</version>
      </extension>
    </extensions>
  </build>

After adding the plugin, use ``${os.detected.classifier}`` as the classifier value.


Using self-contained cvc5 Java API JAR
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Starting from version 1.2.1, a JAR file containing the cvc5 Java API and
all required native libraries is available on the release page for each version.
To use it, download the appropriate JAR file for your platform. For example,
if your computer runs Linux x86_64, download `cvc5-Linux-x86_64-java-api.jar` to
a working directory.

To compile the `QuickStart.java` example provided in
the :doc:`quickstart guide <quickstart>`, ensure the file is in
the same directory as the JAR. Then, run:

.. code-block:: bash

    $ javac -cp "cvc5-Linux-x86_64-java-api.jar" ./QuickStart.java -d .

After compilation, execute the example with:

.. code-block:: bash

     $ java -cp "cvc5-Linux-x86_64-java-api.jar:." QuickStart # Replace : with ; on Windows
       expected: sat
       result: sat
       value for x: 1/6
       value for y: 1/6
       value for x - y: 0/1
       computed correctly
       expected: unsat
       result: unsat
       unsat core size: 3
       unsat core:
       (< 0 a)
       (< 0 b)
       (< (+ a b) 1)


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
       cmake             libcvc5parser.so.1  libpoly.so        libpolyxx.so
       libcvc5jni.so     libcvc5.so          libpoly.so.0      libpolyxx.so.0
       libcvc5parser.so  libcvc5.so.1        libpoly.so.0.2.0  libpolyxx.so.0.2.0
     $ ls install/share/java/
       cvc5-1.3.2-SNAPSHOT.jar  cvc5.jar

     # compile example QuickStart.java with cvc5 jar file
     $ javac -cp "install/share/java/cvc5.jar" ../examples/api/java/QuickStart.java -d .

     # run example QuickStart with cvc5 jar file and cvc5 shared libraries
     $ java -cp "install/share/java/cvc5.jar:." "-Djava.library.path=install/lib" QuickStart
       expected: sat
       result: sat
       value for x: 1/6
       value for y: 1/6
       value for x - y: 0/1
       computed correctly
       expected: unsat
       result: unsat
       unsat core size: 3
       unsat core: 
       (< 0 a)
       (< 0 b)
       (< (+ a b) 1)

----

`Javadoc API Documentation <index.html>`_
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

`Package io.github.cvc5 <io/github/cvc5/package-summary.html>`_
...............................................................

  * class `AbstractPlugin <io/github/cvc5/AbstractPlugin.html>`_
  * class `Command <io/github/cvc5/Command.html>`_
  * class `Datatype <io/github/cvc5/Datatype.html>`_
  * class `DatatypeConstructor <io/github/cvc5/DatatypeConstructor.html>`_
  * class `DatatypeConstructorDecl <io/github/cvc5/DatatypeConstructorDecl.html>`_
  * class `DatatypeDecl <io/github/cvc5/DatatypeDecl.html>`_
  * class `DatatypeSelector <io/github/cvc5/DatatypeSelector.html>`_
  * class `Grammar <io/github/cvc5/Grammar.html>`_
  * class `InputParser <io/github/cvc5/InputParser.html>`_
  * class `Op <io/github/cvc5/Op.html>`_
  * class `OptionInfo <io/github/cvc5/OptionInfo.html>`_
  * class `Pair<K,V> <io/github/cvc5/Pair.html>`_
  * class `Proof <io/github/cvc5/Proof.html>`_
  * class `Result <io/github/cvc5/Result.html>`_
  * class `Solver <io/github/cvc5/Solver.html>`_
  * class `Sort <io/github/cvc5/Sort.html>`_
  * class `Stat <io/github/cvc5/Stat.html>`_
  * class `Statistics <io/github/cvc5/Statistics.html>`_
  * class `SymbolManager <io/github/cvc5/SymbolManager.html>`_
  * class `SynthResult <io/github/cvc5/SynthResult.html>`_
  * class `Term <io/github/cvc5/Term.html>`_
  * class `TermManager <io/github/cvc5/TermManager.html>`_
  * class `Triplet<A,B,C> <io/github/cvc5/Triplet.html>`_
  * class `Utils <io/github/cvc5/Utils.html>`_
  * enum `Kind <io/github/cvc5/Kind.html>`_
  * enum `Result.UnknownExplanation <io/github/cvc5/Result.UnknownExplanation.html>`_
  * enum `RoundingMode <io/github/cvc5/RoundingMode.html>`_
  * enum `ProofRule <io/github/cvc5/ProofRule.html>`_
  * exception `CVC5ApiException <io/github/cvc5/CVC5ApiException.html>`_
  * exception `CVC5ApiOptionException <io/github/cvc5/CVC5ApiOptionException.html>`_
  * exception `CVC5ApiRecoverableException <io/github/cvc5/CVC5ApiRecoverableException.html>`_


`Package io.github.cvc5.modes <io/github/cvc5/modes/package-summary.html>`_
...........................................................................

  * enum `BlockModelsMode <io/github/cvc5/modes/BlockModelsMode.html>`_
  * enum `FindSynthTarget <io/github/cvc5/modes/FindSynthTarget.html>`_
  * enum `InputLanguage <io/github/cvc5/modes/InputLanguage.html>`_
  * enum `LearnedLitType <io/github/cvc5/modes/LearnedLitType.html>`_
  * enum `OptionCategory <io/github/cvc5/modes/OptionCategory.html>`_
  * enum `ProofComponent <io/github/cvc5/modes/ProofComponent.html>`_
  * enum `ProofFormat <io/github/cvc5/modes/ProofFormat.html>`_

