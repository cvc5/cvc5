(set-info :smt-lib-version 2.6)
(set-logic BV)
(set-info :source |These benchmarks are translations from the TPTP Library (Thousands of
Problems for Theorem Provers), see http://www.cs.miami.edu/~tptp/

The TPTP is maintained by Geoff Sutcliffe, and he contributed this
selection of benchmarks to SMT-LIB.

Translated to BV by Mathias Preiner.
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")
(set-info :status unknown)
(assert (not (exists ((?X (_ BitVec 32))) (= (bvmul ?X ?X) ?X))))
(check-sat)
(exit)
