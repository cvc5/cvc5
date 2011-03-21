(benchmark bitvec2.smt
  :source {
Hand-crafted bit-vector benchmarks.  Some are from the SVC benchmark suite.
Contributed by Vijay Ganesh (vganesh@stanford.edu).  Translated into SMT-LIB
format by Clark Barrett using CVC3.

}
  :status unsat
  :difficulty { 0 }
  :category { crafted }
  :logic QF_BV
  :extrapreds ((a))
  :formula
(not (= (concat bv1[1] (ite a bv0[1] bv1[1])) (ite a bv2[2] bv3[2])))
)
