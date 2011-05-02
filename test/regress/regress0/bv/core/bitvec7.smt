(benchmark bitvec7.smt
  :source {
Hand-crafted bit-vector benchmarks.  Some are from the SVC benchmark suite.
Contributed by Vijay Ganesh (vganesh@stanford.edu).  Translated into SMT-LIB
format by Clark Barrett using CVC3.

}
  :status unsat
  :difficulty { 0 }
  :category { crafted }
  :logic QF_BV
  :extrafuns ((bv BitVec[10]))
  :extrapreds ((a))
  :formula
(not (and (= (extract[5:3] bv96[8]) (extract[4:2] (concat bv121[7] (extract[0:0] bv)))) (= (concat bv1[1] (ite a bv0[1] bv1[1])) (extract[1:0] (ite a bv6[3] bv3[3])))))
)
