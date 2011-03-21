(benchmark a95test0002.smt
  :source {
Bit-vector benchmarks from Dawson Engler's tool contributed by Vijay Ganesh
(vganesh@stanford.edu).  Translated into SMT-LIB format by Clark Barrett using
CVC3.

}
  :status sat
  :difficulty { 0 }
  :category { industrial }
  :logic QF_BV
  :extrafuns ((a BitVec[32]))
  :assumption
(not (not (= (concat bv0[16] (extract[15:0] a)) a)))
  :formula
(not false)
)
