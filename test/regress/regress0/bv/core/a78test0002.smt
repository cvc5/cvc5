(benchmark a78test0002.smt
  :source {
Bit-vector benchmarks from Dawson Engler's tool contributed by Vijay Ganesh
(vganesh@stanford.edu).  Translated into SMT-LIB format by Clark Barrett using
CVC3.

}
  :status sat
  :difficulty { 0 }
  :category { industrial }
  :logic QF_BV
  :extrafuns ((r1 BitVec[16]))
  :assumption
(not (= r1 bv0[16]))
  :assumption
(not (not (= (concat bv0[16] r1) bv65535[32])))
  :formula
(not false)
)
