(benchmark bitvec5.smt
  :source {
Hand-crafted bit-vector benchmarks.  Some are from the SVC benchmark suite.
Contributed by Vijay Ganesh (vganesh@stanford.edu).  Translated into SMT-LIB
format by Clark Barrett using CVC3.

}
  :status unsat
  :difficulty { 0 }
  :category { crafted }
  :logic QF_BV
  :extrafuns ((a BitVec[32]))
  :extrafuns ((b BitVec[32]))
  :extrafuns ((c BitVec[32]))
  :extrafuns ((d BitVec[32]))
  :extrafuns ((e BitVec[32]))
  :formula
(not (and (implies (and (and (= (extract[31:0] a) (extract[31:0] b)) (= (extract[31:16] a) (extract[15:0] c))) (= (extract[31:8] b) (extract[23:0] d))) (= (extract[11:8] c) (extract[19:16] d))) (implies (= (extract[30:0] e) (extract[31:1] e)) (= (extract[0:0] e) (extract[31:31] e)))))
)
