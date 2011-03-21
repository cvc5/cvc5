(benchmark bitvec1.smt
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
  :extrafuns ((res BitVec[32]))
  :formula
(flet ($cvc_1 (= (extract[0:0] a) bv1[1])) (flet ($cvc_2 (= (extract[0:0] b) bv1[1])) (let (?cvc_0 (extract[0:0] c)) (flet ($cvc_6 (= ?cvc_0 bv1[1])) (let (?cvc_3 (extract[0:0] res)) (flet ($cvc_4 (= (extract[1:1] a) bv1[1])) (flet ($cvc_5 (= (extract[1:1] b) bv1[1])) (flet ($cvc_8 (if_then_else $cvc_4 (not $cvc_5) $cvc_5)) (let (?cvc_7 (extract[1:1] c)) (let (?cvc_9 (extract[1:1] res)) (not (implies (and (and (and (= (extract[1:0] a) bv1[2]) (= (extract[1:0] b) bv1[2])) (and (if_then_else (and $cvc_1 $cvc_2) $cvc_6 (= ?cvc_0 bv0[1])) (if_then_else (if_then_else $cvc_1 (not $cvc_2) $cvc_2) (= ?cvc_3 bv1[1]) (= ?cvc_3 bv0[1])))) (and (if_then_else (or (and $cvc_4 $cvc_5)  (and $cvc_8 $cvc_6) ) (= ?cvc_7 bv1[1]) (= ?cvc_7 bv0[1])) (if_then_else (if_then_else $cvc_6 (not $cvc_8) $cvc_8) (= ?cvc_9 bv1[1]) (= ?cvc_9 bv0[1])))) (and (= (extract[1:0] res) bv2[2]) (= (extract[1:0] c) bv1[2]))))))))))))))
)
