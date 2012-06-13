(benchmark bitvec0.smt
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
  :extrafuns ((t BitVec[32]))
  :extrafuns ((b BitVec[32]))
  :extrafuns ((aa BitVec[32]))
  :extrafuns ((c BitVec[32]))
  :extrafuns ((d BitVec[32]))
  :extrafuns ((aaaa BitVec[32]))
  :extrafuns ((bbb BitVec[32]))
  :extrafuns ((aaa BitVec[32]))
  :extrafuns ((z BitVec[32]))
  :formula
(let (?cvc_0 (extract[6:2] a)) (let (?cvc_1 (extract[2:2] t)) (let (?cvc_2 (extract[6:6] t)) (let (?cvc_3 (extract[2:0] b)) (let (?cvc_4 (extract[2:0] c)) (not (and (and (and (if_then_else (= (concat (concat bv0[1] (extract[3:2] a)) (extract[6:5] a)) ?cvc_0) (= ?cvc_0 bv0[5]) (if_then_else (or (or (= bv2[3] bv6[3])  (= bv0[3] bv6[3]) )  (= bv7[3] bv6[3]) ) false true)) (and (if_then_else (= (concat (extract[3:2] t) (extract[6:5] t)) (extract[5:2] t)) (= ?cvc_1 ?cvc_2) true) (if_then_else (= (extract[4:0] t) (extract[6:2] t)) (and (and (= ?cvc_1 (extract[4:4] t)) (= (extract[0:0] t) ?cvc_2)) (= (extract[1:1] t) (extract[5:5] t))) true))) (implies (and (and (= ?cvc_3 (extract[2:0] aa)) (= ?cvc_4 ?cvc_3)) (= ?cvc_4 (extract[2:0] d))) (= (extract[1:1] d) (extract[1:1] aa)))) (and (and (and (if_then_else (= bv7[3] (extract[2:0] aaaa)) (= bv1[1] (extract[1:1] aaaa)) true) (if_then_else (= (extract[2:0] bbb) (extract[2:0] aaa)) (= (extract[1:1] bbb) (extract[1:1] aaa)) true)) (= (concat (concat (concat bv4[3] bv1[1]) bv1[1]) bv2[2]) (concat (concat bv1[1] bv7[5]) bv0[1]))) (if_then_else (= bv3[2] (extract[1:0] z)) (= bv1[1] (extract[0:0] z)) true)))))))))
)
