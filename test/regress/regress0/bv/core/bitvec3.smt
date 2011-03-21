(benchmark bitvec3.smt
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
  :extrafuns ((c1 BitVec[32]))
  :extrafuns ((c2 BitVec[32]))
  :extrafuns ((out BitVec[32]))
  :extrafuns ((carry BitVec[32]))
  :formula
(let (?cvc_0 (extract[1:0] b)) (let (?cvc_1 (extract[2:0] c1)) (let (?cvc_3 (concat bv0[1] bv0[2])) (let (?cvc_2 (extract[2:0] c2)) (flet ($cvc_4 (= (extract[0:0] c1) bv1[1])) (flet ($cvc_5 (= (extract[0:0] c2) bv1[1])) (let (?cvc_6 (extract[0:0] carry)) (let (?cvc_7 (extract[1:1] c1)) (flet ($cvc_11 (= ?cvc_7 bv1[1])) (let (?cvc_8 (extract[1:1] c2)) (flet ($cvc_10 (= ?cvc_8 bv0[1])) (flet ($cvc_9 (= ?cvc_7 bv0[1])) (flet ($cvc_12 (= ?cvc_8 bv1[1])) (flet ($cvc_14 (or (and $cvc_11 $cvc_10)  (and $cvc_9 $cvc_12) )) (flet ($cvc_13 (= ?cvc_6 bv1[1])) (let (?cvc_15 (extract[1:1] carry)) (let (?cvc_16 (extract[2:2] c1)) (flet ($cvc_20 (= ?cvc_16 bv1[1])) (let (?cvc_17 (extract[2:2] c2)) (flet ($cvc_19 (= ?cvc_17 bv0[1])) (flet ($cvc_18 (= ?cvc_16 bv0[1])) (flet ($cvc_21 (= ?cvc_17 bv1[1])) (flet ($cvc_22 (= ?cvc_15 bv1[1])) (not (implies (and (= (extract[1:0] a) bv3[2]) (= ?cvc_0 bv3[2])) (implies (and (and (and (and (and (and (and (if_then_else (= (extract[0:0] a) bv1[1]) (= ?cvc_1 (concat bv0[1] ?cvc_0)) (= ?cvc_1 ?cvc_3)) (if_then_else (= (extract[1:1] a) bv1[1]) (= ?cvc_2 (concat ?cvc_0 bv0[1])) (= ?cvc_2 ?cvc_3))) (= (extract[0:0] out) (ite (or $cvc_4  $cvc_5 ) bv1[1] bv0[1]))) (= ?cvc_6 (ite (and $cvc_4 $cvc_5) bv1[1] bv0[1]))) (= (extract[1:1] out) (ite (or (and (= ?cvc_6 bv0[1]) $cvc_14)  (and $cvc_13 (and $cvc_9 $cvc_10)) ) bv1[1] bv0[1]))) (= ?cvc_15 (ite (or (and $cvc_11 $cvc_12)  (and $cvc_13 $cvc_14) ) bv1[1] bv0[1]))) (= (extract[2:2] out) (ite (or (and (= ?cvc_15 bv0[1]) (or (and $cvc_20 $cvc_19)  (and $cvc_18 $cvc_21) ))  (and $cvc_22 (and $cvc_18 $cvc_19)) ) bv1[1] bv0[1]))) (= (extract[2:2] carry) (ite (or (and $cvc_20 $cvc_21)  (and $cvc_22 (or $cvc_20  $cvc_21 )) ) bv1[1] bv0[1]))) (and (= (extract[2:0] out) bv1[3]) (= (extract[2:0] carry) bv6[3]))))))))))))))))))))))))))))
)
