(set-option :incremental false)
(set-info :source "CADE ATP System competition. See http://www.cs.miami.edu/~tptp/CASC
 for more information. 

This benchmark was obtained by trying to find a finite model of a first-order 
formula (Albert Oliveras).")
(set-info :status unsat)
(set-info :category "crafted")
(set-info :difficulty "0")
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun c3 () U)
(declare-fun f1 (U U) U)
(declare-fun c2 () U)
(declare-fun f4 (U) U)
(declare-fun c_0 () U)
(declare-fun c_1 () U)
(check-sat-assuming ( (let ((_let_0 (f1 (f1 c3 c_0) c_0))) (let ((_let_1 (f1 c_0 c_0))) (let ((_let_2 (f1 c_0 _let_1))) (let ((_let_3 (f1 c_0 c_1))) (let ((_let_4 (f1 (f1 c3 c_0) c_1))) (let ((_let_5 (f1 c_1 _let_1))) (let ((_let_6 (f1 (f1 c3 c_1) c_0))) (let ((_let_7 (f1 c_1 c_0))) (let ((_let_8 (f1 c_1 c_1))) (let ((_let_9 (f1 c_0 _let_8))) (let ((_let_10 (f1 (f1 c3 c_1) c_1))) (let ((_let_11 (f1 c_1 _let_8))) (let ((_let_12 (f1 c2 c_0))) (let ((_let_13 (f1 c2 c_1))) (let ((_let_14 (f4 c_0))) (let ((_let_15 (f1 c_0 _let_14))) (let ((_let_16 (f4 c_1))) (let ((_let_17 (f1 c_1 _let_16))) (and (distinct c_0 c_1) (= (f1 _let_0 c_0) _let_2) (= (f1 _let_0 c_1) (f1 c_0 _let_3)) (= (f1 _let_4 c_0) _let_5) (= (f1 _let_4 c_1) (f1 c_1 _let_3)) (= (f1 _let_6 c_0) (f1 c_0 _let_7)) (= (f1 _let_6 c_1) _let_9) (= (f1 _let_10 c_0) (f1 c_1 _let_7)) (= (f1 _let_10 c_1) _let_11) (= (f1 _let_12 c_0) _let_2) (= (f1 _let_12 c_1) _let_9) (= (f1 _let_13 c_0) _let_5) (= (f1 _let_13 c_1) _let_11) (not (= _let_15 (f1 _let_14 _let_15))) (not (= _let_17 (f1 _let_16 _let_17))) (or (= _let_1 c_0) (= _let_1 c_1)) (or (= _let_3 c_0) (= _let_3 c_1)) (or (= _let_7 c_0) (= _let_7 c_1)) (or (= _let_8 c_0) (= _let_8 c_1)) (or (= _let_14 c_0) (= _let_14 c_1)) (or (= _let_16 c_0) (= _let_16 c_1)) (or (= c3 c_0) (= c3 c_1)) (or (= c2 c_0) (= c2 c_1))))))))))))))))))))) ))
