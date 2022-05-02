(set-option :incremental false)
(set-info :source "CADE ATP System competition. See http://www.cs.miami.edu/~tptp/CASC
 for more information. 

This benchmark was obtained by trying to find a finite model of a first-order 
formula (Albert Oliveras).

Original source is QF_UF/PEQ/PEQ012_size3.smt
Mucked up by Tim")
(set-info :status sat)
(set-info :category "crafted")
(set-info :difficulty "0")
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun f1 (U U) U)
(declare-fun c6 () U)
(declare-fun c3 () U)
(declare-fun c7 () U)
(declare-fun c5 () U)
(declare-fun c2 () U)
(declare-fun c4 () U)
(declare-fun c8 () U)
(declare-fun c9 () U)
(declare-fun c_0 () U)
(declare-fun c_1 () U)
(declare-fun c_2 () U)
(check-sat-assuming ( (let ((_let_0 (= c_0 c_2))) (let ((_let_1 (f1 c_0 c_1))) (let ((_let_2 (f1 c_0 c_2))) (let ((_let_3 (f1 c_0 c_0))) (let ((_let_4 (f1 c_1 c_0))) (let ((_let_5 (f1 c_1 c_2))) (let ((_let_6 (f1 c_1 c_1))) (let ((_let_7 (f1 c_2 c_1))) (let ((_let_8 (f1 c_2 c_2))) (let ((_let_9 (f1 c_2 c_0))) (let ((_let_10 (f1 c_2 _let_9))) (and (not (= c_0 c_1)) (not _let_0) (not (= c_1 c_2)) (or (not (= _let_1 _let_1)) (= c_1 c_1)) (or (not (= _let_2 _let_3)) (= c_2 c_0)) (or (not (= _let_2 _let_2)) (= c_2 c_2)) (or (not (= _let_4 _let_4)) (= c_0 c_0)) (or (not (= _let_4 _let_5)) _let_0) (or (not (= _let_6 _let_4)) (= c_1 c_0)) (= (f1 _let_3 c_0) (f1 c_0 _let_3)) (= (f1 _let_3 c_2) (f1 c_0 _let_2)) (= (f1 _let_1 c_1) (f1 c_0 _let_6)) (= (f1 _let_1 c_2) (f1 c_0 _let_5)) (= (f1 _let_7 c_2) (f1 c_2 _let_5)) (= (f1 _let_8 c_0) _let_10) (= (f1 _let_8 c_1) (f1 c_2 _let_7)) (= (f1 c_0 (f1 c_2 _let_10)) (f1 c_2 (f1 c_0 (f1 c_2 _let_2)))) (= (f1 c2 c8) (f1 c4 c9)) (not (= (f1 c6 c8) (f1 c7 c9))) (or (= _let_3 c_0) (= _let_3 c_1) (= _let_3 c_2)) (or (= _let_1 c_0) (= _let_1 c_1) (= _let_1 c_2)) (or (= _let_4 c_0) (= _let_4 c_1) (= _let_4 c_2)) (or (= _let_6 c_0) (= _let_6 c_1) (= _let_6 c_2)) (or (= _let_5 c_0) (= _let_5 c_1) (= _let_5 c_2)) (or (= _let_9 c_0) (= _let_9 c_1) (= _let_9 c_2)) (or (= _let_7 c_0) (= _let_7 c_1) (= _let_7 c_2)) (or (= _let_8 c_0) (= _let_8 c_1) (= _let_8 c_2)) (or (= c6 c_0) (= c6 c_1) (= c6 c_2)) (or (= c3 c_0) (= c3 c_1) (= c3 c_2)) (or (= c7 c_0) (= c7 c_1) (= c7 c_2)) (or (= c5 c_0) (= c5 c_1) (= c5 c_2)) (or (= c2 c_0) (= c2 c_1) (= c2 c_2)) (or (= c4 c_0) (= c4 c_1) (= c4 c_2)) (or (= c8 c_0) (= c8 c_1) (= c8 c_2)) (or (= c9 c_0) (= c9 c_1) (= c9 c_2)))))))))))))) ))
