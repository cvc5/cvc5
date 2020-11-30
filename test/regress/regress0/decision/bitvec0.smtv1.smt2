; COMMAND-LINE: --decision=justification
; EXPECT: unsat
(set-option :incremental false)
(set-info :source "Hand-crafted bit-vector benchmarks.  Some are from the SVC benchmark suite.
Contributed by Vijay Ganesh (vganesh@stanford.edu).  Translated into SMT-LIB
format by Clark Barrett using CVC3.")
(set-info :status unsat)
(set-info :difficulty "0")
(set-info :category "crafted")
(set-logic QF_BV)
(declare-fun a () (_ BitVec 32))
(declare-fun t () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
(declare-fun aa () (_ BitVec 32))
(declare-fun c () (_ BitVec 32))
(declare-fun d () (_ BitVec 32))
(declare-fun aaaa () (_ BitVec 32))
(declare-fun bbb () (_ BitVec 32))
(declare-fun aaa () (_ BitVec 32))
(declare-fun z () (_ BitVec 32))
(check-sat-assuming ( (let ((_let_0 ((_ extract 6 2) a))) (let ((_let_1 ((_ extract 2 2) t))) (let ((_let_2 ((_ extract 6 6) t))) (let ((_let_3 ((_ extract 2 0) b))) (let ((_let_4 ((_ extract 2 0) c))) (not (and (and (and (ite (= (concat (concat (_ bv0 1) ((_ extract 3 2) a)) ((_ extract 6 5) a)) _let_0) (= _let_0 (_ bv0 5)) (ite (or (or (= (_ bv2 3) (_ bv6 3)) (= (_ bv0 3) (_ bv6 3))) (= (_ bv7 3) (_ bv6 3))) false true)) (and (ite (= (concat ((_ extract 3 2) t) ((_ extract 6 5) t)) ((_ extract 5 2) t)) (= _let_1 _let_2) true) (ite (= ((_ extract 4 0) t) ((_ extract 6 2) t)) (and (and (= _let_1 ((_ extract 4 4) t)) (= ((_ extract 0 0) t) _let_2)) (= ((_ extract 1 1) t) ((_ extract 5 5) t))) true))) (=> (and (and (= _let_3 ((_ extract 2 0) aa)) (= _let_4 _let_3)) (= _let_4 ((_ extract 2 0) d))) (= ((_ extract 1 1) d) ((_ extract 1 1) aa)))) (and (and (and (ite (= (_ bv7 3) ((_ extract 2 0) aaaa)) (= (_ bv1 1) ((_ extract 1 1) aaaa)) true) (ite (= ((_ extract 2 0) bbb) ((_ extract 2 0) aaa)) (= ((_ extract 1 1) bbb) ((_ extract 1 1) aaa)) true)) (= (concat (concat (concat (_ bv4 3) (_ bv1 1)) (_ bv1 1)) (_ bv2 2)) (concat (concat (_ bv1 1) (_ bv7 5)) (_ bv0 1)))) (ite (= (_ bv3 2) ((_ extract 1 0) z)) (= (_ bv1 1) ((_ extract 0 0) z)) true))))))))) ))
