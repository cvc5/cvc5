; EXPECT: unsat
; DISABLE-TESTER: unsat-core

; Note we require disabling proofs/unsat cores due to timeouts in nightlies

(set-logic AUFLIRA)
(set-info :source | Example extracted from Peter Baumgartner's talk at CADE-21: Logical Engineering with Instance-Based Methods.

It was translated to SMT-LIB by Leonardo de Moura |)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status unsat)
(declare-fun symmetric ((Array Int (Array Int Real)) Int) Bool)
(declare-fun n () Int)
(declare-fun a0 () (Array Int (Array Int Real)))
(declare-fun e0 () Real)
(declare-fun a1 () (Array Int (Array Int Real)))
(declare-fun e1 () Real)
(declare-fun a2 () (Array Int (Array Int Real)))
(declare-fun e2 () Real)
(declare-fun a3 () (Array Int (Array Int Real)))
(declare-fun e3 () Real)
(declare-fun a4 () (Array Int (Array Int Real)))
(declare-fun e4 () Real)
(declare-fun a5 () (Array Int (Array Int Real)))
(declare-fun e5 () Real)
(declare-fun a6 () (Array Int (Array Int Real)))
(declare-fun e6 () Real)
(assert (forall ((?a (Array Int (Array Int Real))) (?n Int)) (= (symmetric ?a ?n) (forall ((?i Int) (?j Int)) (=> (and (<= 1 ?i) (<= ?i ?n) (<= 1 ?j) (<= ?j ?n)) (= (select (select ?a ?i) ?j) (select (select ?a ?j) ?i)))))))
(assert (symmetric a0 n))
(assert (= a1 (store a0 0 (store (select a0 0) 0 e0))))
(assert (= a2 (store a1 1 (store (select a1 1) 1 e1))))
(assert (= a3 (store a2 2 (store (select a2 2) 2 e2))))
(assert (= a4 (store a3 3 (store (select a3 3) 3 e3))))
(assert (= a5 (store a4 4 (store (select a4 4) 4 e4))))
(assert (= a6 (store a5 5 (store (select a5 5) 5 e5))))
(assert (not (symmetric a6 n)))
(check-sat)
(exit)
