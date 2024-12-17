; COMMAND-LINE: --enum-inst
; EXPECT: unsat
(set-logic ALL)
(declare-fun V () Int)
(declare-fun e () Int)
(declare-fun a2 () (Array Int Int))
(declare-fun a () (Array Int Int))
(declare-fun i () Int)
(assert (and (< i V) (<= 0 i) (forall ((? Int)) (= 1 (select a2 i))) (forall ((? Int)) (= (select a ?) (select a2 ?))) (forall ((? Int)) (forall ((? Int)) (= 1 (select a2 ?)))) (forall ((? Int)) (or (distinct e (select a ?)) (> ? (- i 1)))) (or (and (= 1 V) (exists ((? Int)) (> 1 (select a 0)))) (exists ((? Int)) (and (<= ? i) (= e (select a ?)))))))
(check-sat)
