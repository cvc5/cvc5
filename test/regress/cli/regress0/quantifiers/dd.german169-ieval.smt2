; COMMAND-LINE: --ieval=use
; EXPECT: unsat
;; introduces fresh Skolem in a trusted step
; DISABLE-TESTER: alethe
(set-logic ALL)
(declare-sort s 0)
(declare-datatypes ((ms 0)) (((a))))
(declare-datatypes ((m 0)) (((c (ml ms)))))
(declare-fun sf () s)
(declare-fun h () (Array s m))
(assert (not (=> (and (forall ((n s)) (not (= a (ml (select h n)))))) (= a (ml (select h sf))) false)))
(check-sat)
