; COMMAND-LINE: --ieval=use
; EXPECT: unsat
(set-logic ALL)
(declare-sort s 0)
(declare-datatypes ((ms 0)) (((a))))
(declare-datatypes ((m 0)) (((c (m ms)))))
(declare-fun s () s)
(declare-fun h () (Array s m))
(assert (not (=> (and (forall ((n s)) (not (= a (m (select h n)))))) (= a (m (select h s))) false)))
(check-sat)
