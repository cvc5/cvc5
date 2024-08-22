; COMMAND-LINE: --ieval=use
; EXPECT: unsat
(set-logic ALL)
(declare-sort s 0)
(declare-datatypes ((ms 0)) (((a))))
(declare-datatypes ((m 0)) (((c (ml ms)))))
(declare-fun sf () s)
(declare-fun h () (Array s m))
(assert (not (=> (and (forall ((n s)) (not (= a (ml (select h n)))))) (= a (ml (select h sf))) false)))
(check-sat)
