; COMMAND-LINE: --finite-model-find
; EXPECT: sat
(set-logic ALL)
(declare-datatypes ((B 0)) (((T) (F))))
(declare-sort U 0)
(declare-datatypes ((s 0)) (((i) (t))))
(declare-datatypes ((m 0)) (((d (ms s)))))
(declare-fun c () (Array U m))
(assert (not (= T (ite (or (forall ((n U)) (not (= t (ms (select c n)))))) T F))))
(check-sat)
