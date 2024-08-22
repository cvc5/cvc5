; COMMAND-LINE: --strings-exp --seq-array=lazy
(set-logic QF_UFSLIA)
(declare-sort E 0)
(declare-fun x () (Seq E))
(declare-fun y () (Seq E))
(assert (= y (seq.update x 0 (seq.unit (seq.nth x 0)))))
(assert (distinct (seq.nth x 1) (seq.nth y 1)))
(set-info :status unsat)
(check-sat)
