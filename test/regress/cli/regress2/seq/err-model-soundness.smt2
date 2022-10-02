; COMMAND-LINE: --strings-exp
(set-logic ALL)
(declare-sort E 0)
(declare-fun x () (Seq E))
(declare-fun y () (Seq E))
(declare-fun z () (Seq E))
(declare-fun e () E)
(declare-fun d () E)

(declare-fun x07 () (Seq E))
(declare-fun x09 () (Seq E))
(declare-fun x10 () (Seq E))
(declare-fun x11 () (Seq E))


(assert (= y (seq.update x09 0 (seq.unit d))))
(assert (= y (seq.update y 0 (seq.unit (seq.nth x 0)))))
(assert (= y (seq.update y 0 (seq.unit (seq.nth y 1)))))
(assert (= z (seq.update z 0 (seq.unit (seq.nth z 1)))))

(assert (= x07 (seq.update z 1 (seq.unit (seq.nth z (- 1))))))
(assert (= x09 (seq.update x 0 (seq.unit e))))
(assert (= x09 (seq.update x09 1 (seq.unit (seq.nth z 0)))))
(assert (= x09 (seq.update x09 1 (seq.unit (seq.nth y (- 1))))))
(assert (= x09 (seq.update z 0 (seq.unit e))))
(assert (= x10 (seq.update z 0 (seq.unit (seq.nth z (- 1))))))
(assert (= x11 (seq.update z 0 (seq.unit (seq.nth x07 (- 1))))))

(assert (distinct x10 x11))
(set-info :status unsat)
(check-sat)
