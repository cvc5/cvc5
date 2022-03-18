(set-logic QF_UFC)
(set-info :status unsat)

(declare-sort U 0)

(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(declare-fun d () U)
(declare-fun e () U)

(assert (not (= a b)))
(assert (not (= b c)))
(assert (not (= c d)))
(assert (not (= d e)))
(assert (not (= e a)))

(assert (_ fmf.card U 2))

(check-sat)
