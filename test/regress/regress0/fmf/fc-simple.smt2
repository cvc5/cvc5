(set-logic QF_UFC)
(set-info :status unsat)

(declare-sort U 0)

(declare-fun a () U)
(declare-fun c () U)

(assert (fmf.card c 2))
(assert (not (fmf.card a 4)))

(check-sat)
