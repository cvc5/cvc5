(set-logic QF_UFC)
(set-info :status unsat)

(declare-sort U 0)

(declare-fun a () U)
(declare-fun c () U)

(assert (_ fmf.card U 2))
(assert (not (_ fmf.card U 4)))

(check-sat)
