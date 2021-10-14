; COMMAND-LINE: --bitblast=eager
(set-logic QF_BV)
(set-info :status unsat)
(declare-const x (_ BitVec 1))
(assert (= (_ bv2 4) ((_ zero_extend 3) x)))
(check-sat)
