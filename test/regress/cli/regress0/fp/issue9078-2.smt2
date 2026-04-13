; COMMAND-LINE: --fp-exp
; EXPECT: unsat
(set-logic ALL)
(declare-const x (_ BitVec 1))
(assert (fp.isSubnormal ((_ to_fp 5 11) roundNearestTiesToAway ((_ zero_extend 10) x))))
(check-sat)
