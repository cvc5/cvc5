; COMMAND-LINE: -i --sat-solver=cadical
; EXPECT: sat
(set-logic QF_LIA)
(declare-fun v () Int)
(declare-fun v_ () Int)
(assert (distinct v v_))
(assert (> v v_))
(push)
(check-sat)
