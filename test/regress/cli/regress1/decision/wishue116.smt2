; COMMAND-LINE: --decision=justification
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
(set-logic SAT)
(set-option :incremental true)
(declare-fun v1 () Bool)
(declare-fun v2 () Bool)
(declare-fun v3 () Bool)
(declare-fun v4 () Bool)
(declare-fun v5 () Bool)
(check-sat)
(assert (and (or (or (and (or false v1) v2) (not (not v3))) (forall ((q0_1 Bool) (q0_2 Bool) (q0_3 Bool)) (forall ((q1_1 Bool)) q1_1))) true))
(check-sat)
(assert (or (not v2) (or (and (or (and v4 true) v2) (forall ((q0_1 Bool)) (not true))) (not (forall ((q0_1 Bool) (q0_2 Bool) (q0_3 Bool) (q0_4 Bool)) (forall ((q1_1 Bool) (q1_2 Bool)) v1))))))
(push)
(assert (not v5))
(assert (not true))
(pop)
(push)
(check-sat)
(pop)
(assert true)
