; COMMAND-LINE: --decision=justification
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
(set-logic SAT)
(set-option :incremental true)
(declare-fun v1 () Bool)
(declare-fun v2 () Bool)
(declare-fun v3 () Bool)
(declare-fun v4 () Bool)
(declare-fun v5 () Bool)
(check-sat)
(check-sat)
(assert (or (not (and (or v1 (and v1 true)) (forall ((q0_1 Bool) (q0_2 Bool) (q0_3 Bool)) (and v1 false)))) false))
(assert (or (or (not true) (and (and (not v1) (or v1 v1)) v1)) (or (and (not (not v2)) (forall ((q0_1 Bool) (q0_2 Bool)) (and q0_2 q0_2))) (and (not (and true v3)) (or (not v1) v2)))))
(check-sat)
(check-sat)
(assert (not (forall ((q0_1 Bool) (q0_2 Bool) (q0_3 Bool) (q0_4 Bool)) (and (not (forall ((q1_1 Bool) (q1_2 Bool) (q1_3 Bool) (q1_4 Bool)) false)) (not (forall ((q1_1 Bool)) q0_2))))))
(assert (forall ((q0_1 Bool) (q0_2 Bool) (q0_3 Bool) (q0_4 Bool) (q0_5 Bool)) (not v1)))
(push)
(check-sat)
(assert (and (forall ((q0_1 Bool) (q0_2 Bool) (q0_3 Bool)) (forall ((q1_1 Bool) (q1_2 Bool) (q1_3 Bool) (q1_4 Bool)) (not (forall ((q2_1 Bool)) true)))) (forall ((q0_1 Bool) (q0_2 Bool) (q0_3 Bool)) (not (or q0_3 (forall ((q1_1 Bool)) v4))))))
(assert (or (forall ((q0_1 Bool) (q0_2 Bool) (q0_3 Bool) (q0_4 Bool)) (forall ((q1_1 Bool) (q1_2 Bool) (q1_3 Bool)) (not q1_1))) v1))
(assert v5)
(check-sat)
(assert (not (forall ((q0_1 Bool)) (and (or (or true q0_1) (and false q0_1)) (not true)))))
(pop)
