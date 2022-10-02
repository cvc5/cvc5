; COMMAND-LINE: --decision=justification
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
(set-logic SAT)
(set-option :incremental true)
(declare-fun v1 () Bool)
(declare-fun v2 () Bool)
(declare-fun v3 () Bool)
(declare-fun v4 () Bool)
(declare-fun v5 () Bool)
(declare-fun v6 () Bool)
(declare-fun v7 () Bool)
(declare-fun v8 () Bool)
(check-sat)
(assert (and (and v1 v2) (and (or true (and (or false v1) v1)) (or (and false v1) v3))))
(assert true)
(assert (or (and (or (and (or v4 v4) false) v2) (and true (or (and v5 true) (and v6 v5)))) v2))
(assert v3)
(check-sat)
(assert false)
(assert true)
(assert (and (or (and v7 (and (and v2 v6) (and false v8))) (and (or (and v8 false) true) (and v6 true))) (and true v3)))
(push)
(assert v7)
(check-sat)
(assert true)
(pop)
(push)
(check-sat)
(check-sat)
