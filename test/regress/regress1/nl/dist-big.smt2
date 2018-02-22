; COMMAND-LINE: --nl-ext
; EXPECT: sat
(set-logic QF_NRA)
(set-info :status sat)
(declare-fun v1 () Real)
(declare-fun v2 () Real)
(declare-fun v3 () Real)
(declare-fun v4 () Real)
(declare-fun v5 () Real)
(declare-fun v6 () Real)
(declare-fun v7 () Real)
(declare-fun v8 () Real)

(assert (= (* (+ v1 v2 v3 v4 v5 v6 v7 v8) (+ v1 v2 v3 v4 v5 v6 v7 v8) (+ v1 v2 v3 v4 v5 v6 v7 v8) (+ v1 v2 v3 v4 v5 v6 v7 v8)) 0))

(check-sat)
