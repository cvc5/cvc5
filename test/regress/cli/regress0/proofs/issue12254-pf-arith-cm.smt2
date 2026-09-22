; COMMAND-LINE: --decision=stoponly --produce-proofs
; EXPECT: sat
(set-logic ALL)
(declare-const u Real)
(declare-const f Int)
(assert (= 0.0 (ite (< 0 (div 0 f)) 0.0 (/ (to_real f) u))))
(check-sat)
