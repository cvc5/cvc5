; COMMAND-LINE:
; EXPECT: sat
(set-logic QF_NIA)
(set-info :status sat)

(declare-fun x () Int)

(assert (= (div 4 2 1) 2))

(assert (= (div x 2 1) 2))

(check-sat)
